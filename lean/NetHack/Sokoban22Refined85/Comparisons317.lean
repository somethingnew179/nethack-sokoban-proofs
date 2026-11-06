/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons316
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44380 (p : Pattern) (guard : d8086 p = 1) : d3239 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44377 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44381 (p : Pattern) (guard : d5847 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34362 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44382 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44383 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44384 (p : Pattern) (guard : d8091 p = 1) : d3239 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44380 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44385 (p : Pattern) (guard : d8095 p = 1) : d3240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d8095, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44386 (p : Pattern) (guard : d8096 p = 1) : d3241 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44384 p hg
    simpa only [d8096, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44385 p hg
    simpa only [d8096, d3241, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44387 (p : Pattern) (guard : d8097 p = 1) : d3242 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44374 p hg
    simpa only [d8097, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44386 p hg
    simpa only [d8097, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44388 (p : Pattern) (guard : d8098 p = 1) : d3243 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44367 p hg
    simpa only [d8098, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44387 p hg
    simpa only [d8098, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44389 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44390 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44389 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44391 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44390 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44392 (p : Pattern) (guard : d8087 p = 1) : d3226 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44391 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44393 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d8091, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44394 (p : Pattern) (guard : d8092 p = 1) : d3238 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44392 p hg
    simpa only [d8092, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44393 p hg
    simpa only [d8092, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44395 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34379 p hg
    simpa only [d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44396 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44395 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44397 (p : Pattern) (guard : d8086 p = 1) : d3239 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44396 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44398 (p : Pattern) (guard : d8091 p = 1) : d3239 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44397 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44399 (p : Pattern) (guard : d8096 p = 1) : d3241 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44398 p hg
    simpa only [d8096, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44385 p hg
    simpa only [d8096, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44400 (p : Pattern) (guard : d8097 p = 1) : d3242 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44394 p hg
    simpa only [d8097, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44399 p hg
    simpa only [d8097, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44401 (p : Pattern) (guard : d1 p = 1) : d3244 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44402 (p : Pattern) (guard : d1 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44403 (p : Pattern) (guard : d1 p = 1) : d3244 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44401 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44402 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44404 (p : Pattern) (guard : d8084 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d8084, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44405 (p : Pattern) (guard : d8085 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44402 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44404 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44406 (p : Pattern) (guard : d8086 p = 1) : d3244 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44403 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44405 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44407 (p : Pattern) (guard : d5847 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34392 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44408 (p : Pattern) (guard : d8089 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44404 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44409 (p : Pattern) (guard : d8090 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44405 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44410 (p : Pattern) (guard : d8091 p = 1) : d3244 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44406 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44409 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44411 (p : Pattern) (guard : d8095 p = 1) : d3245 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44409 p hg
    simpa only [d8095, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44412 (p : Pattern) (guard : d8096 p = 1) : d3246 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44410 p hg
    simpa only [d8096, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44411 p hg
    simpa only [d8096, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44413 (p : Pattern) (guard : d8102 p = 1) : d3247 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44412 p hg
    simpa only [d8102, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44414 (p : Pattern) (guard : d8103 p = 1) : d3248 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44400 p hg
    simpa only [d8103, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44413 p hg
    simpa only [d8103, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44415 (p : Pattern) (guard : d8104 p = 1) : d3249 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44388 p hg
    simpa only [d8104, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44414 p hg
    simpa only [d8104, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44416 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44417 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44416 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44418 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44417 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44419 (p : Pattern) (guard : d8087 p = 1) : d3226 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44418 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44420 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44421 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d8084, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44422 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44423 (p : Pattern) (guard : d8086 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44424 (p : Pattern) (guard : d8091 p = 1) : d3251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44423 p hg
    simpa only [d8091, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44425 (p : Pattern) (guard : d8092 p = 1) : d3252 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44419 p hg
    simpa only [d8092, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44424 p hg
    simpa only [d8092, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44426 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44427 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44426 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44428 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44427 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44429 (p : Pattern) (guard : d5847 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44430 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44431 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44432 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44428 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44433 (p : Pattern) (guard : d1 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44434 (p : Pattern) (guard : d8084 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d8084, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44435 (p : Pattern) (guard : d8085 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44433 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44434 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44436 (p : Pattern) (guard : d5847 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34423 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44437 (p : Pattern) (guard : d8089 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44434 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44436 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44438 (p : Pattern) (guard : d8090 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44435 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44437 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44439 (p : Pattern) (guard : d8095 p = 1) : d3254 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44438 p hg
    simpa only [d8095, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44440 (p : Pattern) (guard : d8096 p = 1) : d3255 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44432 p hg
    simpa only [d8096, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44439 p hg
    simpa only [d8096, d3255, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44441 (p : Pattern) (guard : d8097 p = 1) : d3256 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44425 p hg
    simpa only [d8097, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44440 p hg
    simpa only [d8097, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44442 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44364 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44443 (p : Pattern) (guard : d1 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44444 (p : Pattern) (guard : d8084 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d8084, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44445 (p : Pattern) (guard : d8085 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44443 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44444 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44446 (p : Pattern) (guard : d5847 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34434 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44447 (p : Pattern) (guard : d8089 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44444 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44446 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44448 (p : Pattern) (guard : d8090 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44445 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44447 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44449 (p : Pattern) (guard : d8095 p = 1) : d3258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44448 p hg
    simpa only [d8095, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44450 (p : Pattern) (guard : d8096 p = 1) : d3259 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44442 p hg
    simpa only [d8096, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44449 p hg
    simpa only [d8096, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44451 (p : Pattern) (guard : d5854 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44452 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44453 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44454 (p : Pattern) (guard : d8101 p = 1) : d3260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44453 p hg
    simpa only [d8101, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44455 (p : Pattern) (guard : d8102 p = 1) : d3261 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44450 p hg
    simpa only [d8102, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44454 p hg
    simpa only [d8102, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44456 (p : Pattern) (guard : d8103 p = 1) : d3262 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44441 p hg
    simpa only [d8103, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44455 p hg
    simpa only [d8103, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44457 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44362 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44458 (p : Pattern) (guard : d8096 p = 1) : d3263 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44457 p hg
    simpa only [d8096, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44459 (p : Pattern) (guard : d8102 p = 1) : d3264 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44458 p hg
    simpa only [d8102, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44454 p hg
    simpa only [d8102, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44460 (p : Pattern) (guard : d5854 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44461 (p : Pattern) (guard : d8094 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44460 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44462 (p : Pattern) (guard : d8095 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44409 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44463 (p : Pattern) (guard : d8101 p = 1) : d3265 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44462 p hg
    simpa only [d8101, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44464 (p : Pattern) (guard : d8107 p = 1) : d3266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44463 p hg
    simpa only [d8107, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44465 (p : Pattern) (guard : d8108 p = 1) : d3267 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44459 p hg
    simpa only [d8108, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44464 p hg
    simpa only [d8108, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44466 (p : Pattern) (guard : d8109 p = 1) : d3268 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44456 p hg
    simpa only [d8109, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44465 p hg
    simpa only [d8109, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44467 (p : Pattern) (guard : d8110 p = 1) : d3269 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44415 p hg
    simpa only [d8110, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44466 p hg
    simpa only [d8110, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44468 (p : Pattern) (guard : d1 p = 1) : d3270 p ≤ (0 : Int) + d379 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3270, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33879 p hg
    simpa only [d3270, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3270, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36088 p hg
    simpa only [d3270, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44469 (p : Pattern) (guard : d1 p = 1) : d3271 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44468 p hg
    simpa only [d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44356 p hg
    simpa only [d3271, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44470 (p : Pattern) (guard : d1 p = 1) : d3272 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44469 p hg
    simpa only [d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44427 p hg
    simpa only [d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44471 (p : Pattern) (guard : d8087 p = 1) : d3273 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44470 p hg
    simpa only [d8087, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44364 p hg
    simpa only [d8087, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44472 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44428 p hg
    simpa only [d8091, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44473 (p : Pattern) (guard : d8092 p = 1) : d3274 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44471 p hg
    simpa only [d8092, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44472 p hg
    simpa only [d8092, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44474 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44475 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44474 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44476 (p : Pattern) (guard : d8086 p = 1) : d3250 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44475 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44477 (p : Pattern) (guard : d5847 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34471 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44478 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44479 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44480 (p : Pattern) (guard : d8091 p = 1) : d3250 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44476 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44481 (p : Pattern) (guard : d8095 p = 1) : d3251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d8095, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44482 (p : Pattern) (guard : d8096 p = 1) : d3275 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44480 p hg
    simpa only [d8096, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44483 (p : Pattern) (guard : d8097 p = 1) : d3276 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44473 p hg
    simpa only [d8097, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44482 p hg
    simpa only [d8097, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44484 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34479 p hg
    simpa only [d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44485 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44484 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44486 (p : Pattern) (guard : d8086 p = 1) : d3239 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44485 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44487 (p : Pattern) (guard : d8091 p = 1) : d3239 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44486 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44488 (p : Pattern) (guard : d8096 p = 1) : d3241 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44487 p hg
    simpa only [d8096, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44385 p hg
    simpa only [d8096, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44489 (p : Pattern) (guard : d8085 p = 1) : d3244 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44401 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44404 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44490 (p : Pattern) (guard : d8090 p = 1) : d3244 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44489 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44491 (p : Pattern) (guard : d8095 p = 1) : d3244 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44490 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44492 (p : Pattern) (guard : d8100 p = 1) : d3245 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d8100, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44493 (p : Pattern) (guard : d8101 p = 1) : d3246 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44491 p hg
    simpa only [d8101, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44492 p hg
    simpa only [d8101, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44494 (p : Pattern) (guard : d8102 p = 1) : d3277 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44488 p hg
    simpa only [d8102, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44493 p hg
    simpa only [d8102, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44495 (p : Pattern) (guard : d8103 p = 1) : d3278 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44483 p hg
    simpa only [d8103, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44494 p hg
    simpa only [d8103, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44496 (p : Pattern) (guard : d1 p = 1) : d3279 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44497 (p : Pattern) (guard : d8084 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d8084, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44498 (p : Pattern) (guard : d8085 p = 1) : d3279 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44496 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44497 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44499 (p : Pattern) (guard : d5847 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34497 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44500 (p : Pattern) (guard : d8089 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44497 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44499 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44501 (p : Pattern) (guard : d8090 p = 1) : d3279 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44498 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44500 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44502 (p : Pattern) (guard : d5854 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44499 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44503 (p : Pattern) (guard : d8094 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44500 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44502 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44504 (p : Pattern) (guard : d8095 p = 1) : d3279 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44501 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44503 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44505 (p : Pattern) (guard : d8100 p = 1) : d3280 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44503 p hg
    simpa only [d8100, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44506 (p : Pattern) (guard : d8101 p = 1) : d3281 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44504 p hg
    simpa only [d8101, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44505 p hg
    simpa only [d8101, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44507 (p : Pattern) (guard : d8102 p = 1) : d3282 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44386 p hg
    simpa only [d8102, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44506 p hg
    simpa only [d8102, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44508 (p : Pattern) (guard : d1 p = 1) : d3257 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44509 (p : Pattern) (guard : d8085 p = 1) : d3257 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44508 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44444 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44510 (p : Pattern) (guard : d8090 p = 1) : d3257 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44509 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44447 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44511 (p : Pattern) (guard : d5854 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44446 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44512 (p : Pattern) (guard : d8094 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44447 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44511 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44513 (p : Pattern) (guard : d8095 p = 1) : d3257 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44510 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44512 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44514 (p : Pattern) (guard : d8100 p = 1) : d3258 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44512 p hg
    simpa only [d8100, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44515 (p : Pattern) (guard : d8101 p = 1) : d3283 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44513 p hg
    simpa only [d8101, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d8101, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44516 (p : Pattern) (guard : d8107 p = 1) : d3284 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44515 p hg
    simpa only [d8107, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44517 (p : Pattern) (guard : d8108 p = 1) : d3285 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44507 p hg
    simpa only [d8108, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44516 p hg
    simpa only [d8108, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44518 (p : Pattern) (guard : d8109 p = 1) : d3286 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44495 p hg
    simpa only [d8109, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44517 p hg
    simpa only [d8109, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44519 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44347 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
