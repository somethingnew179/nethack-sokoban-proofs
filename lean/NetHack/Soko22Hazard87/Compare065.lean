import NetHack.Soko22Hazard87.Compare064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16250 (p : Pattern) (guard : d5251 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16249 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16251 (p : Pattern) (guard : d15555 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16252 (p : Pattern) (guard : d15556 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16251 p hg
    simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d15556, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16253 (p : Pattern) (guard : d15557 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16252 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16254 (p : Pattern) (guard : d15558 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16250 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16253 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16255 (p : Pattern) (guard : d17165 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16244 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16254 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16256 (p : Pattern) (guard : d17166 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16255 p hg
    simpa only [d17166, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16257 (p : Pattern) (guard : d17167 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16256 p hg
    simpa only [d17167, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16258 (p : Pattern) (guard : d17168 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16247 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16257 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16259 (p : Pattern) (guard : d17238 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16238 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16258 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16260 (p : Pattern) (guard : d17239 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16259 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16261 (p : Pattern) (guard : d17240 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d17240, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d17240, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16262 (p : Pattern) (guard : d17241 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16261 p hg
    simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16263 (p : Pattern) (guard : d17242 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16257 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16264 (p : Pattern) (guard : d17243 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16258 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16263 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16265 (p : Pattern) (guard : d17244 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16264 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16266 (p : Pattern) (guard : d17245 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16265 p hg
    simpa only [d17245, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d17245, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16267 (p : Pattern) (guard : d17246 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16266 p hg
    simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16268 (p : Pattern) (guard : d17247 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16262 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16267 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16269 (p : Pattern) (guard : d17248 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16268 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16270 (p : Pattern) (guard : d17249 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16269 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16271 (p : Pattern) (guard : d17323 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17249 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16270 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16272 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare16273 (p : Pattern) (guard : d2068 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16272 p hg
    simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d2068, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16274 (p : Pattern) (guard : d2071 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16273 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16275 (p : Pattern) (guard : d15563 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16274 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16253 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16276 (p : Pattern) (guard : d17169 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16244 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16275 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16277 (p : Pattern) (guard : d17170 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16276 p hg
    simpa only [d17170, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16278 (p : Pattern) (guard : d17171 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16277 p hg
    simpa only [d17171, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16279 (p : Pattern) (guard : d17172 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16278 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16280 (p : Pattern) (guard : d17177 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16279 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16281 (p : Pattern) (guard : d17178 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16280 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16282 (p : Pattern) (guard : d17179 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16281 p hg
    simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d17179, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16283 (p : Pattern) (guard : d17180 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16282 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16284 (p : Pattern) (guard : d17251 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16267 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16283 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16285 (p : Pattern) (guard : d17252 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16284 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16286 (p : Pattern) (guard : d17253 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16287 (p : Pattern) (guard : d17324 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17253 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16286 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16288 (p : Pattern) (guard : d17325 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17323 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16271 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17324 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16287 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16289 (p : Pattern) (guard : d128401 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17325 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16288 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16290 (p : Pattern) (guard : d13614 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16274 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16291 (p : Pattern) (guard : d17294 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16244 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16290 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16292 (p : Pattern) (guard : d17295 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17295, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d17295, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17294 p = 1 := by simpa only [d17295, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16291 p hg
    simpa only [d17295, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16293 (p : Pattern) (guard : d17296 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d17296, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16292 p hg
    simpa only [d17296, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16294 (p : Pattern) (guard : d17297 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16293 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16295 (p : Pattern) (guard : d17298 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16258 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16294 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16296 (p : Pattern) (guard : d17299 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16297 (p : Pattern) (guard : d17300 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16296 p hg
    simpa only [d17300, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d17300, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16298 (p : Pattern) (guard : d17301 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16297 p hg
    simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16299 (p : Pattern) (guard : d17302 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16300 (p : Pattern) (guard : d17303 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16299 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16301 (p : Pattern) (guard : d17304 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16300 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16302 (p : Pattern) (guard : d17330 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17304 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16301 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16303 (p : Pattern) (guard : d17331 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17330 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16302 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16304 (p : Pattern) (guard : d17332 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17331 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16305 (p : Pattern) (guard : d128402 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128401 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16289 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17332 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16304 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16306 (p : Pattern) (guard : d128410 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128402 p = 1 := by simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16305 p hg
    simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16307 (p : Pattern) (guard : d128411 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128410 p = 1 := by simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16306 p hg
    simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16308 (p : Pattern) (guard : d128412 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128412, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128412, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128411 p = 1 := by simpa only [d128412, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16307 p hg
    simpa only [d128412, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16309 (p : Pattern) (guard : d128413 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128412 p = 1 := by simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16308 p hg
    simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16310 (p : Pattern) (guard : d17185 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16283 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16311 (p : Pattern) (guard : d17186 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16310 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16312 (p : Pattern) (guard : d17187 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16311 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16313 (p : Pattern) (guard : d17198 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16312 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16314 (p : Pattern) (guard : d17349 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17198 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16313 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16315 (p : Pattern) (guard : d17350 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17349 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16314 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16316 (p : Pattern) (guard : d17351 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17350 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16315 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16317 (p : Pattern) (guard : d17352 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17351 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16316 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16318 (p : Pattern) (guard : d17353 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17352 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16317 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16319 (p : Pattern) (guard : d17363 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17363, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17363, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17353 p = 1 := by simpa only [d17363, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16318 p hg
    simpa only [d17363, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16320 (p : Pattern) (guard : d17364 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17363 p = 1 := by simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16319 p hg
    simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16321 (p : Pattern) (guard : d128414 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128413 p = 1 := by simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16309 p hg
    simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17364 p = 1 := by simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16320 p hg
    simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16322 (p : Pattern) (guard : d128415 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128414 p = 1 := by simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16321 p hg
    simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16323 (p : Pattern) (guard : d128416 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128415 p = 1 := by simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16322 p hg
    simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16324 (p : Pattern) (guard : d128417 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128409 p = 1 := by simpa only [d128417, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16211 p hg
    simpa only [d128417, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128416 p = 1 := by simpa only [d128417, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16323 p hg
    simpa only [d128417, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16325 (p : Pattern) (guard : d2333 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16326 (p : Pattern) (guard : d2334 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2333 p = 1 := by simpa only [d2334, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16325 p hg
    simpa only [d2334, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2334, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d2334, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16327 (p : Pattern) (guard : d17371 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16328 (p : Pattern) (guard : d17372 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17371 p = 1 := by simpa only [d17372, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16327 p hg
    simpa only [d17372, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17372, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17372, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16329 (p : Pattern) (guard : d17373 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2334 p = 1 := by simpa only [d17373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16326 p hg
    simpa only [d17373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17372 p = 1 := by simpa only [d17373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16328 p hg
    simpa only [d17373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16330 (p : Pattern) (guard : d13815 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16331 (p : Pattern) (guard : d13816 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13815 p = 1 := by simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d13816, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16332 (p : Pattern) (guard : d17374 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d17374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13816 p = 1 := by simpa only [d17374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16331 p hg
    simpa only [d17374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16333 (p : Pattern) (guard : d17375 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17373 p = 1 := by simpa only [d17375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16329 p hg
    simpa only [d17375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17374 p = 1 := by simpa only [d17375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16332 p hg
    simpa only [d17375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16334 (p : Pattern) (guard : d2337 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16335 (p : Pattern) (guard : d2338 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2337 p = 1 := by simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16334 p hg
    simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d2338, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16336 (p : Pattern) (guard : d17378 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16337 (p : Pattern) (guard : d17379 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17378 p = 1 := by simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16336 p hg
    simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17379, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16338 (p : Pattern) (guard : d17380 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2338 p = 1 := by simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16335 p hg
    simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17379 p = 1 := by simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d17380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16339 (p : Pattern) (guard : d15777 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16340 (p : Pattern) (guard : d15778 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15777 p = 1 := by simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16339 p hg
    simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15778, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16341 (p : Pattern) (guard : d17381 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13816 p = 1 := by simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16331 p hg
    simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15778 p = 1 := by simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16340 p hg
    simpa only [d17381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16342 (p : Pattern) (guard : d17382 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17380 p = 1 := by simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16338 p hg
    simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17381 p = 1 := by simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d17382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16343 (p : Pattern) (guard : d17383 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17375 p = 1 := by simpa only [d17383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16333 p hg
    simpa only [d17383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17382 p = 1 := by simpa only [d17383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16342 p hg
    simpa only [d17383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16344 (p : Pattern) (guard : d17384 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17384, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17384, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17383 p = 1 := by simpa only [d17384, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16343 p hg
    simpa only [d17384, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16345 (p : Pattern) (guard : d17385 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17385, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17385, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17384 p = 1 := by simpa only [d17385, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16344 p hg
    simpa only [d17385, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16346 (p : Pattern) (guard : d15779 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15778 p = 1 := by simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16340 p hg
    simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16347 (p : Pattern) (guard : d17386 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17381 p = 1 := by simpa only [d17386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d17386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15779 p = 1 := by simpa only [d17386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d17386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16348 (p : Pattern) (guard : d17387 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17382 p = 1 := by simpa only [d17387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16342 p hg
    simpa only [d17387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17386 p = 1 := by simpa only [d17387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16347 p hg
    simpa only [d17387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16349 (p : Pattern) (guard : d17388 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17388, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17388, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17387 p = 1 := by simpa only [d17388, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16348 p hg
    simpa only [d17388, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16350 (p : Pattern) (guard : d17389 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17389, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17389, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17388 p = 1 := by simpa only [d17389, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16349 p hg
    simpa only [d17389, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16351 (p : Pattern) (guard : d17390 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17385 p = 1 := by simpa only [d17390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16345 p hg
    simpa only [d17390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17389 p = 1 := by simpa only [d17390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d17390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16352 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16353 (p : Pattern) (guard : d2343 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16352 p hg
    simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16354 (p : Pattern) (guard : d17393 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16355 (p : Pattern) (guard : d17394 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17393 p = 1 := by simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16354 p hg
    simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16356 (p : Pattern) (guard : d17395 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2343 p = 1 := by simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17394 p = 1 := by simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16355 p hg
    simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16357 (p : Pattern) (guard : d17396 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17395 p = 1 := by simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15779 p = 1 := by simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16358 (p : Pattern) (guard : d17397 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17382 p = 1 := by simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16342 p hg
    simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17396 p = 1 := by simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16357 p hg
    simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16359 (p : Pattern) (guard : d17398 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17397 p = 1 := by simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16358 p hg
    simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16360 (p : Pattern) (guard : d17399 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17398 p = 1 := by simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16361 (p : Pattern) (guard : d6645 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16362 (p : Pattern) (guard : d6646 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6645 p = 1 := by simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16361 p hg
    simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16363 (p : Pattern) (guard : d6647 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6646 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16362 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16364 (p : Pattern) (guard : d15792 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16365 (p : Pattern) (guard : d15793 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15792 p = 1 := by simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16364 p hg
    simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16366 (p : Pattern) (guard : d15794 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15793 p = 1 := by simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16365 p hg
    simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16367 (p : Pattern) (guard : d15795 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6647 p = 1 := by simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16363 p hg
    simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15794 p = 1 := by simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16366 p hg
    simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16368 (p : Pattern) (guard : d17400 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17396 p = 1 := by simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16357 p hg
    simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15795 p = 1 := by simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16367 p hg
    simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16369 (p : Pattern) (guard : d17401 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17400 p = 1 := by simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16368 p hg
    simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16370 (p : Pattern) (guard : d17402 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17401 p = 1 := by simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16369 p hg
    simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16371 (p : Pattern) (guard : d17403 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17399 p = 1 := by simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16360 p hg
    simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17402 p = 1 := by simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16370 p hg
    simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16372 (p : Pattern) (guard : d17404 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17390 p = 1 := by simpa only [d17404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16351 p hg
    simpa only [d17404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17403 p = 1 := by simpa only [d17404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16371 p hg
    simpa only [d17404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16373 (p : Pattern) (guard : d17405 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17404 p = 1 := by simpa only [d17405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16372 p hg
    simpa only [d17405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16374 (p : Pattern) (guard : d17406 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17405 p = 1 := by simpa only [d17406, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16373 p hg
    simpa only [d17406, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17406, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17406, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16375 (p : Pattern) (guard : d17407 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17407, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17407, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17406 p = 1 := by simpa only [d17407, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16374 p hg
    simpa only [d17407, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16376 (p : Pattern) (guard : d17408 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17402 p = 1 := by simpa only [d17408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16370 p hg
    simpa only [d17408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16377 (p : Pattern) (guard : d17409 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17403 p = 1 := by simpa only [d17409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16371 p hg
    simpa only [d17409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17408 p = 1 := by simpa only [d17409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16376 p hg
    simpa only [d17409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16378 (p : Pattern) (guard : d17410 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17409 p = 1 := by simpa only [d17410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16377 p hg
    simpa only [d17410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16379 (p : Pattern) (guard : d17411 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17410 p = 1 := by simpa only [d17411, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16378 p hg
    simpa only [d17411, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17411, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17411, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16380 (p : Pattern) (guard : d17412 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17412, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17412, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17411 p = 1 := by simpa only [d17412, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16379 p hg
    simpa only [d17412, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16381 (p : Pattern) (guard : d17413 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17407 p = 1 := by simpa only [d17413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16375 p hg
    simpa only [d17413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17412 p = 1 := by simpa only [d17413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d17413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16382 (p : Pattern) (guard : d17414 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17413 p = 1 := by simpa only [d17414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16381 p hg
    simpa only [d17414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16383 (p : Pattern) (guard : d17415 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17414 p = 1 := by simpa only [d17415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16382 p hg
    simpa only [d17415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16384 (p : Pattern) (guard : d17416 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17415 p = 1 := by simpa only [d17416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d17416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16385 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare16386 (p : Pattern) (guard : d2349 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16385 p hg
    simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16387 (p : Pattern) (guard : d2355 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2349 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16386 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16388 (p : Pattern) (guard : d15813 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2355 p = 1 := by simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15794 p = 1 := by simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16366 p hg
    simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16389 (p : Pattern) (guard : d17417 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17396 p = 1 := by simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16357 p hg
    simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15813 p = 1 := by simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16388 p hg
    simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16390 (p : Pattern) (guard : d17418 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17417 p = 1 := by simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16389 p hg
    simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16391 (p : Pattern) (guard : d17419 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17418 p = 1 := by simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16390 p hg
    simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16392 (p : Pattern) (guard : d17420 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17419 p = 1 := by simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16391 p hg
    simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16393 (p : Pattern) (guard : d17421 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17420 p = 1 := by simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16392 p hg
    simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16394 (p : Pattern) (guard : d17422 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17421 p = 1 := by simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16393 p hg
    simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16395 (p : Pattern) (guard : d17423 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17422 p = 1 := by simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16394 p hg
    simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16396 (p : Pattern) (guard : d17424 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17423 p = 1 := by simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16395 p hg
    simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16397 (p : Pattern) (guard : d17425 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17412 p = 1 := by simpa only [d17425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16380 p hg
    simpa only [d17425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17424 p = 1 := by simpa only [d17425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16396 p hg
    simpa only [d17425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16398 (p : Pattern) (guard : d17426 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17425 p = 1 := by simpa only [d17426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16397 p hg
    simpa only [d17426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16399 (p : Pattern) (guard : d17427 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17426 p = 1 := by simpa only [d17427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16398 p hg
    simpa only [d17427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16400 (p : Pattern) (guard : d17428 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17427 p = 1 := by simpa only [d17428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16399 p hg
    simpa only [d17428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16401 (p : Pattern) (guard : d17429 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17416 p = 1 := by simpa only [d17429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16384 p hg
    simpa only [d17429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17428 p = 1 := by simpa only [d17429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16400 p hg
    simpa only [d17429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16402 (p : Pattern) (guard : d128418 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17429 p = 1 := by simpa only [d128418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16401 p hg
    simpa only [d128418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16403 (p : Pattern) (guard : d13843 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2355 p = 1 := by simpa only [d13843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16387 p hg
    simpa only [d13843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d13843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16404 (p : Pattern) (guard : d17472 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17396 p = 1 := by simpa only [d17472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16357 p hg
    simpa only [d17472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13843 p = 1 := by simpa only [d17472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16403 p hg
    simpa only [d17472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16405 (p : Pattern) (guard : d17473 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17473, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d17473, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17472 p = 1 := by simpa only [d17473, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16404 p hg
    simpa only [d17473, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16406 (p : Pattern) (guard : d17474 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17474, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d17474, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17473 p = 1 := by simpa only [d17474, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16405 p hg
    simpa only [d17474, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16407 (p : Pattern) (guard : d17475 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17474 p = 1 := by simpa only [d17475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16406 p hg
    simpa only [d17475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16408 (p : Pattern) (guard : d17476 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17403 p = 1 := by simpa only [d17476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16371 p hg
    simpa only [d17476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17475 p = 1 := by simpa only [d17476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16407 p hg
    simpa only [d17476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16409 (p : Pattern) (guard : d17477 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17476 p = 1 := by simpa only [d17477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16408 p hg
    simpa only [d17477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d17477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16410 (p : Pattern) (guard : d17478 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17477 p = 1 := by simpa only [d17478, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16409 p hg
    simpa only [d17478, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17478, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d17478, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16411 (p : Pattern) (guard : d17479 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17479, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d17479, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17478 p = 1 := by simpa only [d17479, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16410 p hg
    simpa only [d17479, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16412 (p : Pattern) (guard : d17480 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17479 p = 1 := by simpa only [d17480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16411 p hg
    simpa only [d17480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16413 (p : Pattern) (guard : d17481 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17480 p = 1 := by simpa only [d17481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16412 p hg
    simpa only [d17481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16414 (p : Pattern) (guard : d17482 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17481 p = 1 := by simpa only [d17482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16413 p hg
    simpa only [d17482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16415 (p : Pattern) (guard : d17483 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17482 p = 1 := by simpa only [d17483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d17483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16416 (p : Pattern) (guard : d17484 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17483 p = 1 := by simpa only [d17484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16415 p hg
    simpa only [d17484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16417 (p : Pattern) (guard : d17485 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17484 p = 1 := by simpa only [d17485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16416 p hg
    simpa only [d17485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16418 (p : Pattern) (guard : d128419 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128418 p = 1 := by simpa only [d128419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16402 p hg
    simpa only [d128419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17485 p = 1 := by simpa only [d128419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16417 p hg
    simpa only [d128419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16419 (p : Pattern) (guard : d128420 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128419 p = 1 := by simpa only [d128420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16418 p hg
    simpa only [d128420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16420 (p : Pattern) (guard : d128421 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128420 p = 1 := by simpa only [d128421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16419 p hg
    simpa only [d128421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16421 (p : Pattern) (guard : d128422 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128422, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128422, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128421 p = 1 := by simpa only [d128422, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16420 p hg
    simpa only [d128422, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16422 (p : Pattern) (guard : d128423 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128422 p = 1 := by simpa only [d128423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16421 p hg
    simpa only [d128423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16423 (p : Pattern) (guard : d17491 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17424 p = 1 := by simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16396 p hg
    simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16424 (p : Pattern) (guard : d17492 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17491 p = 1 := by simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16423 p hg
    simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16425 (p : Pattern) (guard : d17493 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17492 p = 1 := by simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16424 p hg
    simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16426 (p : Pattern) (guard : d17494 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17493 p = 1 := by simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16425 p hg
    simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16427 (p : Pattern) (guard : d17495 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17494 p = 1 := by simpa only [d17495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16426 p hg
    simpa only [d17495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16428 (p : Pattern) (guard : d17496 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17495 p = 1 := by simpa only [d17496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16427 p hg
    simpa only [d17496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16429 (p : Pattern) (guard : d17497 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17496 p = 1 := by simpa only [d17497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16428 p hg
    simpa only [d17497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16430 (p : Pattern) (guard : d17498 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17497 p = 1 := by simpa only [d17498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16429 p hg
    simpa only [d17498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16431 (p : Pattern) (guard : d17499 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d17499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17498 p = 1 := by simpa only [d17499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16430 p hg
    simpa only [d17499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16432 (p : Pattern) (guard : d17500 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17500, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d17500, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17499 p = 1 := by simpa only [d17500, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16431 p hg
    simpa only [d17500, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16433 (p : Pattern) (guard : d17501 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d17501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17500 p = 1 := by simpa only [d17501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16432 p hg
    simpa only [d17501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16434 (p : Pattern) (guard : d128424 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128423 p = 1 := by simpa only [d128424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16422 p hg
    simpa only [d128424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17501 p = 1 := by simpa only [d128424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16433 p hg
    simpa only [d128424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16435 (p : Pattern) (guard : d128425 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128424 p = 1 := by simpa only [d128425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16434 p hg
    simpa only [d128425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16436 (p : Pattern) (guard : d128426 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128425 p = 1 := by simpa only [d128426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16435 p hg
    simpa only [d128426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16437 (p : Pattern) (guard : d128427 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128426 p = 1 := by simpa only [d128427, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16436 p hg
    simpa only [d128427, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128427, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128427, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16438 (p : Pattern) (guard : d128428 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128417 p = 1 := by simpa only [d128428, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16324 p hg
    simpa only [d128428, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128427 p = 1 := by simpa only [d128428, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16437 p hg
    simpa only [d128428, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16439 (p : Pattern) (guard : d128429 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128428 p = 1 := by simpa only [d128429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16438 p hg
    simpa only [d128429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16440 (p : Pattern) (guard : d128430 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128429 p = 1 := by simpa only [d128430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16439 p hg
    simpa only [d128430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16441 (p : Pattern) (guard : d128431 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128430 p = 1 := by simpa only [d128431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16440 p hg
    simpa only [d128431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16442 (p : Pattern) (guard : d128432 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128431 p = 1 := by simpa only [d128432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16441 p hg
    simpa only [d128432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16443 (p : Pattern) (guard : d128433 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128432 p = 1 := by simpa only [d128433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16442 p hg
    simpa only [d128433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16444 (p : Pattern) (guard : d128434 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128433 p = 1 := by simpa only [d128434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16443 p hg
    simpa only [d128434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16445 (p : Pattern) (guard : d128435 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128434 p = 1 := by simpa only [d128435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16444 p hg
    simpa only [d128435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16446 (p : Pattern) (guard : d128436 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128435 p = 1 := by simpa only [d128436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16445 p hg
    simpa only [d128436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16447 (p : Pattern) (guard : d128437 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128436 p = 1 := by simpa only [d128437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16446 p hg
    simpa only [d128437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16448 (p : Pattern) (guard : d128438 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128437 p = 1 := by simpa only [d128438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16447 p hg
    simpa only [d128438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16449 (p : Pattern) (guard : d128439 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d128395 p = 1 := by simpa only [d128439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15937 p hg
    simpa only [d128439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128438 p = 1 := by simpa only [d128439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16448 p hg
    simpa only [d128439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16450 (p : Pattern) (guard : d128440 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 260 with
  | false =>
    have hg : d128439 p = 1 := by simpa only [d128440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16449 p hg
    simpa only [d128440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16451 (p : Pattern) (guard : d128441 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 259 with
  | false =>
    have hg : d128440 p = 1 := by simpa only [d128441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16450 p hg
    simpa only [d128441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16452 (p : Pattern) (guard : d128442 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 258 with
  | false =>
    have hg : d128441 p = 1 := by simpa only [d128442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16451 p hg
    simpa only [d128442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16453 (p : Pattern) (guard : d128443 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 257 with
  | false =>
    have hg : d128442 p = 1 := by simpa only [d128443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16452 p hg
    simpa only [d128443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16454 (p : Pattern) (guard : d128444 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 256 with
  | false =>
    have hg : d128443 p = 1 := by simpa only [d128444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16453 p hg
    simpa only [d128444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16455 (p : Pattern) (guard : d128445 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 255 with
  | false =>
    have hg : d128444 p = 1 := by simpa only [d128445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16454 p hg
    simpa only [d128445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16456 (p : Pattern) (guard : d128446 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 254 with
  | false =>
    have hg : d128445 p = 1 := by simpa only [d128446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16455 p hg
    simpa only [d128446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16457 (p : Pattern) (guard : d128447 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 253 with
  | false =>
    have hg : d128446 p = 1 := by simpa only [d128447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16456 p hg
    simpa only [d128447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16458 (p : Pattern) (guard : d128448 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 252 with
  | false =>
    have hg : d128447 p = 1 := by simpa only [d128448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16457 p hg
    simpa only [d128448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16459 (p : Pattern) (guard : d128449 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 251 with
  | false =>
    have hg : d128448 p = 1 := by simpa only [d128449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16458 p hg
    simpa only [d128449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16460 (p : Pattern) (guard : d128450 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 250 with
  | false =>
    have hg : d128449 p = 1 := by simpa only [d128450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16459 p hg
    simpa only [d128450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16461 (p : Pattern) (guard : d128451 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 249 with
  | false =>
    have hg : d128450 p = 1 := by simpa only [d128451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16460 p hg
    simpa only [d128451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16462 (p : Pattern) (guard : d128452 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 245 with
  | false =>
    have hg : d128451 p = 1 := by simpa only [d128452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16461 p hg
    simpa only [d128452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16463 (p : Pattern) (guard : d128453 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 200 with
  | false =>
    have hg : d128452 p = 1 := by simpa only [d128453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16462 p hg
    simpa only [d128453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16464 (p : Pattern) (guard : d128454 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 199 with
  | false =>
    have hg : d128453 p = 1 := by simpa only [d128454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16463 p hg
    simpa only [d128454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16465 (p : Pattern) (guard : d128455 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 186 with
  | false =>
    have hg : d128454 p = 1 := by simpa only [d128455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16464 p hg
    simpa only [d128455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16466 (p : Pattern) (guard : d128456 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 185 with
  | false =>
    have hg : d128455 p = 1 := by simpa only [d128456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16465 p hg
    simpa only [d128456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16467 (p : Pattern) (guard : d128457 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 184 with
  | false =>
    have hg : d128456 p = 1 := by simpa only [d128457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16466 p hg
    simpa only [d128457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16468 (p : Pattern) (guard : d128458 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 181 with
  | false =>
    have hg : d128457 p = 1 := by simpa only [d128458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16467 p hg
    simpa only [d128458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16469 (p : Pattern) (guard : d128459 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 177 with
  | false =>
    have hg : d128458 p = 1 := by simpa only [d128459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16468 p hg
    simpa only [d128459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16470 (p : Pattern) (guard : d128460 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 164 with
  | false =>
    have hg : d128459 p = 1 := by simpa only [d128460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16469 p hg
    simpa only [d128460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16471 (p : Pattern) (guard : d128461 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 156 with
  | false =>
    have hg : d128460 p = 1 := by simpa only [d128461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16470 p hg
    simpa only [d128461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16472 (p : Pattern) (guard : d128462 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 155 with
  | false =>
    have hg : d128461 p = 1 := by simpa only [d128462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16471 p hg
    simpa only [d128462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16473 (p : Pattern) (guard : d128463 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 134 with
  | false =>
    have hg : d128462 p = 1 := by simpa only [d128463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16472 p hg
    simpa only [d128463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16474 (p : Pattern) (guard : d128464 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d128463 p = 1 := by simpa only [d128464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16473 p hg
    simpa only [d128464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16475 (p : Pattern) (guard : d128465 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 120 with
  | false =>
    have hg : d128464 p = 1 := by simpa only [d128465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16474 p hg
    simpa only [d128465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16476 (p : Pattern) (guard : d128466 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 118 with
  | false =>
    have hg : d128465 p = 1 := by simpa only [d128466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16475 p hg
    simpa only [d128466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16477 (p : Pattern) (guard : d128467 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 114 with
  | false =>
    have hg : d128466 p = 1 := by simpa only [d128467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16476 p hg
    simpa only [d128467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16478 (p : Pattern) (guard : d128468 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 111 with
  | false =>
    have hg : d128467 p = 1 := by simpa only [d128468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16477 p hg
    simpa only [d128468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16479 (p : Pattern) (guard : d128469 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 98 with
  | false =>
    have hg : d128468 p = 1 := by simpa only [d128469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16478 p hg
    simpa only [d128469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16480 (p : Pattern) (guard : d128470 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 97 with
  | false =>
    have hg : d128469 p = 1 := by simpa only [d128470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16479 p hg
    simpa only [d128470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16481 (p : Pattern) (guard : d128471 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 94 with
  | false =>
    have hg : d128470 p = 1 := by simpa only [d128471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16480 p hg
    simpa only [d128471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16482 (p : Pattern) (guard : d128472 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 76 with
  | false =>
    have hg : d128471 p = 1 := by simpa only [d128472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16481 p hg
    simpa only [d128472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16483 (p : Pattern) (guard : d128473 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 67 with
  | false =>
    have hg : d128472 p = 1 := by simpa only [d128473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16482 p hg
    simpa only [d128473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16484 (p : Pattern) (guard : d128474 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 52 with
  | false =>
    have hg : d128473 p = 1 := by simpa only [d128474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16483 p hg
    simpa only [d128474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16485 (p : Pattern) (guard : d128475 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 47 with
  | false =>
    have hg : d128474 p = 1 := by simpa only [d128475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16484 p hg
    simpa only [d128475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16486 (p : Pattern) (guard : d128476 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 46 with
  | false =>
    have hg : d128475 p = 1 := by simpa only [d128476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16485 p hg
    simpa only [d128476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16487 (p : Pattern) (guard : d128477 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 45 with
  | false =>
    have hg : d128476 p = 1 := by simpa only [d128477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16486 p hg
    simpa only [d128477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16488 (p : Pattern) (guard : d128478 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 30 with
  | false =>
    have hg : d128477 p = 1 := by simpa only [d128478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16487 p hg
    simpa only [d128478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16489 (p : Pattern) (guard : d128479 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 29 with
  | false =>
    have hg : d128478 p = 1 := by simpa only [d128479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16488 p hg
    simpa only [d128479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16490 (p : Pattern) (guard : d128480 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 28 with
  | false =>
    have hg : d128479 p = 1 := by simpa only [d128480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16489 p hg
    simpa only [d128480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16491 (p : Pattern) (guard : d128481 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 27 with
  | false =>
    have hg : d128480 p = 1 := by simpa only [d128481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16490 p hg
    simpa only [d128481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16492 (p : Pattern) (guard : d128482 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 25 with
  | false =>
    have hg : d128481 p = 1 := by simpa only [d128482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16491 p hg
    simpa only [d128482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16493 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16494 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16495 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16496 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16497 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16498 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (0 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16499 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (0 : Int) + d48130 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Soko22Hazard87
