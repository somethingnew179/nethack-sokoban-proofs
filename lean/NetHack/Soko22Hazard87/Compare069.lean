import NetHack.Soko22Hazard87.Compare068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17250 (p : Pattern) (guard : d171137 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171136 p = 1 := by simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17249 p hg
    simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17251 (p : Pattern) (guard : d171138 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171132 p = 1 := by simpa only [d171138, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17186 p hg
    simpa only [d171138, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171137 p = 1 := by simpa only [d171138, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17250 p hg
    simpa only [d171138, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17252 (p : Pattern) (guard : d1382 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17253 (p : Pattern) (guard : d1383 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1382 p = 1 := by simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17252 p hg
    simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1383, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17254 (p : Pattern) (guard : d16658 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17255 (p : Pattern) (guard : d16659 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16658 p = 1 := by simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17254 p hg
    simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d16659, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17256 (p : Pattern) (guard : d16660 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1383 p = 1 := by simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17253 p hg
    simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16659 p = 1 := by simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17255 p hg
    simpa only [d16660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17257 (p : Pattern) (guard : d14996 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17258 (p : Pattern) (guard : d14997 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14996 p = 1 := by simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17257 p hg
    simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d14997, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17259 (p : Pattern) (guard : d15006 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17260 (p : Pattern) (guard : d15007 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15006 p = 1 := by simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17259 p hg
    simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15007, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17261 (p : Pattern) (guard : d16661 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14997 p = 1 := by simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15007 p = 1 := by simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17260 p hg
    simpa only [d16661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17262 (p : Pattern) (guard : d16662 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16660 p = 1 := by simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17256 p hg
    simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16661 p = 1 := by simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17261 p hg
    simpa only [d16662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17263 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17264 (p : Pattern) (guard : d1388 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17263 p hg
    simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1388, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17265 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17266 (p : Pattern) (guard : d1394 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17265 p hg
    simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17267 (p : Pattern) (guard : d1395 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1388 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17264 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17266 p hg
    simpa only [d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17268 (p : Pattern) (guard : d15008 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15007 p = 1 := by simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17260 p hg
    simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17269 (p : Pattern) (guard : d16672 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1395 p = 1 := by simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17267 p hg
    simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15008 p = 1 := by simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17268 p hg
    simpa only [d16672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17270 (p : Pattern) (guard : d16673 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16662 p = 1 := by simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17262 p hg
    simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16672 p = 1 := by simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17269 p hg
    simpa only [d16673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17271 (p : Pattern) (guard : d16674 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16673 p = 1 := by simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17270 p hg
    simpa only [d16674, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17272 (p : Pattern) (guard : d16675 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16674 p = 1 := by simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17271 p hg
    simpa only [d16675, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17273 (p : Pattern) (guard : d6352 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17274 (p : Pattern) (guard : d6353 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6352 p = 1 := by simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17273 p hg
    simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d6353, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17275 (p : Pattern) (guard : d6354 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6353 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17274 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17276 (p : Pattern) (guard : d15021 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17277 (p : Pattern) (guard : d15022 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15021 p = 1 := by simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17276 p hg
    simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15022, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17278 (p : Pattern) (guard : d15023 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15022 p = 1 := by simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17277 p hg
    simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17279 (p : Pattern) (guard : d15024 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6354 p = 1 := by simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17275 p hg
    simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15023 p = 1 := by simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17278 p hg
    simpa only [d15024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17280 (p : Pattern) (guard : d16676 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16672 p = 1 := by simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17269 p hg
    simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15024 p = 1 := by simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17279 p hg
    simpa only [d16676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17281 (p : Pattern) (guard : d16677 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16676 p = 1 := by simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17280 p hg
    simpa only [d16677, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17282 (p : Pattern) (guard : d16678 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16677 p = 1 := by simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17281 p hg
    simpa only [d16678, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17283 (p : Pattern) (guard : d16679 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16675 p = 1 := by simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17272 p hg
    simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16678 p = 1 := by simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17282 p hg
    simpa only [d16679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17284 (p : Pattern) (guard : d1400 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1394 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17266 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17285 (p : Pattern) (guard : d15042 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1400 p = 1 := by simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17284 p hg
    simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15023 p = 1 := by simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17278 p hg
    simpa only [d15042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17286 (p : Pattern) (guard : d16693 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16672 p = 1 := by simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17269 p hg
    simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15042 p = 1 := by simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17285 p hg
    simpa only [d16693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17287 (p : Pattern) (guard : d16694 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16693 p = 1 := by simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17286 p hg
    simpa only [d16694, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17288 (p : Pattern) (guard : d16695 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16694 p = 1 := by simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17287 p hg
    simpa only [d16695, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17289 (p : Pattern) (guard : d16696 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16695 p = 1 := by simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17288 p hg
    simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d16696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17290 (p : Pattern) (guard : d171139 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16679 p = 1 := by simpa only [d171139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17283 p hg
    simpa only [d171139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16696 p = 1 := by simpa only [d171139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17289 p hg
    simpa only [d171139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17291 (p : Pattern) (guard : d171140 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d171139 p = 1 := by simpa only [d171140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17290 p hg
    simpa only [d171140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d171140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17292 (p : Pattern) (guard : d171141 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d171140 p = 1 := by simpa only [d171141, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17291 p hg
    simpa only [d171141, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171141, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d171141, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17293 (p : Pattern) (guard : d171142 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171142, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d171142, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171141 p = 1 := by simpa only [d171142, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17292 p hg
    simpa only [d171142, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17294 (p : Pattern) (guard : d16697 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16696 p = 1 := by simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17289 p hg
    simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d16697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17295 (p : Pattern) (guard : d16698 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16697 p = 1 := by simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17294 p hg
    simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d16698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17296 (p : Pattern) (guard : d16699 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16698 p = 1 := by simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17295 p hg
    simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d16699, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17297 (p : Pattern) (guard : d16700 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16699 p = 1 := by simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17296 p hg
    simpa only [d16700, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17298 (p : Pattern) (guard : d171143 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d171142 p = 1 := by simpa only [d171143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17293 p hg
    simpa only [d171143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16700 p = 1 := by simpa only [d171143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17297 p hg
    simpa only [d171143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17299 (p : Pattern) (guard : d171144 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d171143 p = 1 := by simpa only [d171144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17298 p hg
    simpa only [d171144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17300 (p : Pattern) (guard : d171145 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d171144 p = 1 := by simpa only [d171145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17299 p hg
    simpa only [d171145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17301 (p : Pattern) (guard : d171146 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d171145 p = 1 := by simpa only [d171146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17300 p hg
    simpa only [d171146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17302 (p : Pattern) (guard : d16762 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16700 p = 1 := by simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17297 p hg
    simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17303 (p : Pattern) (guard : d16763 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16762 p = 1 := by simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17302 p hg
    simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17304 (p : Pattern) (guard : d16764 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16763 p = 1 := by simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17303 p hg
    simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17305 (p : Pattern) (guard : d16765 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16764 p = 1 := by simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17304 p hg
    simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17306 (p : Pattern) (guard : d171147 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d171146 p = 1 := by simpa only [d171147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17301 p hg
    simpa only [d171147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16765 p = 1 := by simpa only [d171147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17305 p hg
    simpa only [d171147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17307 (p : Pattern) (guard : d171148 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171147 p = 1 := by simpa only [d171148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17306 p hg
    simpa only [d171148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17308 (p : Pattern) (guard : d171149 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d171148 p = 1 := by simpa only [d171149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17307 p hg
    simpa only [d171149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17309 (p : Pattern) (guard : d171150 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171149 p = 1 := by simpa only [d171150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17308 p hg
    simpa only [d171150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17310 (p : Pattern) (guard : d171151 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171150 p = 1 := by simpa only [d171151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d171151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17311 (p : Pattern) (guard : d171152 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171152, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171152, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171151 p = 1 := by simpa only [d171152, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17310 p hg
    simpa only [d171152, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17312 (p : Pattern) (guard : d171153 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171152 p = 1 := by simpa only [d171153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17311 p hg
    simpa only [d171153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17313 (p : Pattern) (guard : d171154 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171153 p = 1 := by simpa only [d171154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17312 p hg
    simpa only [d171154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17314 (p : Pattern) (guard : d171155 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171154 p = 1 := by simpa only [d171155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17313 p hg
    simpa only [d171155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17315 (p : Pattern) (guard : d171156 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171155 p = 1 := by simpa only [d171156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17314 p hg
    simpa only [d171156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17316 (p : Pattern) (guard : d171157 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171156 p = 1 := by simpa only [d171157, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17315 p hg
    simpa only [d171157, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171157, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d171157, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17317 (p : Pattern) (guard : d171158 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171138 p = 1 := by simpa only [d171158, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17251 p hg
    simpa only [d171158, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171157 p = 1 := by simpa only [d171158, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17316 p hg
    simpa only [d171158, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17318 (p : Pattern) (guard : d171159 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171158 p = 1 := by simpa only [d171159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d171159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17319 (p : Pattern) (guard : d171160 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171159 p = 1 := by simpa only [d171160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17318 p hg
    simpa only [d171160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17320 (p : Pattern) (guard : d171161 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171160 p = 1 := by simpa only [d171161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17319 p hg
    simpa only [d171161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17321 (p : Pattern) (guard : d171162 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171161 p = 1 := by simpa only [d171162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17320 p hg
    simpa only [d171162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17322 (p : Pattern) (guard : d171163 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171162 p = 1 := by simpa only [d171163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d171163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17323 (p : Pattern) (guard : d171164 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171163 p = 1 := by simpa only [d171164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17322 p hg
    simpa only [d171164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17324 (p : Pattern) (guard : d171165 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171164 p = 1 := by simpa only [d171165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17323 p hg
    simpa only [d171165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17325 (p : Pattern) (guard : d171166 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171165 p = 1 := by simpa only [d171166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17324 p hg
    simpa only [d171166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17326 (p : Pattern) (guard : d171167 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d171130 p = 1 := by simpa only [d171167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17088 p hg
    simpa only [d171167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171166 p = 1 := by simpa only [d171167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17325 p hg
    simpa only [d171167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17327 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17328 (p : Pattern) (guard : d1558 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17327 p hg
    simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1558, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17329 (p : Pattern) (guard : d16787 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17330 (p : Pattern) (guard : d16788 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17329 p hg
    simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d16788, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17331 (p : Pattern) (guard : d16789 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17328 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17330 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17332 (p : Pattern) (guard : d15151 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17333 (p : Pattern) (guard : d15152 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17332 p hg
    simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d15152, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17334 (p : Pattern) (guard : d15156 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17335 (p : Pattern) (guard : d15157 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17334 p hg
    simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d15157, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17336 (p : Pattern) (guard : d16790 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17333 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17335 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17337 (p : Pattern) (guard : d16791 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17331 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17338 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17339 (p : Pattern) (guard : d1573 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17338 p hg
    simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1573, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17340 (p : Pattern) (guard : d16792 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17341 (p : Pattern) (guard : d16793 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17340 p hg
    simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d16793, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17342 (p : Pattern) (guard : d16794 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17339 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17341 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17343 (p : Pattern) (guard : d15158 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17335 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17344 (p : Pattern) (guard : d16795 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17343 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17345 (p : Pattern) (guard : d16796 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17337 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17344 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17346 (p : Pattern) (guard : d16797 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17345 p hg
    simpa only [d16797, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17347 (p : Pattern) (guard : d16798 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17346 p hg
    simpa only [d16798, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17348 (p : Pattern) (guard : d5136 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17349 (p : Pattern) (guard : d5137 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17348 p hg
    simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d5137, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17350 (p : Pattern) (guard : d5138 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17349 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17351 (p : Pattern) (guard : d15163 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17352 (p : Pattern) (guard : d15164 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d15164, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17353 (p : Pattern) (guard : d15165 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17352 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17354 (p : Pattern) (guard : d15166 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17350 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17353 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17355 (p : Pattern) (guard : d16799 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17344 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17354 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17356 (p : Pattern) (guard : d16800 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17355 p hg
    simpa only [d16800, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17357 (p : Pattern) (guard : d16801 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17356 p hg
    simpa only [d16801, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17358 (p : Pattern) (guard : d16802 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17347 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17357 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17359 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare17360 (p : Pattern) (guard : d1585 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17359 p hg
    simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d1585, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17361 (p : Pattern) (guard : d1588 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17360 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17362 (p : Pattern) (guard : d15171 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17361 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17353 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17363 (p : Pattern) (guard : d16803 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17344 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17362 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17364 (p : Pattern) (guard : d16804 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17363 p hg
    simpa only [d16804, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17365 (p : Pattern) (guard : d16805 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d16805, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17366 (p : Pattern) (guard : d16806 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17365 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17367 (p : Pattern) (guard : d16807 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17358 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17366 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17368 (p : Pattern) (guard : d16808 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17367 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17369 (p : Pattern) (guard : d16809 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17368 p hg
    simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16809, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17370 (p : Pattern) (guard : d16810 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17369 p hg
    simpa only [d16810, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17371 (p : Pattern) (guard : d16811 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17366 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17372 (p : Pattern) (guard : d16812 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17371 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17373 (p : Pattern) (guard : d16813 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17372 p hg
    simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16813, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17374 (p : Pattern) (guard : d16814 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17373 p hg
    simpa only [d16814, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17375 (p : Pattern) (guard : d16815 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17370 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17374 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17376 (p : Pattern) (guard : d16816 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17375 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17377 (p : Pattern) (guard : d16817 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17376 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17378 (p : Pattern) (guard : d16818 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17377 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17379 (p : Pattern) (guard : d16819 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17374 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17380 (p : Pattern) (guard : d16820 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17379 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17381 (p : Pattern) (guard : d16821 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17380 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17382 (p : Pattern) (guard : d16822 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17381 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17383 (p : Pattern) (guard : d16823 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17378 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17382 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17384 (p : Pattern) (guard : d16824 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17383 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17385 (p : Pattern) (guard : d16825 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17384 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17386 (p : Pattern) (guard : d16826 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17385 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17387 (p : Pattern) (guard : d16827 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17388 (p : Pattern) (guard : d16828 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16827 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17387 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17389 (p : Pattern) (guard : d16798 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17346 p hg
    simpa only [d16798, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17390 (p : Pattern) (guard : d16801 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17356 p hg
    simpa only [d16801, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17391 (p : Pattern) (guard : d16802 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17389 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17390 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17392 (p : Pattern) (guard : d16805 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17364 p hg
    simpa only [d16805, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17393 (p : Pattern) (guard : d16806 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17392 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17394 (p : Pattern) (guard : d16807 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17391 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17395 (p : Pattern) (guard : d16808 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17394 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17396 (p : Pattern) (guard : d16809 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17395 p hg
    simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16809, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17397 (p : Pattern) (guard : d16810 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17396 p hg
    simpa only [d16810, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17398 (p : Pattern) (guard : d16811 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17393 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17399 (p : Pattern) (guard : d16812 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17398 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17400 (p : Pattern) (guard : d16813 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17399 p hg
    simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16813, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17401 (p : Pattern) (guard : d16814 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17400 p hg
    simpa only [d16814, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17402 (p : Pattern) (guard : d16815 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17397 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17403 (p : Pattern) (guard : d16816 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17402 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17404 (p : Pattern) (guard : d16817 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17403 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17405 (p : Pattern) (guard : d16818 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17404 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17406 (p : Pattern) (guard : d16819 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17407 (p : Pattern) (guard : d16820 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17406 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17408 (p : Pattern) (guard : d16821 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17407 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17409 (p : Pattern) (guard : d16822 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17410 (p : Pattern) (guard : d16823 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17405 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17409 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17411 (p : Pattern) (guard : d16824 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17410 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17412 (p : Pattern) (guard : d16825 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17411 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17413 (p : Pattern) (guard : d16826 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17412 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17414 (p : Pattern) (guard : d16827 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17413 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17415 (p : Pattern) (guard : d16831 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17377 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17416 (p : Pattern) (guard : d16832 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17381 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17417 (p : Pattern) (guard : d16833 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17415 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17416 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17418 (p : Pattern) (guard : d16834 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17417 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17419 (p : Pattern) (guard : d16835 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17418 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17420 (p : Pattern) (guard : d16836 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17419 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17421 (p : Pattern) (guard : d16837 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17420 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17422 (p : Pattern) (guard : d16838 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16827 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17414 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17421 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17423 (p : Pattern) (guard : d16839 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16828 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17388 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16838 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17422 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17424 (p : Pattern) (guard : d16840 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16839 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17423 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17425 (p : Pattern) (guard : d171168 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16840 p = 1 := by simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17424 p hg
    simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17426 (p : Pattern) (guard : d171169 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171168 p = 1 := by simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17425 p hg
    simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17427 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17428 (p : Pattern) (guard : d1558 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17427 p hg
    simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1558, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17429 (p : Pattern) (guard : d16787 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17430 (p : Pattern) (guard : d16788 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17429 p hg
    simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d16788, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17431 (p : Pattern) (guard : d16789 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17428 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17430 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17432 (p : Pattern) (guard : d15151 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17433 (p : Pattern) (guard : d15152 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17432 p hg
    simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d15152, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17434 (p : Pattern) (guard : d15156 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17435 (p : Pattern) (guard : d15157 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17434 p hg
    simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d15157, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17436 (p : Pattern) (guard : d16790 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17433 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17435 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17437 (p : Pattern) (guard : d16791 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17431 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17436 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17438 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17439 (p : Pattern) (guard : d1573 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17438 p hg
    simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1573, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17440 (p : Pattern) (guard : d16792 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17441 (p : Pattern) (guard : d16793 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17440 p hg
    simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d16793, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17442 (p : Pattern) (guard : d16794 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17439 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17441 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17443 (p : Pattern) (guard : d15158 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17435 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17444 (p : Pattern) (guard : d16795 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17442 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17443 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17445 (p : Pattern) (guard : d16796 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17437 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17444 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17446 (p : Pattern) (guard : d16797 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17445 p hg
    simpa only [d16797, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17447 (p : Pattern) (guard : d16798 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17446 p hg
    simpa only [d16798, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17448 (p : Pattern) (guard : d5136 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17449 (p : Pattern) (guard : d5137 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17448 p hg
    simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d5137, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17450 (p : Pattern) (guard : d5138 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17449 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17451 (p : Pattern) (guard : d15163 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17452 (p : Pattern) (guard : d15164 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17451 p hg
    simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d15164, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17453 (p : Pattern) (guard : d15165 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17452 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17454 (p : Pattern) (guard : d15166 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17450 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17453 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17455 (p : Pattern) (guard : d16799 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17444 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17454 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17456 (p : Pattern) (guard : d16800 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17455 p hg
    simpa only [d16800, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17457 (p : Pattern) (guard : d16801 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17456 p hg
    simpa only [d16801, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17458 (p : Pattern) (guard : d16802 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17447 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17457 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17459 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare17460 (p : Pattern) (guard : d1585 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17459 p hg
    simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d1585, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17461 (p : Pattern) (guard : d1588 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17460 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17462 (p : Pattern) (guard : d15171 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17461 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17453 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17463 (p : Pattern) (guard : d16803 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17444 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17462 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17464 (p : Pattern) (guard : d16804 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17463 p hg
    simpa only [d16804, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17465 (p : Pattern) (guard : d16805 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17464 p hg
    simpa only [d16805, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17466 (p : Pattern) (guard : d16806 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17465 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17467 (p : Pattern) (guard : d16807 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17458 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17466 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17468 (p : Pattern) (guard : d16808 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17467 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17469 (p : Pattern) (guard : d16809 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17468 p hg
    simpa only [d16809, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16809, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17470 (p : Pattern) (guard : d16810 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17469 p hg
    simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17471 (p : Pattern) (guard : d16811 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17466 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17472 (p : Pattern) (guard : d16812 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17471 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17473 (p : Pattern) (guard : d16813 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17472 p hg
    simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16813, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17474 (p : Pattern) (guard : d16814 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17473 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17475 (p : Pattern) (guard : d16815 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17470 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17474 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17476 (p : Pattern) (guard : d16816 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17475 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17477 (p : Pattern) (guard : d16817 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17476 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17478 (p : Pattern) (guard : d16831 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17477 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17479 (p : Pattern) (guard : d16819 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17474 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17480 (p : Pattern) (guard : d16820 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17479 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17481 (p : Pattern) (guard : d16821 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17480 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17482 (p : Pattern) (guard : d16832 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17481 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17483 (p : Pattern) (guard : d16833 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17478 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17482 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17484 (p : Pattern) (guard : d16834 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17483 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17485 (p : Pattern) (guard : d16835 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17484 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17486 (p : Pattern) (guard : d16836 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17485 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17487 (p : Pattern) (guard : d16837 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17486 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17488 (p : Pattern) (guard : d171170 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171170, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171170, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d171170, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17487 p hg
    simpa only [d171170, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17489 (p : Pattern) (guard : d171171 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171170 p = 1 := by simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17488 p hg
    simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17490 (p : Pattern) (guard : d171172 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171171 p = 1 := by simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17489 p hg
    simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17491 (p : Pattern) (guard : d171173 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171172 p = 1 := by simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17490 p hg
    simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17492 (p : Pattern) (guard : d171174 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171173 p = 1 := by simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17491 p hg
    simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17493 (p : Pattern) (guard : d171175 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171169 p = 1 := by simpa only [d171175, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17426 p hg
    simpa only [d171175, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171174 p = 1 := by simpa only [d171175, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17492 p hg
    simpa only [d171175, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17494 (p : Pattern) (guard : d1859 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17495 (p : Pattern) (guard : d1860 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1859 p = 1 := by simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17494 p hg
    simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d1860, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17496 (p : Pattern) (guard : d17013 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17497 (p : Pattern) (guard : d17014 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17013 p = 1 := by simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17496 p hg
    simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d17014, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17498 (p : Pattern) (guard : d17015 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1860 p = 1 := by simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17495 p hg
    simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17014 p = 1 := by simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17497 p hg
    simpa only [d17015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17499 (p : Pattern) (guard : d15389 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
end NetHack.Soko22Hazard87
