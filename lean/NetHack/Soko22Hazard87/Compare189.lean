import NetHack.Soko22Hazard87.Compare188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47250 (p : Pattern) (guard : d369576 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369575 p = 1 := by simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47248 p hg
    simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369504 p = 1 := by simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47249 p hg
    simpa only [d369576, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47251 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (1 : Int) + d49319 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare47252 (p : Pattern) (guard : d46040 p = 1) : d47634 p ≤ (1 : Int) + d49322 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47006 p hg
    simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45587 p = 1 := by simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47004 p hg
    simpa only [d46040, d49322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47253 (p : Pattern) (guard : d46041 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47251 p hg
    simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46040 p = 1 := by simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47252 p hg
    simpa only [d46041, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47254 (p : Pattern) (guard : d46042 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46041 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47253 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d46042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47255 (p : Pattern) (guard : d46043 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d46042 p = 1 := by simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47254 p hg
    simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46787 p hg
    simpa only [d46043, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47256 (p : Pattern) (guard : d369497 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46043 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47255 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369386 p = 1 := by simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47014 p hg
    simpa only [d369497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47257 (p : Pattern) (guard : d46459 p = 1) : d47634 p ≤ (1 : Int) + d49319 p := by
  cases selected : p 225 with
  | false =>
    have hg : d44996 p = 1 := by simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47000 p hg
    simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46782 p hg
    simpa only [d46459, d49319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47258 (p : Pattern) (guard : d46460 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46459 p = 1 := by simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47257 p hg
    simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46784 p hg
    simpa only [d46460, d49323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47259 (p : Pattern) (guard : d369498 p = 1) : d47634 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46460 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47258 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d369498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47260 (p : Pattern) (guard : d369499 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d369498 p = 1 := by simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47259 p hg
    simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46787 p hg
    simpa only [d369499, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47261 (p : Pattern) (guard : d369500 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d369499 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47260 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46788 p hg
    simpa only [d369500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47262 (p : Pattern) (guard : d369501 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47256 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369500 p = 1 := by simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47261 p hg
    simpa only [d369501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47263 (p : Pattern) (guard : d369502 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369501 p = 1 := by simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47262 p hg
    simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d369502, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47264 (p : Pattern) (guard : d369503 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47263 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369389 p = 1 := by simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47017 p hg
    simpa only [d369503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47265 (p : Pattern) (guard : d369504 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369503 p = 1 := by simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47264 p hg
    simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369504, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47266 (p : Pattern) (guard : d369505 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369504 p = 1 := by simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47265 p hg
    simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369505, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47267 (p : Pattern) (guard : d369577 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369576 p = 1 := by simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47250 p hg
    simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369505 p = 1 := by simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47266 p hg
    simpa only [d369577, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47268 (p : Pattern) (guard : d369578 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369577 p = 1 := by simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47267 p hg
    simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369578, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47269 (p : Pattern) (guard : d369579 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369578 p = 1 := by simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47268 p hg
    simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369437 p = 1 := by simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47022 p hg
    simpa only [d369579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47270 (p : Pattern) (guard : d369509 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46993 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47271 (p : Pattern) (guard : d369510 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47270 p hg
    simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d369510, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47272 (p : Pattern) (guard : d369511 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47271 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46775 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47273 (p : Pattern) (guard : d369580 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369511 p = 1 := by simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47272 p hg
    simpa only [d369580, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47274 (p : Pattern) (guard : d369512 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47107 p hg
    simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369512, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47275 (p : Pattern) (guard : d369581 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369580 p = 1 := by simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47273 p hg
    simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369512 p = 1 := by simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47274 p hg
    simpa only [d369581, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47276 (p : Pattern) (guard : d369509 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369387 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47015 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d369509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47277 (p : Pattern) (guard : d369510 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369509 p = 1 := by simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47276 p hg
    simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d369510, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47278 (p : Pattern) (guard : d369511 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369510 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47277 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275503 p = 1 := by simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46792 p hg
    simpa only [d369511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47279 (p : Pattern) (guard : d369512 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369511 p = 1 := by simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47278 p hg
    simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369512, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47280 (p : Pattern) (guard : d369513 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369512 p = 1 := by simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47279 p hg
    simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369513, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47281 (p : Pattern) (guard : d369582 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369581 p = 1 := by simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47275 p hg
    simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369513 p = 1 := by simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47280 p hg
    simpa only [d369582, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47282 (p : Pattern) (guard : d369583 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369582 p = 1 := by simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47281 p hg
    simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369583, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47283 (p : Pattern) (guard : d369584 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369583 p = 1 := by simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47282 p hg
    simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275549 p = 1 := by simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46799 p hg
    simpa only [d369584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47284 (p : Pattern) (guard : d369585 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369579 p = 1 := by simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47269 p hg
    simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369584 p = 1 := by simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47283 p hg
    simpa only [d369585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47285 (p : Pattern) (guard : d369586 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369585 p = 1 := by simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47284 p hg
    simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369439 p = 1 := by simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47024 p hg
    simpa only [d369586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47286 (p : Pattern) (guard : d369587 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369586 p = 1 := by simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47285 p hg
    simpa only [d369587, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47287 (p : Pattern) (guard : d369588 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369587 p = 1 := by simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47286 p hg
    simpa only [d369588, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47288 (p : Pattern) (guard : d369589 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369588 p = 1 := by simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47287 p hg
    simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369442 p = 1 := by simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47027 p hg
    simpa only [d369589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47289 (p : Pattern) (guard : d369590 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369589 p = 1 := by simpa only [d369590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47288 p hg
    simpa only [d369590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369443 p = 1 := by simpa only [d369590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47028 p hg
    simpa only [d369590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47290 (p : Pattern) (guard : d369591 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369590 p = 1 := by simpa only [d369591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47289 p hg
    simpa only [d369591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47291 (p : Pattern) (guard : d369592 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369591 p = 1 := by simpa only [d369592, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47290 p hg
    simpa only [d369592, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369592, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d369592, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47292 (p : Pattern) (guard : d369593 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369593, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369593, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369592 p = 1 := by simpa only [d369593, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47291 p hg
    simpa only [d369593, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47293 (p : Pattern) (guard : d369594 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369593 p = 1 := by simpa only [d369594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47292 p hg
    simpa only [d369594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369447 p = 1 := by simpa only [d369594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47032 p hg
    simpa only [d369594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47294 (p : Pattern) (guard : d369595 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369594 p = 1 := by simpa only [d369595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47293 p hg
    simpa only [d369595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47295 (p : Pattern) (guard : d369596 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369595 p = 1 := by simpa only [d369596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47294 p hg
    simpa only [d369596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47296 (p : Pattern) (guard : d369597 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369596 p = 1 := by simpa only [d369597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47295 p hg
    simpa only [d369597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47297 (p : Pattern) (guard : d369598 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369597 p = 1 := by simpa only [d369598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47296 p hg
    simpa only [d369598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369451 p = 1 := by simpa only [d369598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47036 p hg
    simpa only [d369598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47298 (p : Pattern) (guard : d369599 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369598 p = 1 := by simpa only [d369599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47297 p hg
    simpa only [d369599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47299 (p : Pattern) (guard : d369600 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369447 p = 1 := by simpa only [d369600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47032 p hg
    simpa only [d369600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47300 (p : Pattern) (guard : d369601 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369600 p = 1 := by simpa only [d369601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47299 p hg
    simpa only [d369601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47301 (p : Pattern) (guard : d369602 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369601 p = 1 := by simpa only [d369602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47300 p hg
    simpa only [d369602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47302 (p : Pattern) (guard : d369603 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369602 p = 1 := by simpa only [d369603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47301 p hg
    simpa only [d369603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47303 (p : Pattern) (guard : d369604 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369603 p = 1 := by simpa only [d369604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47302 p hg
    simpa only [d369604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47304 (p : Pattern) (guard : d369605 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369604 p = 1 := by simpa only [d369605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47303 p hg
    simpa only [d369605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47305 (p : Pattern) (guard : d369606 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369599 p = 1 := by simpa only [d369606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47298 p hg
    simpa only [d369606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369605 p = 1 := by simpa only [d369606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47304 p hg
    simpa only [d369606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47306 (p : Pattern) (guard : d369607 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369606 p = 1 := by simpa only [d369607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47305 p hg
    simpa only [d369607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47307 (p : Pattern) (guard : d369608 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369607 p = 1 := by simpa only [d369608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47306 p hg
    simpa only [d369608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47308 (p : Pattern) (guard : d369609 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369609, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369609, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369608 p = 1 := by simpa only [d369609, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47307 p hg
    simpa only [d369609, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47309 (p : Pattern) (guard : d369610 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369609 p = 1 := by simpa only [d369610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47308 p hg
    simpa only [d369610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47310 (p : Pattern) (guard : d275866 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275564 p = 1 := by simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46817 p hg
    simpa only [d275866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47311 (p : Pattern) (guard : d275867 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d275866 p = 1 := by simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47310 p hg
    simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47312 (p : Pattern) (guard : d275868 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275867 p = 1 := by simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47311 p hg
    simpa only [d275868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47313 (p : Pattern) (guard : d275869 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275868 p = 1 := by simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47312 p hg
    simpa only [d275869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47314 (p : Pattern) (guard : d275870 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275869 p = 1 := by simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47313 p hg
    simpa only [d275870, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47315 (p : Pattern) (guard : d275871 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275870 p = 1 := by simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47314 p hg
    simpa only [d275871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47316 (p : Pattern) (guard : d369611 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369610 p = 1 := by simpa only [d369611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47309 p hg
    simpa only [d369611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275871 p = 1 := by simpa only [d369611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47315 p hg
    simpa only [d369611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47317 (p : Pattern) (guard : d369612 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369611 p = 1 := by simpa only [d369612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47316 p hg
    simpa only [d369612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47318 (p : Pattern) (guard : d369613 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369612 p = 1 := by simpa only [d369613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47317 p hg
    simpa only [d369613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47319 (p : Pattern) (guard : d369614 p = 1) : d50822 p ≤ (1 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369613 p = 1 := by simpa only [d369614, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47318 p hg
    simpa only [d369614, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369614, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d369614, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47320 (p : Pattern) (guard : d369615 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d369574 p = 1 := by simpa only [d369615, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47229 p hg
    simpa only [d369615, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369614 p = 1 := by simpa only [d369615, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47319 p hg
    simpa only [d369615, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47321 (p : Pattern) (guard : d369616 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369615 p = 1 := by simpa only [d369616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47320 p hg
    simpa only [d369616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47322 (p : Pattern) (guard : d369617 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369616 p = 1 := by simpa only [d369617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47321 p hg
    simpa only [d369617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47323 (p : Pattern) (guard : d369618 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369617 p = 1 := by simpa only [d369618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47322 p hg
    simpa only [d369618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47324 (p : Pattern) (guard : d369619 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369618 p = 1 := by simpa only [d369619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47323 p hg
    simpa only [d369619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47325 (p : Pattern) (guard : d369620 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369619 p = 1 := by simpa only [d369620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47324 p hg
    simpa only [d369620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47326 (p : Pattern) (guard : d369621 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369620 p = 1 := by simpa only [d369621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47325 p hg
    simpa only [d369621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47327 (p : Pattern) (guard : d369622 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d369469 p = 1 := by simpa only [d369622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47054 p hg
    simpa only [d369622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369621 p = 1 := by simpa only [d369622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47326 p hg
    simpa only [d369622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47328 (p : Pattern) (guard : d369623 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46890 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47329 (p : Pattern) (guard : d369624 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47117 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369623 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47328 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47330 (p : Pattern) (guard : d369625 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369624 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47329 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47331 (p : Pattern) (guard : d369626 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369625 p = 1 := by simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47330 p hg
    simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369626, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47332 (p : Pattern) (guard : d369627 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369626 p = 1 := by simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47331 p hg
    simpa only [d369627, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47333 (p : Pattern) (guard : d369628 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369623 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47328 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47334 (p : Pattern) (guard : d369629 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369628 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47333 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47335 (p : Pattern) (guard : d369630 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369629 p = 1 := by simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47334 p hg
    simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369630, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47336 (p : Pattern) (guard : d369631 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369630 p = 1 := by simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47335 p hg
    simpa only [d369631, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47337 (p : Pattern) (guard : d369632 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369631 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47336 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47338 (p : Pattern) (guard : d369633 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369632 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47337 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47339 (p : Pattern) (guard : d369634 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369633 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47338 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47340 (p : Pattern) (guard : d369635 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369634 p = 1 := by simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47339 p hg
    simpa only [d369635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47341 (p : Pattern) (guard : d369636 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369631 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47336 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47342 (p : Pattern) (guard : d369637 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369636 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47341 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47343 (p : Pattern) (guard : d369638 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369637 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47342 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47344 (p : Pattern) (guard : d369639 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369638 p = 1 := by simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47343 p hg
    simpa only [d369639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47345 (p : Pattern) (guard : d369640 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369635 p = 1 := by simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47340 p hg
    simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369639 p = 1 := by simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47344 p hg
    simpa only [d369640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47346 (p : Pattern) (guard : d369641 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369640 p = 1 := by simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47345 p hg
    simpa only [d369641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47347 (p : Pattern) (guard : d369642 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369641 p = 1 := by simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47346 p hg
    simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47348 (p : Pattern) (guard : d369643 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369642 p = 1 := by simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47347 p hg
    simpa only [d369643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47349 (p : Pattern) (guard : d369644 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369643 p = 1 := by simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47348 p hg
    simpa only [d369644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47350 (p : Pattern) (guard : d369645 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369644 p = 1 := by simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47349 p hg
    simpa only [d369645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47351 (p : Pattern) (guard : d369646 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369645 p = 1 := by simpa only [d369646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47350 p hg
    simpa only [d369646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47352 (p : Pattern) (guard : d369647 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369646 p = 1 := by simpa only [d369647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47351 p hg
    simpa only [d369647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47353 (p : Pattern) (guard : d369648 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369634 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47339 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47354 (p : Pattern) (guard : d369649 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369638 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47343 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47355 (p : Pattern) (guard : d369650 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369648 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47353 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369649 p = 1 := by simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47354 p hg
    simpa only [d369650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47356 (p : Pattern) (guard : d369651 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369650 p = 1 := by simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47355 p hg
    simpa only [d369651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47357 (p : Pattern) (guard : d369652 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369651 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47356 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47358 (p : Pattern) (guard : d369653 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369652 p = 1 := by simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47357 p hg
    simpa only [d369653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47359 (p : Pattern) (guard : d369654 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369653 p = 1 := by simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47358 p hg
    simpa only [d369654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47360 (p : Pattern) (guard : d369655 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369644 p = 1 := by simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47349 p hg
    simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369654 p = 1 := by simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47359 p hg
    simpa only [d369655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47361 (p : Pattern) (guard : d369656 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369645 p = 1 := by simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47350 p hg
    simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369655 p = 1 := by simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47360 p hg
    simpa only [d369656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47362 (p : Pattern) (guard : d369657 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369656 p = 1 := by simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47361 p hg
    simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47363 (p : Pattern) (guard : d369658 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369647 p = 1 := by simpa only [d369658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47352 p hg
    simpa only [d369658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369657 p = 1 := by simpa only [d369658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47362 p hg
    simpa only [d369658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47364 (p : Pattern) (guard : d369659 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369633 p = 1 := by simpa only [d369659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47338 p hg
    simpa only [d369659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47365 (p : Pattern) (guard : d369660 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369659 p = 1 := by simpa only [d369660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47364 p hg
    simpa only [d369660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47366 (p : Pattern) (guard : d369661 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369637 p = 1 := by simpa only [d369661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47342 p hg
    simpa only [d369661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47367 (p : Pattern) (guard : d369662 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369661 p = 1 := by simpa only [d369662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47366 p hg
    simpa only [d369662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47368 (p : Pattern) (guard : d369663 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369660 p = 1 := by simpa only [d369663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47365 p hg
    simpa only [d369663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369662 p = 1 := by simpa only [d369663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47367 p hg
    simpa only [d369663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47369 (p : Pattern) (guard : d369664 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369663 p = 1 := by simpa only [d369664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47368 p hg
    simpa only [d369664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47370 (p : Pattern) (guard : d369665 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369664 p = 1 := by simpa only [d369665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47369 p hg
    simpa only [d369665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47371 (p : Pattern) (guard : d369666 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369665 p = 1 := by simpa only [d369666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47370 p hg
    simpa only [d369666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47372 (p : Pattern) (guard : d369667 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369632 p = 1 := by simpa only [d369667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47337 p hg
    simpa only [d369667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47373 (p : Pattern) (guard : d369668 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369667 p = 1 := by simpa only [d369668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47372 p hg
    simpa only [d369668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47374 (p : Pattern) (guard : d369669 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369668 p = 1 := by simpa only [d369669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47373 p hg
    simpa only [d369669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47375 (p : Pattern) (guard : d369670 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369636 p = 1 := by simpa only [d369670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47341 p hg
    simpa only [d369670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47376 (p : Pattern) (guard : d369671 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369670 p = 1 := by simpa only [d369671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47375 p hg
    simpa only [d369671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47377 (p : Pattern) (guard : d369672 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369671 p = 1 := by simpa only [d369672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47376 p hg
    simpa only [d369672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47378 (p : Pattern) (guard : d369673 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369669 p = 1 := by simpa only [d369673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47374 p hg
    simpa only [d369673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369672 p = 1 := by simpa only [d369673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47377 p hg
    simpa only [d369673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47379 (p : Pattern) (guard : d369674 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369673 p = 1 := by simpa only [d369674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47378 p hg
    simpa only [d369674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47380 (p : Pattern) (guard : d369675 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369674 p = 1 := by simpa only [d369675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47379 p hg
    simpa only [d369675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47381 (p : Pattern) (guard : d46053 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47090 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47382 (p : Pattern) (guard : d46054 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47381 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47383 (p : Pattern) (guard : d46055 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47382 p hg
    simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d46055, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47384 (p : Pattern) (guard : d179205 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46657 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47385 (p : Pattern) (guard : d369676 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47091 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47384 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47386 (p : Pattern) (guard : d369677 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47385 p hg
    simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d369677, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47387 (p : Pattern) (guard : d369678 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47383 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47386 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47388 (p : Pattern) (guard : d369679 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47387 p hg
    simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369679, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47389 (p : Pattern) (guard : d369680 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47388 p hg
    simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369680, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47390 (p : Pattern) (guard : d369681 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47389 p hg
    simpa only [d369681, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47391 (p : Pattern) (guard : d369682 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369681 p = 1 := by simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47390 p hg
    simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369682, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47392 (p : Pattern) (guard : d369683 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47098 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47106 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47393 (p : Pattern) (guard : d369684 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47392 p hg
    simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369684, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47394 (p : Pattern) (guard : d369685 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47393 p hg
    simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369685, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47395 (p : Pattern) (guard : d369686 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47394 p hg
    simpa only [d369686, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47396 (p : Pattern) (guard : d369687 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369686 p = 1 := by simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47395 p hg
    simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369687, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47397 (p : Pattern) (guard : d369688 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369682 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47391 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369687 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47396 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47398 (p : Pattern) (guard : d369689 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47091 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47399 (p : Pattern) (guard : d369690 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47398 p hg
    simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46660 p hg
    simpa only [d369690, d50553, d367764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47400 (p : Pattern) (guard : d369691 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47399 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47106 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47401 (p : Pattern) (guard : d369692 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47400 p hg
    simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369692, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47402 (p : Pattern) (guard : d369693 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47401 p hg
    simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369693, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47403 (p : Pattern) (guard : d369694 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47402 p hg
    simpa only [d369694, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47404 (p : Pattern) (guard : d369695 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369694 p = 1 := by simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47403 p hg
    simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369695, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47405 (p : Pattern) (guard : d369696 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47404 p hg
    simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369515 p = 1 := by simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47111 p hg
    simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47406 (p : Pattern) (guard : d369697 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47397 p hg
    simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369696 p = 1 := by simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47405 p hg
    simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47407 (p : Pattern) (guard : d369698 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369697 p = 1 := by simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47406 p hg
    simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369517 p = 1 := by simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47408 (p : Pattern) (guard : d369699 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369699, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369699, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369698 p = 1 := by simpa only [d369699, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47407 p hg
    simpa only [d369699, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47409 (p : Pattern) (guard : d369700 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369700, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369700, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369699 p = 1 := by simpa only [d369700, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47408 p hg
    simpa only [d369700, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47410 (p : Pattern) (guard : d369701 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369516 p = 1 := by simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47112 p hg
    simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46672 p hg
    simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47411 (p : Pattern) (guard : d369702 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47113 p hg
    simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369701 p = 1 := by simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47410 p hg
    simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47412 (p : Pattern) (guard : d369703 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369703, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369703, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369702 p = 1 := by simpa only [d369703, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47411 p hg
    simpa only [d369703, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47413 (p : Pattern) (guard : d369704 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369704, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369704, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369703 p = 1 := by simpa only [d369704, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47412 p hg
    simpa only [d369704, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47414 (p : Pattern) (guard : d369705 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369700 p = 1 := by simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47409 p hg
    simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369704 p = 1 := by simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47413 p hg
    simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47415 (p : Pattern) (guard : d369706 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369705 p = 1 := by simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47414 p hg
    simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369521 p = 1 := by simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47117 p hg
    simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47416 (p : Pattern) (guard : d369707 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369706 p = 1 := by simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47415 p hg
    simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47417 (p : Pattern) (guard : d369708 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369707 p = 1 := by simpa only [d369708, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47416 p hg
    simpa only [d369708, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369708, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369708, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47418 (p : Pattern) (guard : d369709 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369709, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369709, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369708 p = 1 := by simpa only [d369709, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47417 p hg
    simpa only [d369709, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47419 (p : Pattern) (guard : d369710 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369709 p = 1 := by simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47418 p hg
    simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369627 p = 1 := by simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47420 (p : Pattern) (guard : d369711 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369710 p = 1 := by simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47419 p hg
    simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47421 (p : Pattern) (guard : d369712 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369711 p = 1 := by simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47420 p hg
    simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47422 (p : Pattern) (guard : d369713 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369712 p = 1 := by simpa only [d369713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47421 p hg
    simpa only [d369713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47423 (p : Pattern) (guard : d369714 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369713 p = 1 := by simpa only [d369714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47422 p hg
    simpa only [d369714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369635 p = 1 := by simpa only [d369714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47340 p hg
    simpa only [d369714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47424 (p : Pattern) (guard : d369715 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369714 p = 1 := by simpa only [d369715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47423 p hg
    simpa only [d369715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47425 (p : Pattern) (guard : d369716 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47332 p hg
    simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47426 (p : Pattern) (guard : d369717 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369716 p = 1 := by simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47425 p hg
    simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47427 (p : Pattern) (guard : d369718 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369717 p = 1 := by simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47426 p hg
    simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47428 (p : Pattern) (guard : d369719 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369718 p = 1 := by simpa only [d369719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47427 p hg
    simpa only [d369719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47429 (p : Pattern) (guard : d369720 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369719 p = 1 := by simpa only [d369720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47428 p hg
    simpa only [d369720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47430 (p : Pattern) (guard : d369721 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369720 p = 1 := by simpa only [d369721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47429 p hg
    simpa only [d369721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47431 (p : Pattern) (guard : d369722 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369715 p = 1 := by simpa only [d369722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47424 p hg
    simpa only [d369722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369721 p = 1 := by simpa only [d369722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47430 p hg
    simpa only [d369722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47432 (p : Pattern) (guard : d369723 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369675 p = 1 := by simpa only [d369723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47380 p hg
    simpa only [d369723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369722 p = 1 := by simpa only [d369723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47431 p hg
    simpa only [d369723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47433 (p : Pattern) (guard : d369724 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369666 p = 1 := by simpa only [d369724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47371 p hg
    simpa only [d369724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369723 p = 1 := by simpa only [d369724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47432 p hg
    simpa only [d369724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47434 (p : Pattern) (guard : d369725 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369724 p = 1 := by simpa only [d369725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47433 p hg
    simpa only [d369725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47435 (p : Pattern) (guard : d369726 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369659 p = 1 := by simpa only [d369726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47364 p hg
    simpa only [d369726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47436 (p : Pattern) (guard : d369727 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369661 p = 1 := by simpa only [d369727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47366 p hg
    simpa only [d369727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47437 (p : Pattern) (guard : d369728 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369726 p = 1 := by simpa only [d369728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47435 p hg
    simpa only [d369728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369727 p = 1 := by simpa only [d369728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47436 p hg
    simpa only [d369728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47438 (p : Pattern) (guard : d369729 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369728 p = 1 := by simpa only [d369729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47437 p hg
    simpa only [d369729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47439 (p : Pattern) (guard : d369730 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369729 p = 1 := by simpa only [d369730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47438 p hg
    simpa only [d369730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47440 (p : Pattern) (guard : d369731 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369730 p = 1 := by simpa only [d369731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47439 p hg
    simpa only [d369731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47441 (p : Pattern) (guard : d369732 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369668 p = 1 := by simpa only [d369732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47373 p hg
    simpa only [d369732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47442 (p : Pattern) (guard : d369733 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369671 p = 1 := by simpa only [d369733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47376 p hg
    simpa only [d369733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47443 (p : Pattern) (guard : d369734 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369732 p = 1 := by simpa only [d369734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47441 p hg
    simpa only [d369734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369733 p = 1 := by simpa only [d369734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47442 p hg
    simpa only [d369734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47444 (p : Pattern) (guard : d369735 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369734 p = 1 := by simpa only [d369735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47443 p hg
    simpa only [d369735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47445 (p : Pattern) (guard : d369736 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369735 p = 1 := by simpa only [d369736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47444 p hg
    simpa only [d369736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47446 (p : Pattern) (guard : d369737 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369712 p = 1 := by simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47421 p hg
    simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47447 (p : Pattern) (guard : d369738 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369737 p = 1 := by simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47446 p hg
    simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369648 p = 1 := by simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47353 p hg
    simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47448 (p : Pattern) (guard : d369739 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369738 p = 1 := by simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47447 p hg
    simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47449 (p : Pattern) (guard : d369740 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369718 p = 1 := by simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47427 p hg
    simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47450 (p : Pattern) (guard : d369741 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369740 p = 1 := by simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47449 p hg
    simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47451 (p : Pattern) (guard : d369742 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369741 p = 1 := by simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47450 p hg
    simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47452 (p : Pattern) (guard : d369743 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369739 p = 1 := by simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47448 p hg
    simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369742 p = 1 := by simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47451 p hg
    simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47453 (p : Pattern) (guard : d369744 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d369736 p = 1 := by simpa only [d369744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47445 p hg
    simpa only [d369744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369743 p = 1 := by simpa only [d369744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47452 p hg
    simpa only [d369744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47454 (p : Pattern) (guard : d369745 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d369731 p = 1 := by simpa only [d369745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47440 p hg
    simpa only [d369745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369744 p = 1 := by simpa only [d369745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47453 p hg
    simpa only [d369745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47455 (p : Pattern) (guard : d369746 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369724 p = 1 := by simpa only [d369746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47433 p hg
    simpa only [d369746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369745 p = 1 := by simpa only [d369746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47454 p hg
    simpa only [d369746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47456 (p : Pattern) (guard : d369747 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369725 p = 1 := by simpa only [d369747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47434 p hg
    simpa only [d369747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369746 p = 1 := by simpa only [d369747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47455 p hg
    simpa only [d369747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47457 (p : Pattern) (guard : d369748 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369639 p = 1 := by simpa only [d369748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47344 p hg
    simpa only [d369748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47458 (p : Pattern) (guard : d369749 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369748 p = 1 := by simpa only [d369749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47457 p hg
    simpa only [d369749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47459 (p : Pattern) (guard : d369750 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369749 p = 1 := by simpa only [d369750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47458 p hg
    simpa only [d369750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47460 (p : Pattern) (guard : d369751 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369750 p = 1 := by simpa only [d369751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47459 p hg
    simpa only [d369751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47461 (p : Pattern) (guard : d369752 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369751 p = 1 := by simpa only [d369752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47460 p hg
    simpa only [d369752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47462 (p : Pattern) (guard : d369753 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369644 p = 1 := by simpa only [d369753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47349 p hg
    simpa only [d369753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369752 p = 1 := by simpa only [d369753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47461 p hg
    simpa only [d369753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47463 (p : Pattern) (guard : d369754 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369649 p = 1 := by simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47354 p hg
    simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47464 (p : Pattern) (guard : d369755 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369754 p = 1 := by simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47463 p hg
    simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47465 (p : Pattern) (guard : d369756 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369755 p = 1 := by simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47464 p hg
    simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47466 (p : Pattern) (guard : d369757 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369756 p = 1 := by simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47465 p hg
    simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47467 (p : Pattern) (guard : d369758 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369757 p = 1 := by simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47466 p hg
    simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47468 (p : Pattern) (guard : d369759 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369752 p = 1 := by simpa only [d369759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47461 p hg
    simpa only [d369759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369758 p = 1 := by simpa only [d369759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47467 p hg
    simpa only [d369759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47469 (p : Pattern) (guard : d369760 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369753 p = 1 := by simpa only [d369760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47462 p hg
    simpa only [d369760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369759 p = 1 := by simpa only [d369760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47468 p hg
    simpa only [d369760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47470 (p : Pattern) (guard : d369761 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369747 p = 1 := by simpa only [d369761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47456 p hg
    simpa only [d369761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369760 p = 1 := by simpa only [d369761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47469 p hg
    simpa only [d369761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47471 (p : Pattern) (guard : d369762 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369761 p = 1 := by simpa only [d369762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47470 p hg
    simpa only [d369762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47472 (p : Pattern) (guard : d369763 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369658 p = 1 := by simpa only [d369763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47363 p hg
    simpa only [d369763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369762 p = 1 := by simpa only [d369763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47471 p hg
    simpa only [d369763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47473 (p : Pattern) (guard : d46053 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47171 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47474 (p : Pattern) (guard : d46054 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47473 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47475 (p : Pattern) (guard : d46055 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47474 p hg
    simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d46055, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47476 (p : Pattern) (guard : d179205 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46718 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47477 (p : Pattern) (guard : d369676 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47172 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47476 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47478 (p : Pattern) (guard : d369677 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47477 p hg
    simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d369677, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47479 (p : Pattern) (guard : d369678 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47475 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47478 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47480 (p : Pattern) (guard : d369679 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47479 p hg
    simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47481 (p : Pattern) (guard : d369680 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47480 p hg
    simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47482 (p : Pattern) (guard : d369681 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47481 p hg
    simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47483 (p : Pattern) (guard : d369682 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369681 p = 1 := by simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47482 p hg
    simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47484 (p : Pattern) (guard : d369683 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47179 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47187 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47485 (p : Pattern) (guard : d369684 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47484 p hg
    simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47486 (p : Pattern) (guard : d369685 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47485 p hg
    simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47487 (p : Pattern) (guard : d369686 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47486 p hg
    simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47488 (p : Pattern) (guard : d369687 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369686 p = 1 := by simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47487 p hg
    simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47489 (p : Pattern) (guard : d369688 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369682 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47483 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369687 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47488 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47490 (p : Pattern) (guard : d369689 p = 1) : d50606 p ≤ (1 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47172 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47491 (p : Pattern) (guard : d369690 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47490 p hg
    simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46721 p hg
    simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47492 (p : Pattern) (guard : d369691 p = 1) : d50642 p ≤ (1 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47491 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47187 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47493 (p : Pattern) (guard : d369692 p = 1) : d50657 p ≤ (1 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47492 p hg
    simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47494 (p : Pattern) (guard : d369693 p = 1) : d50658 p ≤ (1 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47493 p hg
    simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47495 (p : Pattern) (guard : d369694 p = 1) : d50659 p ≤ (1 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46710 p hg
    simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47494 p hg
    simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47496 (p : Pattern) (guard : d369695 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369694 p = 1 := by simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47495 p hg
    simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46729 p hg
    simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47497 (p : Pattern) (guard : d369696 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47496 p hg
    simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369515 p = 1 := by simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47192 p hg
    simpa only [d369696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47498 (p : Pattern) (guard : d369697 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47489 p hg
    simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369696 p = 1 := by simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47497 p hg
    simpa only [d369697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47499 (p : Pattern) (guard : d369698 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369697 p = 1 := by simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47498 p hg
    simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369517 p = 1 := by simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47194 p hg
    simpa only [d369698, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
