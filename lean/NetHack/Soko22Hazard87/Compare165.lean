import NetHack.Soko22Hazard87.Compare164
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41250 (p : Pattern) (guard : d348405 p = 1) : d50907 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41227 p hg
    simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41249 p hg
    simpa only [d348405, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41251 (p : Pattern) (guard : d0 p = 1) : d50910 p ≤ (1 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41252 (p : Pattern) (guard : d348406 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348405 p = 1 := by simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41250 p hg
    simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41251 p hg
    simpa only [d348406, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41253 (p : Pattern) (guard : d348407 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348406 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41252 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41254 (p : Pattern) (guard : d348408 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348407 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41253 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41255 (p : Pattern) (guard : d348409 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348406 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41252 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41256 (p : Pattern) (guard : d348410 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41255 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41257 (p : Pattern) (guard : d348411 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41254 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348410 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41256 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41258 (p : Pattern) (guard : d348412 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348411 p = 1 := by simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41257 p hg
    simpa only [d348412, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41259 (p : Pattern) (guard : d348413 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41258 p hg
    simpa only [d348413, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41260 (p : Pattern) (guard : d348414 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348410 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41256 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41261 (p : Pattern) (guard : d348415 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348414 p = 1 := by simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41260 p hg
    simpa only [d348415, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41262 (p : Pattern) (guard : d348416 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41261 p hg
    simpa only [d348416, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41263 (p : Pattern) (guard : d348417 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41259 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41262 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41264 (p : Pattern) (guard : d0 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41265 (p : Pattern) (guard : d348418 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41262 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41266 (p : Pattern) (guard : d348419 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41263 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41265 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41267 (p : Pattern) (guard : d348420 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41266 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41268 (p : Pattern) (guard : d0 p = 1) : d50931 p ≤ (1 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41269 (p : Pattern) (guard : d348421 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41267 p hg
    simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348421, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41270 (p : Pattern) (guard : d348422 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41269 p hg
    simpa only [d348422, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41271 (p : Pattern) (guard : d348423 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41265 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41272 (p : Pattern) (guard : d348424 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41271 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41273 (p : Pattern) (guard : d348425 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41272 p hg
    simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348425, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41274 (p : Pattern) (guard : d348426 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41273 p hg
    simpa only [d348426, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41275 (p : Pattern) (guard : d348427 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41270 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41274 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41276 (p : Pattern) (guard : d348428 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41275 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41277 (p : Pattern) (guard : d348429 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41276 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41278 (p : Pattern) (guard : d348430 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348429 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41277 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41279 (p : Pattern) (guard : d348431 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41274 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41280 (p : Pattern) (guard : d348432 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41279 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41281 (p : Pattern) (guard : d348433 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41280 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41282 (p : Pattern) (guard : d348434 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348433 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41281 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41283 (p : Pattern) (guard : d348435 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348430 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41278 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348434 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41282 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41284 (p : Pattern) (guard : d348436 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348435 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41283 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41285 (p : Pattern) (guard : d348437 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348436 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41284 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41286 (p : Pattern) (guard : d348438 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348437 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41285 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41287 (p : Pattern) (guard : d348439 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348438 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41286 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41288 (p : Pattern) (guard : d348440 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348439 p = 1 := by simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41287 p hg
    simpa only [d348440, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41289 (p : Pattern) (guard : d348441 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348440 p = 1 := by simpa only [d348441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41288 p hg
    simpa only [d348441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41290 (p : Pattern) (guard : d348442 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348441 p = 1 := by simpa only [d348442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41289 p hg
    simpa only [d348442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41291 (p : Pattern) (guard : d0 p = 1) : d50923 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41292 (p : Pattern) (guard : d0 p = 1) : d50929 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41293 (p : Pattern) (guard : d348413 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41258 p hg
    simpa only [d348413, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41294 (p : Pattern) (guard : d348416 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41261 p hg
    simpa only [d348416, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41295 (p : Pattern) (guard : d348417 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41293 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41294 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41296 (p : Pattern) (guard : d0 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41297 (p : Pattern) (guard : d348418 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41294 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41298 (p : Pattern) (guard : d348419 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41295 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41297 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41299 (p : Pattern) (guard : d348420 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41298 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41300 (p : Pattern) (guard : d348421 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41299 p hg
    simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348421, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41301 (p : Pattern) (guard : d348422 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41300 p hg
    simpa only [d348422, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41302 (p : Pattern) (guard : d348423 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41297 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41303 (p : Pattern) (guard : d348424 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41302 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41304 (p : Pattern) (guard : d348425 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41303 p hg
    simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348425, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41305 (p : Pattern) (guard : d348426 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41304 p hg
    simpa only [d348426, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41306 (p : Pattern) (guard : d348427 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41301 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41305 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41307 (p : Pattern) (guard : d348428 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41306 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41308 (p : Pattern) (guard : d348429 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41307 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41309 (p : Pattern) (guard : d348430 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348429 p = 1 := by simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41308 p hg
    simpa only [d348430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41310 (p : Pattern) (guard : d348431 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41305 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41311 (p : Pattern) (guard : d348432 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41310 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41312 (p : Pattern) (guard : d348433 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41311 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41313 (p : Pattern) (guard : d348434 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348433 p = 1 := by simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41312 p hg
    simpa only [d348434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41314 (p : Pattern) (guard : d348435 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348430 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41309 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348434 p = 1 := by simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41313 p hg
    simpa only [d348435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41315 (p : Pattern) (guard : d348436 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348435 p = 1 := by simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41314 p hg
    simpa only [d348436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41316 (p : Pattern) (guard : d348437 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348436 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41315 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41317 (p : Pattern) (guard : d348438 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348437 p = 1 := by simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41316 p hg
    simpa only [d348438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41318 (p : Pattern) (guard : d348439 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348438 p = 1 := by simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41317 p hg
    simpa only [d348439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41319 (p : Pattern) (guard : d348443 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348429 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41277 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41320 (p : Pattern) (guard : d348444 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348433 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41281 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41321 (p : Pattern) (guard : d348445 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348443 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41319 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348444 p = 1 := by simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41320 p hg
    simpa only [d348445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41322 (p : Pattern) (guard : d348446 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348445 p = 1 := by simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41321 p hg
    simpa only [d348446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41323 (p : Pattern) (guard : d348447 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348446 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41322 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41324 (p : Pattern) (guard : d348448 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348447 p = 1 := by simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41323 p hg
    simpa only [d348448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41325 (p : Pattern) (guard : d348449 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348448 p = 1 := by simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41324 p hg
    simpa only [d348449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41326 (p : Pattern) (guard : d348450 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348439 p = 1 := by simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41318 p hg
    simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348449 p = 1 := by simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41325 p hg
    simpa only [d348450, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41327 (p : Pattern) (guard : d348451 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348440 p = 1 := by simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41288 p hg
    simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348450 p = 1 := by simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41326 p hg
    simpa only [d348451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41328 (p : Pattern) (guard : d348452 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348451 p = 1 := by simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41327 p hg
    simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41329 (p : Pattern) (guard : d348453 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348442 p = 1 := by simpa only [d348453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41290 p hg
    simpa only [d348453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348452 p = 1 := by simpa only [d348453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41328 p hg
    simpa only [d348453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41330 (p : Pattern) (guard : d348454 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348428 p = 1 := by simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41276 p hg
    simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41331 (p : Pattern) (guard : d348455 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348454 p = 1 := by simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41330 p hg
    simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41332 (p : Pattern) (guard : d348456 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348432 p = 1 := by simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41280 p hg
    simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41333 (p : Pattern) (guard : d348457 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348456 p = 1 := by simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41332 p hg
    simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41334 (p : Pattern) (guard : d348458 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348455 p = 1 := by simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41331 p hg
    simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348457 p = 1 := by simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41333 p hg
    simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41335 (p : Pattern) (guard : d348459 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348458 p = 1 := by simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41334 p hg
    simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41336 (p : Pattern) (guard : d348460 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348459 p = 1 := by simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41335 p hg
    simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41337 (p : Pattern) (guard : d348461 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348460 p = 1 := by simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41336 p hg
    simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41338 (p : Pattern) (guard : d348462 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348427 p = 1 := by simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41275 p hg
    simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41339 (p : Pattern) (guard : d348463 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348462 p = 1 := by simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41338 p hg
    simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41340 (p : Pattern) (guard : d348464 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348463 p = 1 := by simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41339 p hg
    simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41341 (p : Pattern) (guard : d348465 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348431 p = 1 := by simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41279 p hg
    simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41342 (p : Pattern) (guard : d348466 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348465 p = 1 := by simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41341 p hg
    simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41343 (p : Pattern) (guard : d348467 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348466 p = 1 := by simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41342 p hg
    simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41344 (p : Pattern) (guard : d348468 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348464 p = 1 := by simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41340 p hg
    simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348467 p = 1 := by simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41343 p hg
    simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41345 (p : Pattern) (guard : d348469 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348468 p = 1 := by simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41344 p hg
    simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41346 (p : Pattern) (guard : d348470 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348469 p = 1 := by simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41345 p hg
    simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41347 (p : Pattern) (guard : d348471 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348408 p = 1 := by simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41254 p hg
    simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41348 (p : Pattern) (guard : d348472 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348472, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348472, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348471 p = 1 := by simpa only [d348472, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41347 p hg
    simpa only [d348472, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41349 (p : Pattern) (guard : d348473 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348473, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348473, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348472 p = 1 := by simpa only [d348473, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41348 p hg
    simpa only [d348473, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41350 (p : Pattern) (guard : d348474 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348407 p = 1 := by simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41253 p hg
    simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41255 p hg
    simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41351 (p : Pattern) (guard : d348475 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41254 p hg
    simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348474 p = 1 := by simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41350 p hg
    simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41352 (p : Pattern) (guard : d348476 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348476, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348476, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348475 p = 1 := by simpa only [d348476, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41351 p hg
    simpa only [d348476, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41353 (p : Pattern) (guard : d348477 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348477, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348477, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348476 p = 1 := by simpa only [d348477, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41352 p hg
    simpa only [d348477, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41354 (p : Pattern) (guard : d348478 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348473 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41349 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348477 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41353 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41355 (p : Pattern) (guard : d348479 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348478 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41354 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348417 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41263 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41356 (p : Pattern) (guard : d348480 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348479 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41355 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41357 (p : Pattern) (guard : d348481 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348480 p = 1 := by simpa only [d348481, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41356 p hg
    simpa only [d348481, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348481, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348481, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41358 (p : Pattern) (guard : d348482 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348482, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348482, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348481 p = 1 := by simpa only [d348482, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41357 p hg
    simpa only [d348482, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41359 (p : Pattern) (guard : d348483 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348482 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41358 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348422 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41270 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41360 (p : Pattern) (guard : d348484 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348483 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41359 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41361 (p : Pattern) (guard : d348485 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348484 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41360 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41362 (p : Pattern) (guard : d348486 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348485 p = 1 := by simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41361 p hg
    simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41363 (p : Pattern) (guard : d348487 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348486 p = 1 := by simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41362 p hg
    simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348430 p = 1 := by simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41278 p hg
    simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41364 (p : Pattern) (guard : d348488 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348487 p = 1 := by simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41363 p hg
    simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41365 (p : Pattern) (guard : d348489 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41270 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41366 (p : Pattern) (guard : d348490 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348489 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41365 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41367 (p : Pattern) (guard : d348491 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348490 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41366 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41368 (p : Pattern) (guard : d348492 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348491 p = 1 := by simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41367 p hg
    simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41369 (p : Pattern) (guard : d348493 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348492 p = 1 := by simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41368 p hg
    simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41370 (p : Pattern) (guard : d348494 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348493 p = 1 := by simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41369 p hg
    simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41371 (p : Pattern) (guard : d348495 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348488 p = 1 := by simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41364 p hg
    simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348494 p = 1 := by simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41370 p hg
    simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41372 (p : Pattern) (guard : d348496 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348470 p = 1 := by simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41346 p hg
    simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348495 p = 1 := by simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41371 p hg
    simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41373 (p : Pattern) (guard : d348497 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348461 p = 1 := by simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41337 p hg
    simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348496 p = 1 := by simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41372 p hg
    simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41374 (p : Pattern) (guard : d348498 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348498, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348498, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348497 p = 1 := by simpa only [d348498, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41373 p hg
    simpa only [d348498, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41375 (p : Pattern) (guard : d348454 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348428 p = 1 := by simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41307 p hg
    simpa only [d348454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41376 (p : Pattern) (guard : d348455 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348454 p = 1 := by simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41375 p hg
    simpa only [d348455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41377 (p : Pattern) (guard : d348456 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348432 p = 1 := by simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41311 p hg
    simpa only [d348456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41378 (p : Pattern) (guard : d348457 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348456 p = 1 := by simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41377 p hg
    simpa only [d348457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41379 (p : Pattern) (guard : d348458 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348455 p = 1 := by simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41376 p hg
    simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348457 p = 1 := by simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41378 p hg
    simpa only [d348458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41380 (p : Pattern) (guard : d348459 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348458 p = 1 := by simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41379 p hg
    simpa only [d348459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41381 (p : Pattern) (guard : d348460 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348459 p = 1 := by simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41380 p hg
    simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41382 (p : Pattern) (guard : d348461 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348460 p = 1 := by simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41381 p hg
    simpa only [d348461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41383 (p : Pattern) (guard : d348462 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348427 p = 1 := by simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41306 p hg
    simpa only [d348462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41384 (p : Pattern) (guard : d348463 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348462 p = 1 := by simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41383 p hg
    simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41385 (p : Pattern) (guard : d348464 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348463 p = 1 := by simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41384 p hg
    simpa only [d348464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41386 (p : Pattern) (guard : d348465 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348431 p = 1 := by simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41310 p hg
    simpa only [d348465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41387 (p : Pattern) (guard : d348466 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348465 p = 1 := by simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41386 p hg
    simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41388 (p : Pattern) (guard : d348467 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348466 p = 1 := by simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41387 p hg
    simpa only [d348467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41389 (p : Pattern) (guard : d348468 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348464 p = 1 := by simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41385 p hg
    simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348467 p = 1 := by simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d348468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41390 (p : Pattern) (guard : d348469 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348468 p = 1 := by simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41389 p hg
    simpa only [d348469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41391 (p : Pattern) (guard : d348470 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348469 p = 1 := by simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41390 p hg
    simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41392 (p : Pattern) (guard : d348473 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348473, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348473, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348472 p = 1 := by simpa only [d348473, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41348 p hg
    simpa only [d348473, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41393 (p : Pattern) (guard : d348477 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348477, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348477, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348476 p = 1 := by simpa only [d348477, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41352 p hg
    simpa only [d348477, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41394 (p : Pattern) (guard : d348478 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348473 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41392 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348477 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41393 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41395 (p : Pattern) (guard : d348479 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348478 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41394 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348417 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41295 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41396 (p : Pattern) (guard : d348480 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348479 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41395 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41397 (p : Pattern) (guard : d348481 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348480 p = 1 := by simpa only [d348481, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41396 p hg
    simpa only [d348481, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348481, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348481, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41398 (p : Pattern) (guard : d348482 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348482, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348482, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348481 p = 1 := by simpa only [d348482, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41397 p hg
    simpa only [d348482, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41399 (p : Pattern) (guard : d348483 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348482 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41398 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348422 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41301 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41400 (p : Pattern) (guard : d348484 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348483 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41399 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41401 (p : Pattern) (guard : d348485 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348484 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41402 (p : Pattern) (guard : d348486 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348485 p = 1 := by simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41401 p hg
    simpa only [d348486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41403 (p : Pattern) (guard : d348487 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348486 p = 1 := by simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41402 p hg
    simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348430 p = 1 := by simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41309 p hg
    simpa only [d348487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41404 (p : Pattern) (guard : d348488 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348487 p = 1 := by simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41403 p hg
    simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41405 (p : Pattern) (guard : d348489 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41301 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41406 (p : Pattern) (guard : d348490 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348489 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41405 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41407 (p : Pattern) (guard : d348491 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348490 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41406 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41408 (p : Pattern) (guard : d348492 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348491 p = 1 := by simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41407 p hg
    simpa only [d348492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41409 (p : Pattern) (guard : d348493 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348492 p = 1 := by simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41408 p hg
    simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41410 (p : Pattern) (guard : d348494 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348493 p = 1 := by simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41409 p hg
    simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41411 (p : Pattern) (guard : d348495 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348488 p = 1 := by simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41404 p hg
    simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348494 p = 1 := by simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41410 p hg
    simpa only [d348495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41412 (p : Pattern) (guard : d348496 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348470 p = 1 := by simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41391 p hg
    simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348495 p = 1 := by simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41411 p hg
    simpa only [d348496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41413 (p : Pattern) (guard : d348497 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348461 p = 1 := by simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41382 p hg
    simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348496 p = 1 := by simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d348497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41414 (p : Pattern) (guard : d348499 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348454 p = 1 := by simpa only [d348499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41330 p hg
    simpa only [d348499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41415 (p : Pattern) (guard : d348500 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348456 p = 1 := by simpa only [d348500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41332 p hg
    simpa only [d348500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41416 (p : Pattern) (guard : d348501 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348499 p = 1 := by simpa only [d348501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41414 p hg
    simpa only [d348501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348500 p = 1 := by simpa only [d348501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41415 p hg
    simpa only [d348501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41417 (p : Pattern) (guard : d348502 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348501 p = 1 := by simpa only [d348502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41416 p hg
    simpa only [d348502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41418 (p : Pattern) (guard : d348503 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348502 p = 1 := by simpa only [d348503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41417 p hg
    simpa only [d348503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41419 (p : Pattern) (guard : d348504 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348503 p = 1 := by simpa only [d348504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41418 p hg
    simpa only [d348504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41420 (p : Pattern) (guard : d348505 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348463 p = 1 := by simpa only [d348505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41339 p hg
    simpa only [d348505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41421 (p : Pattern) (guard : d348506 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348466 p = 1 := by simpa only [d348506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41342 p hg
    simpa only [d348506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41422 (p : Pattern) (guard : d348507 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348505 p = 1 := by simpa only [d348507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41420 p hg
    simpa only [d348507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348506 p = 1 := by simpa only [d348507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41421 p hg
    simpa only [d348507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41423 (p : Pattern) (guard : d348508 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348507 p = 1 := by simpa only [d348508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41422 p hg
    simpa only [d348508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41424 (p : Pattern) (guard : d348509 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348508 p = 1 := by simpa only [d348509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41423 p hg
    simpa only [d348509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41425 (p : Pattern) (guard : d348510 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348485 p = 1 := by simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41361 p hg
    simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41426 (p : Pattern) (guard : d348511 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348510 p = 1 := by simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41425 p hg
    simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348443 p = 1 := by simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41319 p hg
    simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41427 (p : Pattern) (guard : d348512 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348511 p = 1 := by simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41426 p hg
    simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41428 (p : Pattern) (guard : d348513 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348491 p = 1 := by simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41367 p hg
    simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41429 (p : Pattern) (guard : d348514 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348513 p = 1 := by simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41428 p hg
    simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41430 (p : Pattern) (guard : d348515 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348514 p = 1 := by simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41429 p hg
    simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41431 (p : Pattern) (guard : d348516 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348512 p = 1 := by simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41427 p hg
    simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348515 p = 1 := by simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41430 p hg
    simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41432 (p : Pattern) (guard : d348517 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d348509 p = 1 := by simpa only [d348517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41424 p hg
    simpa only [d348517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348516 p = 1 := by simpa only [d348517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41431 p hg
    simpa only [d348517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41433 (p : Pattern) (guard : d348518 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d348504 p = 1 := by simpa only [d348518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41419 p hg
    simpa only [d348518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348517 p = 1 := by simpa only [d348518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41432 p hg
    simpa only [d348518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41434 (p : Pattern) (guard : d348519 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348497 p = 1 := by simpa only [d348519, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41413 p hg
    simpa only [d348519, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348518 p = 1 := by simpa only [d348519, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41433 p hg
    simpa only [d348519, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41435 (p : Pattern) (guard : d348520 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348498 p = 1 := by simpa only [d348520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41374 p hg
    simpa only [d348520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348519 p = 1 := by simpa only [d348520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41434 p hg
    simpa only [d348520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41436 (p : Pattern) (guard : d348521 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348434 p = 1 := by simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41282 p hg
    simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41437 (p : Pattern) (guard : d348522 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348521 p = 1 := by simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41436 p hg
    simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41438 (p : Pattern) (guard : d348523 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348522 p = 1 := by simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41437 p hg
    simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41439 (p : Pattern) (guard : d348524 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348523 p = 1 := by simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41438 p hg
    simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41440 (p : Pattern) (guard : d348525 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348524 p = 1 := by simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41439 p hg
    simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41441 (p : Pattern) (guard : d348526 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348439 p = 1 := by simpa only [d348526, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41318 p hg
    simpa only [d348526, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348525 p = 1 := by simpa only [d348526, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41440 p hg
    simpa only [d348526, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41442 (p : Pattern) (guard : d348521 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348434 p = 1 := by simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41313 p hg
    simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41443 (p : Pattern) (guard : d348522 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348521 p = 1 := by simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41442 p hg
    simpa only [d348522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41444 (p : Pattern) (guard : d348523 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348522 p = 1 := by simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41443 p hg
    simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41445 (p : Pattern) (guard : d348524 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348523 p = 1 := by simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d348524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41446 (p : Pattern) (guard : d348525 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348524 p = 1 := by simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41445 p hg
    simpa only [d348525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41447 (p : Pattern) (guard : d348527 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348444 p = 1 := by simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41320 p hg
    simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41448 (p : Pattern) (guard : d348528 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348527 p = 1 := by simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41447 p hg
    simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41449 (p : Pattern) (guard : d348529 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348528 p = 1 := by simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41448 p hg
    simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41450 (p : Pattern) (guard : d348530 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348529 p = 1 := by simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41449 p hg
    simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41451 (p : Pattern) (guard : d348531 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348530 p = 1 := by simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41450 p hg
    simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41452 (p : Pattern) (guard : d348532 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348525 p = 1 := by simpa only [d348532, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41446 p hg
    simpa only [d348532, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348531 p = 1 := by simpa only [d348532, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41451 p hg
    simpa only [d348532, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41453 (p : Pattern) (guard : d348533 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348526 p = 1 := by simpa only [d348533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41441 p hg
    simpa only [d348533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348532 p = 1 := by simpa only [d348533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41452 p hg
    simpa only [d348533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41454 (p : Pattern) (guard : d348534 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348520 p = 1 := by simpa only [d348534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41435 p hg
    simpa only [d348534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348533 p = 1 := by simpa only [d348534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d348534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41455 (p : Pattern) (guard : d348535 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348534 p = 1 := by simpa only [d348535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d348535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41456 (p : Pattern) (guard : d348536 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348453 p = 1 := by simpa only [d348536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41329 p hg
    simpa only [d348536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348535 p = 1 := by simpa only [d348536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41455 p hg
    simpa only [d348536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41457 (p : Pattern) (guard : d0 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41458 (p : Pattern) (guard : d0 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41459 (p : Pattern) (guard : d0 p = 1) : d51030 p ≤ (1 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41460 (p : Pattern) (guard : d0 p = 1) : d51033 p ≤ (1 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41461 (p : Pattern) (guard : d0 p = 1) : d51015 p ≤ (1 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41462 (p : Pattern) (guard : d0 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41463 (p : Pattern) (guard : d0 p = 1) : d51017 p ≤ (1 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41464 (p : Pattern) (guard : d0 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41465 (p : Pattern) (guard : d14 p = 1) : d5 p ≤ (1 : Int) + d5 p := by
  omega
theorem compare41466 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41467 (p : Pattern) (guard : d15 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41465 p hg
    simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41466 p hg
    simpa only [d15, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41468 (p : Pattern) (guard : d16 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41467 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41469 (p : Pattern) (guard : d17 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41468 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41470 (p : Pattern) (guard : d38813 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41469 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41471 (p : Pattern) (guard : d258091 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41470 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41472 (p : Pattern) (guard : d337158 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41471 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41473 (p : Pattern) (guard : d337173 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41472 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41474 (p : Pattern) (guard : d257183 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41470 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41475 (p : Pattern) (guard : d257184 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41474 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41476 (p : Pattern) (guard : d257185 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41475 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41477 (p : Pattern) (guard : d348400 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41473 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41476 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41478 (p : Pattern) (guard : d0 p = 1) : d50966 p ≤ (1 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41479 (p : Pattern) (guard : d348401 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41477 p hg
    simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41478 p hg
    simpa only [d348401, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41480 (p : Pattern) (guard : d0 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41481 (p : Pattern) (guard : d348402 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41479 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41480 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41482 (p : Pattern) (guard : d0 p = 1) : d50882 p ≤ (1 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41483 (p : Pattern) (guard : d348403 p = 1) : d50997 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41481 p hg
    simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348403, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41484 (p : Pattern) (guard : d348404 p = 1) : d50998 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41483 p hg
    simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348404, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41485 (p : Pattern) (guard : d348405 p = 1) : d51018 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41463 p hg
    simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41484 p hg
    simpa only [d348405, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41486 (p : Pattern) (guard : d0 p = 1) : d51021 p ≤ (1 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41487 (p : Pattern) (guard : d348406 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348405 p = 1 := by simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41485 p hg
    simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41486 p hg
    simpa only [d348406, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41488 (p : Pattern) (guard : d348407 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348406 p = 1 := by simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41487 p hg
    simpa only [d348407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41489 (p : Pattern) (guard : d348408 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348407 p = 1 := by simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41488 p hg
    simpa only [d348408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41490 (p : Pattern) (guard : d348471 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348408 p = 1 := by simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41489 p hg
    simpa only [d348471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41491 (p : Pattern) (guard : d348472 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348472, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348472, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348471 p = 1 := by simpa only [d348472, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41490 p hg
    simpa only [d348472, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41492 (p : Pattern) (guard : d348473 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348473, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348473, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348472 p = 1 := by simpa only [d348473, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41491 p hg
    simpa only [d348473, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41493 (p : Pattern) (guard : d348409 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348406 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41487 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41494 (p : Pattern) (guard : d348474 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348407 p = 1 := by simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41488 p hg
    simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41493 p hg
    simpa only [d348474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41495 (p : Pattern) (guard : d348475 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41489 p hg
    simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348474 p = 1 := by simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41494 p hg
    simpa only [d348475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41496 (p : Pattern) (guard : d348476 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348476, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348476, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348475 p = 1 := by simpa only [d348476, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41495 p hg
    simpa only [d348476, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41497 (p : Pattern) (guard : d348477 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348477, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348477, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348476 p = 1 := by simpa only [d348477, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41496 p hg
    simpa only [d348477, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41498 (p : Pattern) (guard : d348478 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348473 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348477 p = 1 := by simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41497 p hg
    simpa only [d348478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41499 (p : Pattern) (guard : d348410 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348409 p = 1 := by simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41493 p hg
    simpa only [d348410, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
