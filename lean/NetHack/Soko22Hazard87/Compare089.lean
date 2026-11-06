import NetHack.Soko22Hazard87.Compare088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22250 (p : Pattern) (guard : d179565 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179564 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22249 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179495 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22161 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22251 (p : Pattern) (guard : d179566 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179565 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22250 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22252 (p : Pattern) (guard : d179567 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179566 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22251 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22253 (p : Pattern) (guard : d179568 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179567 p = 1 := by simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22252 p hg
    simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22254 (p : Pattern) (guard : d179569 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179568 p = 1 := by simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22253 p hg
    simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179503 p = 1 := by simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22169 p hg
    simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22255 (p : Pattern) (guard : d179570 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179569 p = 1 := by simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22254 p hg
    simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22256 (p : Pattern) (guard : d179571 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22161 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22257 (p : Pattern) (guard : d179572 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179571 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22256 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22258 (p : Pattern) (guard : d179573 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179572 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22257 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22259 (p : Pattern) (guard : d179574 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179573 p = 1 := by simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22258 p hg
    simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22260 (p : Pattern) (guard : d179575 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179574 p = 1 := by simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22259 p hg
    simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22261 (p : Pattern) (guard : d179576 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179575 p = 1 := by simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22260 p hg
    simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22262 (p : Pattern) (guard : d179577 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179570 p = 1 := by simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22255 p hg
    simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179576 p = 1 := by simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22261 p hg
    simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22263 (p : Pattern) (guard : d179578 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179543 p = 1 := by simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22234 p hg
    simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179577 p = 1 := by simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22262 p hg
    simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22264 (p : Pattern) (guard : d179579 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179534 p = 1 := by simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22225 p hg
    simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179578 p = 1 := by simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22263 p hg
    simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22265 (p : Pattern) (guard : d179580 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179580, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179580, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179579 p = 1 := by simpa only [d179580, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22264 p hg
    simpa only [d179580, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22266 (p : Pattern) (guard : d179527 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179501 p = 1 := by simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22195 p hg
    simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22267 (p : Pattern) (guard : d179528 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179527 p = 1 := by simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22266 p hg
    simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22268 (p : Pattern) (guard : d179529 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179505 p = 1 := by simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22269 (p : Pattern) (guard : d179530 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179529 p = 1 := by simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22268 p hg
    simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22270 (p : Pattern) (guard : d179531 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179528 p = 1 := by simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22267 p hg
    simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179530 p = 1 := by simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22269 p hg
    simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22271 (p : Pattern) (guard : d179532 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179531 p = 1 := by simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22270 p hg
    simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22272 (p : Pattern) (guard : d179533 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179532 p = 1 := by simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22271 p hg
    simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22273 (p : Pattern) (guard : d179534 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179533 p = 1 := by simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22272 p hg
    simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22274 (p : Pattern) (guard : d179535 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179500 p = 1 := by simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22194 p hg
    simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22275 (p : Pattern) (guard : d179536 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179535 p = 1 := by simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22274 p hg
    simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22276 (p : Pattern) (guard : d179537 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179536 p = 1 := by simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22275 p hg
    simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22277 (p : Pattern) (guard : d179538 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179504 p = 1 := by simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22278 (p : Pattern) (guard : d179539 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179538 p = 1 := by simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22277 p hg
    simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22279 (p : Pattern) (guard : d179540 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179539 p = 1 := by simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22278 p hg
    simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22280 (p : Pattern) (guard : d179541 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179537 p = 1 := by simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22276 p hg
    simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179540 p = 1 := by simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22279 p hg
    simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22281 (p : Pattern) (guard : d179542 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179541 p = 1 := by simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22280 p hg
    simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22282 (p : Pattern) (guard : d179543 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179542 p = 1 := by simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22281 p hg
    simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22283 (p : Pattern) (guard : d179556 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179556, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179556, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179555 p = 1 := by simpa only [d179556, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22240 p hg
    simpa only [d179556, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22284 (p : Pattern) (guard : d179559 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179559, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179559, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179558 p = 1 := by simpa only [d179559, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22243 p hg
    simpa only [d179559, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22285 (p : Pattern) (guard : d179560 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179556 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22283 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179559 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22284 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22286 (p : Pattern) (guard : d179561 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179560 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22285 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179490 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22184 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22287 (p : Pattern) (guard : d179562 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179561 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22286 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22288 (p : Pattern) (guard : d179563 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179562 p = 1 := by simpa only [d179563, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22287 p hg
    simpa only [d179563, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179563, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179563, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22289 (p : Pattern) (guard : d179564 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179564, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179564, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179563 p = 1 := by simpa only [d179564, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22288 p hg
    simpa only [d179564, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22290 (p : Pattern) (guard : d179565 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179564 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22289 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179495 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22189 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22291 (p : Pattern) (guard : d179566 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179565 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22290 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22292 (p : Pattern) (guard : d179567 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179566 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22291 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22293 (p : Pattern) (guard : d179568 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179567 p = 1 := by simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22292 p hg
    simpa only [d179568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22294 (p : Pattern) (guard : d179569 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179568 p = 1 := by simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22293 p hg
    simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179503 p = 1 := by simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22197 p hg
    simpa only [d179569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22295 (p : Pattern) (guard : d179570 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179569 p = 1 := by simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22294 p hg
    simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22296 (p : Pattern) (guard : d179571 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22189 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22297 (p : Pattern) (guard : d179572 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179571 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22296 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22298 (p : Pattern) (guard : d179573 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179572 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22297 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22299 (p : Pattern) (guard : d179574 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179573 p = 1 := by simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22298 p hg
    simpa only [d179574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22300 (p : Pattern) (guard : d179575 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179574 p = 1 := by simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22299 p hg
    simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22301 (p : Pattern) (guard : d179576 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179575 p = 1 := by simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22300 p hg
    simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22302 (p : Pattern) (guard : d179577 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179570 p = 1 := by simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22295 p hg
    simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179576 p = 1 := by simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22301 p hg
    simpa only [d179577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22303 (p : Pattern) (guard : d179578 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179543 p = 1 := by simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22282 p hg
    simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179577 p = 1 := by simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22302 p hg
    simpa only [d179578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22304 (p : Pattern) (guard : d179579 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179534 p = 1 := by simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22273 p hg
    simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179578 p = 1 := by simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22303 p hg
    simpa only [d179579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22305 (p : Pattern) (guard : d179581 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179527 p = 1 := by simpa only [d179581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22218 p hg
    simpa only [d179581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22306 (p : Pattern) (guard : d179582 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179529 p = 1 := by simpa only [d179582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22220 p hg
    simpa only [d179582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22307 (p : Pattern) (guard : d179583 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179581 p = 1 := by simpa only [d179583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22305 p hg
    simpa only [d179583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179582 p = 1 := by simpa only [d179583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22306 p hg
    simpa only [d179583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22308 (p : Pattern) (guard : d179584 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179583 p = 1 := by simpa only [d179584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22307 p hg
    simpa only [d179584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22309 (p : Pattern) (guard : d179585 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179584 p = 1 := by simpa only [d179585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22308 p hg
    simpa only [d179585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22310 (p : Pattern) (guard : d179586 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179585 p = 1 := by simpa only [d179586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22309 p hg
    simpa only [d179586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22311 (p : Pattern) (guard : d179587 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179536 p = 1 := by simpa only [d179587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22227 p hg
    simpa only [d179587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22312 (p : Pattern) (guard : d179588 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179539 p = 1 := by simpa only [d179588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22230 p hg
    simpa only [d179588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22313 (p : Pattern) (guard : d179589 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179587 p = 1 := by simpa only [d179589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22311 p hg
    simpa only [d179589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179588 p = 1 := by simpa only [d179589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22312 p hg
    simpa only [d179589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22314 (p : Pattern) (guard : d179590 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179589 p = 1 := by simpa only [d179590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22313 p hg
    simpa only [d179590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22315 (p : Pattern) (guard : d179591 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179590 p = 1 := by simpa only [d179591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22314 p hg
    simpa only [d179591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22316 (p : Pattern) (guard : d179592 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179567 p = 1 := by simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22252 p hg
    simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22317 (p : Pattern) (guard : d179593 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179592 p = 1 := by simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22316 p hg
    simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179516 p = 1 := by simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22207 p hg
    simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22318 (p : Pattern) (guard : d179594 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179593 p = 1 := by simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22317 p hg
    simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22319 (p : Pattern) (guard : d179595 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179573 p = 1 := by simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22258 p hg
    simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22320 (p : Pattern) (guard : d179596 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179595 p = 1 := by simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22319 p hg
    simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22321 (p : Pattern) (guard : d179597 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179596 p = 1 := by simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22320 p hg
    simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22322 (p : Pattern) (guard : d179598 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179594 p = 1 := by simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22318 p hg
    simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179597 p = 1 := by simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22321 p hg
    simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22323 (p : Pattern) (guard : d179599 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179591 p = 1 := by simpa only [d179599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22315 p hg
    simpa only [d179599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179598 p = 1 := by simpa only [d179599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22322 p hg
    simpa only [d179599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22324 (p : Pattern) (guard : d179600 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179586 p = 1 := by simpa only [d179600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22310 p hg
    simpa only [d179600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179599 p = 1 := by simpa only [d179600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22323 p hg
    simpa only [d179600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22325 (p : Pattern) (guard : d179601 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179579 p = 1 := by simpa only [d179601, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22304 p hg
    simpa only [d179601, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179600 p = 1 := by simpa only [d179601, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22324 p hg
    simpa only [d179601, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22326 (p : Pattern) (guard : d179602 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179580 p = 1 := by simpa only [d179602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22265 p hg
    simpa only [d179602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179601 p = 1 := by simpa only [d179602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22325 p hg
    simpa only [d179602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22327 (p : Pattern) (guard : d179603 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179507 p = 1 := by simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22173 p hg
    simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22328 (p : Pattern) (guard : d179604 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179603 p = 1 := by simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22327 p hg
    simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22329 (p : Pattern) (guard : d179605 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179604 p = 1 := by simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22328 p hg
    simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22330 (p : Pattern) (guard : d179606 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179605 p = 1 := by simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22329 p hg
    simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22331 (p : Pattern) (guard : d179607 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179606 p = 1 := by simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22330 p hg
    simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22332 (p : Pattern) (guard : d179608 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179512 p = 1 := by simpa only [d179608, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22206 p hg
    simpa only [d179608, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179607 p = 1 := by simpa only [d179608, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22331 p hg
    simpa only [d179608, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22333 (p : Pattern) (guard : d179603 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179507 p = 1 := by simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22201 p hg
    simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22334 (p : Pattern) (guard : d179604 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179603 p = 1 := by simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22333 p hg
    simpa only [d179604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22335 (p : Pattern) (guard : d179605 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179604 p = 1 := by simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22334 p hg
    simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22336 (p : Pattern) (guard : d179606 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179605 p = 1 := by simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22335 p hg
    simpa only [d179606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22337 (p : Pattern) (guard : d179607 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179606 p = 1 := by simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22336 p hg
    simpa only [d179607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22338 (p : Pattern) (guard : d179609 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179517 p = 1 := by simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22208 p hg
    simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22339 (p : Pattern) (guard : d179610 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179609 p = 1 := by simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22338 p hg
    simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22340 (p : Pattern) (guard : d179611 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179610 p = 1 := by simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22339 p hg
    simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22341 (p : Pattern) (guard : d179612 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179611 p = 1 := by simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22340 p hg
    simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22342 (p : Pattern) (guard : d179613 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179612 p = 1 := by simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22341 p hg
    simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22343 (p : Pattern) (guard : d179614 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179607 p = 1 := by simpa only [d179614, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22337 p hg
    simpa only [d179614, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179613 p = 1 := by simpa only [d179614, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22342 p hg
    simpa only [d179614, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22344 (p : Pattern) (guard : d179615 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179608 p = 1 := by simpa only [d179615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22332 p hg
    simpa only [d179615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179614 p = 1 := by simpa only [d179615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22343 p hg
    simpa only [d179615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22345 (p : Pattern) (guard : d179616 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179602 p = 1 := by simpa only [d179616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22326 p hg
    simpa only [d179616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179615 p = 1 := by simpa only [d179616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22344 p hg
    simpa only [d179616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22346 (p : Pattern) (guard : d179617 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179616 p = 1 := by simpa only [d179617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22345 p hg
    simpa only [d179617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22347 (p : Pattern) (guard : d179618 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179526 p = 1 := by simpa only [d179618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d179618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179617 p = 1 := by simpa only [d179618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22346 p hg
    simpa only [d179618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22348 (p : Pattern) (guard : d179550 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22349 (p : Pattern) (guard : d179551 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179550 p = 1 := by simpa only [d179551, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22348 p hg
    simpa only [d179551, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179551, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179551, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22350 (p : Pattern) (guard : d179552 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179551 p = 1 := by simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22349 p hg
    simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22351 (p : Pattern) (guard : d179553 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179552 p = 1 := by simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22350 p hg
    simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22352 (p : Pattern) (guard : d179468 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22353 (p : Pattern) (guard : d179469 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179468 p = 1 := by simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22352 p hg
    simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22354 (p : Pattern) (guard : d179470 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179469 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22353 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22355 (p : Pattern) (guard : d179471 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179470 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22354 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22356 (p : Pattern) (guard : d179554 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179553 p = 1 := by simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22351 p hg
    simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179471 p = 1 := by simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22357 (p : Pattern) (guard : d179555 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179555, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179555, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179554 p = 1 := by simpa only [d179555, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22356 p hg
    simpa only [d179555, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22358 (p : Pattern) (guard : d179556 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179556, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179556, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179555 p = 1 := by simpa only [d179556, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22357 p hg
    simpa only [d179556, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22359 (p : Pattern) (guard : d179557 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22360 (p : Pattern) (guard : d179558 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179558, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179558, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179557 p = 1 := by simpa only [d179558, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22359 p hg
    simpa only [d179558, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22361 (p : Pattern) (guard : d179559 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179559, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179559, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179558 p = 1 := by simpa only [d179559, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22360 p hg
    simpa only [d179559, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22362 (p : Pattern) (guard : d179560 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179556 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22358 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179559 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22361 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22363 (p : Pattern) (guard : d179480 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22364 (p : Pattern) (guard : d179481 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179480 p = 1 := by simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22363 p hg
    simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22365 (p : Pattern) (guard : d179482 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179481 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22364 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22366 (p : Pattern) (guard : d179483 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179482 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22365 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22367 (p : Pattern) (guard : d179484 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179483 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22366 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22368 (p : Pattern) (guard : d179485 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179484 p = 1 := by simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22367 p hg
    simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22369 (p : Pattern) (guard : d179486 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22368 p hg
    simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22370 (p : Pattern) (guard : d179487 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179483 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22366 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22371 (p : Pattern) (guard : d179488 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179487 p = 1 := by simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22370 p hg
    simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22372 (p : Pattern) (guard : d179489 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22371 p hg
    simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22373 (p : Pattern) (guard : d179490 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22369 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22372 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22374 (p : Pattern) (guard : d179561 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179560 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22362 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179490 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22373 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22375 (p : Pattern) (guard : d179562 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179561 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22374 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22376 (p : Pattern) (guard : d179563 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179562 p = 1 := by simpa only [d179563, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22375 p hg
    simpa only [d179563, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179563, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179563, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22377 (p : Pattern) (guard : d179564 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179564, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179564, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179563 p = 1 := by simpa only [d179564, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22376 p hg
    simpa only [d179564, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22378 (p : Pattern) (guard : d179491 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22372 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22379 (p : Pattern) (guard : d179492 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22373 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22378 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22380 (p : Pattern) (guard : d179493 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22379 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22381 (p : Pattern) (guard : d179494 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22380 p hg
    simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22382 (p : Pattern) (guard : d179495 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22381 p hg
    simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22383 (p : Pattern) (guard : d179565 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179564 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22377 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179495 p = 1 := by simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22382 p hg
    simpa only [d179565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22384 (p : Pattern) (guard : d179566 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179565 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22383 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22385 (p : Pattern) (guard : d179567 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179566 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22384 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22386 (p : Pattern) (guard : d179592 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179567 p = 1 := by simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22385 p hg
    simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22387 (p : Pattern) (guard : d179496 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22378 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22388 (p : Pattern) (guard : d179497 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22387 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22389 (p : Pattern) (guard : d179498 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22388 p hg
    simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22390 (p : Pattern) (guard : d179499 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22389 p hg
    simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22391 (p : Pattern) (guard : d179500 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22382 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22390 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22392 (p : Pattern) (guard : d179501 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22393 (p : Pattern) (guard : d179502 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22392 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22394 (p : Pattern) (guard : d179516 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179502 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22395 (p : Pattern) (guard : d179593 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179592 p = 1 := by simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22386 p hg
    simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179516 p = 1 := by simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22394 p hg
    simpa only [d179593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22396 (p : Pattern) (guard : d179594 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179593 p = 1 := by simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22395 p hg
    simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22397 (p : Pattern) (guard : d179571 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22382 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22398 (p : Pattern) (guard : d179572 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179571 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22397 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22399 (p : Pattern) (guard : d179573 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179572 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22400 (p : Pattern) (guard : d179595 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179573 p = 1 := by simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22399 p hg
    simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22401 (p : Pattern) (guard : d179596 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179595 p = 1 := by simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22400 p hg
    simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22402 (p : Pattern) (guard : d179597 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179596 p = 1 := by simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22401 p hg
    simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22403 (p : Pattern) (guard : d179598 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179594 p = 1 := by simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22396 p hg
    simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179597 p = 1 := by simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22402 p hg
    simpa only [d179598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22404 (p : Pattern) (guard : d179619 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179598 p = 1 := by simpa only [d179619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22403 p hg
    simpa only [d179619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22405 (p : Pattern) (guard : d179620 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179619 p = 1 := by simpa only [d179620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22404 p hg
    simpa only [d179620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22406 (p : Pattern) (guard : d179621 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179621, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179621, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179620 p = 1 := by simpa only [d179621, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22405 p hg
    simpa only [d179621, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22407 (p : Pattern) (guard : d179622 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179621 p = 1 := by simpa only [d179622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22406 p hg
    simpa only [d179622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22408 (p : Pattern) (guard : d179504 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22390 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22409 (p : Pattern) (guard : d179505 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22408 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22410 (p : Pattern) (guard : d179506 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22409 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22411 (p : Pattern) (guard : d179517 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179506 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22410 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22412 (p : Pattern) (guard : d179609 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179517 p = 1 := by simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22411 p hg
    simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22413 (p : Pattern) (guard : d179610 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179609 p = 1 := by simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22412 p hg
    simpa only [d179610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22414 (p : Pattern) (guard : d179611 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179610 p = 1 := by simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22413 p hg
    simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22415 (p : Pattern) (guard : d179612 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179611 p = 1 := by simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22414 p hg
    simpa only [d179612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22416 (p : Pattern) (guard : d179613 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179612 p = 1 := by simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22415 p hg
    simpa only [d179613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22417 (p : Pattern) (guard : d179623 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179623, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179623, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179613 p = 1 := by simpa only [d179623, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22416 p hg
    simpa only [d179623, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22418 (p : Pattern) (guard : d179624 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179623 p = 1 := by simpa only [d179624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22417 p hg
    simpa only [d179624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22419 (p : Pattern) (guard : d179625 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179622 p = 1 := by simpa only [d179625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22407 p hg
    simpa only [d179625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179624 p = 1 := by simpa only [d179625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22418 p hg
    simpa only [d179625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22420 (p : Pattern) (guard : d179626 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179625 p = 1 := by simpa only [d179626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22419 p hg
    simpa only [d179626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22421 (p : Pattern) (guard : d179627 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179626 p = 1 := by simpa only [d179627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22420 p hg
    simpa only [d179627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22422 (p : Pattern) (guard : d179628 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179618 p = 1 := by simpa only [d179628, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22347 p hg
    simpa only [d179628, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179627 p = 1 := by simpa only [d179628, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22421 p hg
    simpa only [d179628, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22423 (p : Pattern) (guard : d179631 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22424 (p : Pattern) (guard : d179632 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179631 p = 1 := by simpa only [d179632, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22423 p hg
    simpa only [d179632, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179632, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179632, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22425 (p : Pattern) (guard : d179633 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179632 p = 1 := by simpa only [d179633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22424 p hg
    simpa only [d179633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22426 (p : Pattern) (guard : d179634 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179633 p = 1 := by simpa only [d179634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22425 p hg
    simpa only [d179634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22427 (p : Pattern) (guard : d179637 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22428 (p : Pattern) (guard : d179638 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179637 p = 1 := by simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22427 p hg
    simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22429 (p : Pattern) (guard : d179639 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179638 p = 1 := by simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22428 p hg
    simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22430 (p : Pattern) (guard : d179640 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179639 p = 1 := by simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22429 p hg
    simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22431 (p : Pattern) (guard : d179641 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179634 p = 1 := by simpa only [d179641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22426 p hg
    simpa only [d179641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179640 p = 1 := by simpa only [d179641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22430 p hg
    simpa only [d179641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22432 (p : Pattern) (guard : d179642 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179642, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179642, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179641 p = 1 := by simpa only [d179642, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22431 p hg
    simpa only [d179642, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22433 (p : Pattern) (guard : d179643 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179643, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179643, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179642 p = 1 := by simpa only [d179643, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22432 p hg
    simpa only [d179643, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22434 (p : Pattern) (guard : d179644 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179640 p = 1 := by simpa only [d179644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22430 p hg
    simpa only [d179644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22435 (p : Pattern) (guard : d179645 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179645, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179645, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179644 p = 1 := by simpa only [d179645, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22434 p hg
    simpa only [d179645, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22436 (p : Pattern) (guard : d179646 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179646, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179646, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179645 p = 1 := by simpa only [d179646, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22435 p hg
    simpa only [d179646, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22437 (p : Pattern) (guard : d179647 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179643 p = 1 := by simpa only [d179647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22433 p hg
    simpa only [d179647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179646 p = 1 := by simpa only [d179647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22436 p hg
    simpa only [d179647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22438 (p : Pattern) (guard : d179650 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22439 (p : Pattern) (guard : d179651 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179650 p = 1 := by simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22438 p hg
    simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22440 (p : Pattern) (guard : d179652 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179651 p = 1 := by simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22439 p hg
    simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22441 (p : Pattern) (guard : d179653 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179652 p = 1 := by simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22440 p hg
    simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22442 (p : Pattern) (guard : d179654 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179640 p = 1 := by simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22430 p hg
    simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179653 p = 1 := by simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22441 p hg
    simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22443 (p : Pattern) (guard : d179655 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179654 p = 1 := by simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22442 p hg
    simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22444 (p : Pattern) (guard : d179656 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179655 p = 1 := by simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22443 p hg
    simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22445 (p : Pattern) (guard : d179657 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179653 p = 1 := by simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22441 p hg
    simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22446 (p : Pattern) (guard : d179658 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179657 p = 1 := by simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22445 p hg
    simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22447 (p : Pattern) (guard : d179659 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179658 p = 1 := by simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22446 p hg
    simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22448 (p : Pattern) (guard : d179660 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179656 p = 1 := by simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22444 p hg
    simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179659 p = 1 := by simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22447 p hg
    simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22449 (p : Pattern) (guard : d179661 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179647 p = 1 := by simpa only [d179661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22437 p hg
    simpa only [d179661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179660 p = 1 := by simpa only [d179661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22448 p hg
    simpa only [d179661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22450 (p : Pattern) (guard : d179662 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179661 p = 1 := by simpa only [d179662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22449 p hg
    simpa only [d179662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22451 (p : Pattern) (guard : d179663 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179662 p = 1 := by simpa only [d179663, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22450 p hg
    simpa only [d179663, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179663, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179663, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22452 (p : Pattern) (guard : d179664 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179664, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179664, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179663 p = 1 := by simpa only [d179664, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22451 p hg
    simpa only [d179664, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22453 (p : Pattern) (guard : d179665 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179659 p = 1 := by simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22447 p hg
    simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22454 (p : Pattern) (guard : d179666 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179660 p = 1 := by simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22448 p hg
    simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179665 p = 1 := by simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22453 p hg
    simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22455 (p : Pattern) (guard : d179667 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179666 p = 1 := by simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22454 p hg
    simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22456 (p : Pattern) (guard : d179668 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179667 p = 1 := by simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22455 p hg
    simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22457 (p : Pattern) (guard : d179669 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179668 p = 1 := by simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22456 p hg
    simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22458 (p : Pattern) (guard : d179670 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179664 p = 1 := by simpa only [d179670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22452 p hg
    simpa only [d179670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179669 p = 1 := by simpa only [d179670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22457 p hg
    simpa only [d179670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22459 (p : Pattern) (guard : d179671 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179670 p = 1 := by simpa only [d179671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22458 p hg
    simpa only [d179671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22460 (p : Pattern) (guard : d179672 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179671 p = 1 := by simpa only [d179672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22459 p hg
    simpa only [d179672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22461 (p : Pattern) (guard : d179673 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179672 p = 1 := by simpa only [d179673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22460 p hg
    simpa only [d179673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22462 (p : Pattern) (guard : d179674 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179665 p = 1 := by simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22453 p hg
    simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22463 (p : Pattern) (guard : d179675 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179674 p = 1 := by simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22462 p hg
    simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22464 (p : Pattern) (guard : d179676 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179675 p = 1 := by simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22463 p hg
    simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22465 (p : Pattern) (guard : d179677 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179676 p = 1 := by simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22464 p hg
    simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22466 (p : Pattern) (guard : d179678 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179669 p = 1 := by simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22457 p hg
    simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179677 p = 1 := by simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22465 p hg
    simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22467 (p : Pattern) (guard : d179679 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179678 p = 1 := by simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22466 p hg
    simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22468 (p : Pattern) (guard : d179680 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179679 p = 1 := by simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22467 p hg
    simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22469 (p : Pattern) (guard : d179681 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179680 p = 1 := by simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22468 p hg
    simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22470 (p : Pattern) (guard : d179682 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179673 p = 1 := by simpa only [d179682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22461 p hg
    simpa only [d179682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179681 p = 1 := by simpa only [d179682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22469 p hg
    simpa only [d179682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22471 (p : Pattern) (guard : d179683 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179682 p = 1 := by simpa only [d179683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22470 p hg
    simpa only [d179683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22472 (p : Pattern) (guard : d179684 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179669 p = 1 := by simpa only [d179684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22457 p hg
    simpa only [d179684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22473 (p : Pattern) (guard : d179685 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179684 p = 1 := by simpa only [d179685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22472 p hg
    simpa only [d179685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22474 (p : Pattern) (guard : d179686 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179685 p = 1 := by simpa only [d179686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22473 p hg
    simpa only [d179686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22475 (p : Pattern) (guard : d179687 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179686 p = 1 := by simpa only [d179687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22474 p hg
    simpa only [d179687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22476 (p : Pattern) (guard : d179688 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179687 p = 1 := by simpa only [d179688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22475 p hg
    simpa only [d179688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22477 (p : Pattern) (guard : d179689 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179688 p = 1 := by simpa only [d179689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22476 p hg
    simpa only [d179689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22478 (p : Pattern) (guard : d179690 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179683 p = 1 := by simpa only [d179690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22471 p hg
    simpa only [d179690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179689 p = 1 := by simpa only [d179690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22477 p hg
    simpa only [d179690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22479 (p : Pattern) (guard : d179691 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179690 p = 1 := by simpa only [d179691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22478 p hg
    simpa only [d179691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22480 (p : Pattern) (guard : d179692 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179691 p = 1 := by simpa only [d179692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22479 p hg
    simpa only [d179692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22481 (p : Pattern) (guard : d179693 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179693, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179693, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179692 p = 1 := by simpa only [d179693, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22480 p hg
    simpa only [d179693, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22482 (p : Pattern) (guard : d179694 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179693 p = 1 := by simpa only [d179694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22481 p hg
    simpa only [d179694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22483 (p : Pattern) (guard : d179695 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179677 p = 1 := by simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22465 p hg
    simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22484 (p : Pattern) (guard : d179696 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179695 p = 1 := by simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22483 p hg
    simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22485 (p : Pattern) (guard : d179697 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179696 p = 1 := by simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22484 p hg
    simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22486 (p : Pattern) (guard : d179698 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179697 p = 1 := by simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22485 p hg
    simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22487 (p : Pattern) (guard : d179699 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179698 p = 1 := by simpa only [d179699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22486 p hg
    simpa only [d179699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22488 (p : Pattern) (guard : d179700 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179699 p = 1 := by simpa only [d179700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22487 p hg
    simpa only [d179700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22489 (p : Pattern) (guard : d179701 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179700 p = 1 := by simpa only [d179701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22488 p hg
    simpa only [d179701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22490 (p : Pattern) (guard : d179702 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179701 p = 1 := by simpa only [d179702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22489 p hg
    simpa only [d179702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22491 (p : Pattern) (guard : d179703 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179702 p = 1 := by simpa only [d179703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22490 p hg
    simpa only [d179703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22492 (p : Pattern) (guard : d179704 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179704, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179704, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179703 p = 1 := by simpa only [d179704, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22491 p hg
    simpa only [d179704, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22493 (p : Pattern) (guard : d179705 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179704 p = 1 := by simpa only [d179705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22492 p hg
    simpa only [d179705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22494 (p : Pattern) (guard : d179706 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179694 p = 1 := by simpa only [d179706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22482 p hg
    simpa only [d179706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179705 p = 1 := by simpa only [d179706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22493 p hg
    simpa only [d179706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22495 (p : Pattern) (guard : d179707 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179706 p = 1 := by simpa only [d179707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22494 p hg
    simpa only [d179707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22496 (p : Pattern) (guard : d179708 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179707 p = 1 := by simpa only [d179708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22495 p hg
    simpa only [d179708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22497 (p : Pattern) (guard : d179709 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179708 p = 1 := by simpa only [d179709, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22496 p hg
    simpa only [d179709, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179709, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d179709, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22498 (p : Pattern) (guard : d179710 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d179628 p = 1 := by simpa only [d179710, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22422 p hg
    simpa only [d179710, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179709 p = 1 := by simpa only [d179710, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22497 p hg
    simpa only [d179710, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22499 (p : Pattern) (guard : d179711 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179710 p = 1 := by simpa only [d179711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22498 p hg
    simpa only [d179711, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
