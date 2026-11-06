import NetHack.Soko22Hazard87.Compare144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36250 (p : Pattern) (guard : d317520 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317515 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36248 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317519 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36249 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36251 (p : Pattern) (guard : d317521 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317520 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36250 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317459 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36120 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36252 (p : Pattern) (guard : d317522 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317521 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36251 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36253 (p : Pattern) (guard : d317523 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317522 p = 1 := by simpa only [d317523, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36252 p hg
    simpa only [d317523, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317523, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317523, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36254 (p : Pattern) (guard : d317524 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317524, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317524, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317523 p = 1 := by simpa only [d317524, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36253 p hg
    simpa only [d317524, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36255 (p : Pattern) (guard : d317525 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317524 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36254 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317464 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36256 (p : Pattern) (guard : d317526 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317525 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36255 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36257 (p : Pattern) (guard : d317527 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317526 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36256 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36258 (p : Pattern) (guard : d317528 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317527 p = 1 := by simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36257 p hg
    simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36259 (p : Pattern) (guard : d317529 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317528 p = 1 := by simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36258 p hg
    simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317472 p = 1 := by simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36133 p hg
    simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36260 (p : Pattern) (guard : d317530 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317529 p = 1 := by simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36259 p hg
    simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36261 (p : Pattern) (guard : d317531 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36262 (p : Pattern) (guard : d317532 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317531 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36261 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36263 (p : Pattern) (guard : d317533 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317532 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36262 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36264 (p : Pattern) (guard : d317534 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317533 p = 1 := by simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36263 p hg
    simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36265 (p : Pattern) (guard : d317535 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317534 p = 1 := by simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36264 p hg
    simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36266 (p : Pattern) (guard : d317536 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317535 p = 1 := by simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36265 p hg
    simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36267 (p : Pattern) (guard : d317537 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317530 p = 1 := by simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36260 p hg
    simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317536 p = 1 := by simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36266 p hg
    simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36268 (p : Pattern) (guard : d317538 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317512 p = 1 := by simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36247 p hg
    simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317537 p = 1 := by simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36267 p hg
    simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36269 (p : Pattern) (guard : d317539 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317503 p = 1 := by simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36238 p hg
    simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317538 p = 1 := by simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36268 p hg
    simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36270 (p : Pattern) (guard : d317541 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317496 p = 1 := by simpa only [d317541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36154 p hg
    simpa only [d317541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36271 (p : Pattern) (guard : d317542 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317498 p = 1 := by simpa only [d317542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36156 p hg
    simpa only [d317542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36272 (p : Pattern) (guard : d317543 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317541 p = 1 := by simpa only [d317543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36270 p hg
    simpa only [d317543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317542 p = 1 := by simpa only [d317543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36271 p hg
    simpa only [d317543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36273 (p : Pattern) (guard : d317544 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317543 p = 1 := by simpa only [d317544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36272 p hg
    simpa only [d317544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36274 (p : Pattern) (guard : d317545 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317544 p = 1 := by simpa only [d317545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36273 p hg
    simpa only [d317545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36275 (p : Pattern) (guard : d317546 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317545 p = 1 := by simpa only [d317546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36274 p hg
    simpa only [d317546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36276 (p : Pattern) (guard : d317547 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317505 p = 1 := by simpa only [d317547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36163 p hg
    simpa only [d317547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36277 (p : Pattern) (guard : d317548 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317508 p = 1 := by simpa only [d317548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36166 p hg
    simpa only [d317548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36278 (p : Pattern) (guard : d317549 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317547 p = 1 := by simpa only [d317549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36276 p hg
    simpa only [d317549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317548 p = 1 := by simpa only [d317549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36277 p hg
    simpa only [d317549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36279 (p : Pattern) (guard : d317550 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317549 p = 1 := by simpa only [d317550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36278 p hg
    simpa only [d317550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36280 (p : Pattern) (guard : d317551 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317550 p = 1 := by simpa only [d317551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36279 p hg
    simpa only [d317551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36281 (p : Pattern) (guard : d317552 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317527 p = 1 := by simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36217 p hg
    simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36282 (p : Pattern) (guard : d317553 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317552 p = 1 := by simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36281 p hg
    simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317485 p = 1 := by simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36283 (p : Pattern) (guard : d317554 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317553 p = 1 := by simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36282 p hg
    simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36284 (p : Pattern) (guard : d317555 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317533 p = 1 := by simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36223 p hg
    simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36285 (p : Pattern) (guard : d317556 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317555 p = 1 := by simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36284 p hg
    simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36286 (p : Pattern) (guard : d317557 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317556 p = 1 := by simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36285 p hg
    simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36287 (p : Pattern) (guard : d317558 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317554 p = 1 := by simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36283 p hg
    simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317557 p = 1 := by simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36286 p hg
    simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36288 (p : Pattern) (guard : d317559 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317551 p = 1 := by simpa only [d317559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36280 p hg
    simpa only [d317559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317558 p = 1 := by simpa only [d317559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36287 p hg
    simpa only [d317559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36289 (p : Pattern) (guard : d317560 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317546 p = 1 := by simpa only [d317560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36275 p hg
    simpa only [d317560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317559 p = 1 := by simpa only [d317560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36288 p hg
    simpa only [d317560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36290 (p : Pattern) (guard : d317561 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317539 p = 1 := by simpa only [d317561, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36269 p hg
    simpa only [d317561, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317560 p = 1 := by simpa only [d317561, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36289 p hg
    simpa only [d317561, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36291 (p : Pattern) (guard : d317562 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317540 p = 1 := by simpa only [d317562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36230 p hg
    simpa only [d317562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317561 p = 1 := by simpa only [d317562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36290 p hg
    simpa only [d317562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36292 (p : Pattern) (guard : d317563 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317476 p = 1 := by simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36109 p hg
    simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36293 (p : Pattern) (guard : d317564 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317563 p = 1 := by simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36292 p hg
    simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36294 (p : Pattern) (guard : d317565 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317564 p = 1 := by simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36293 p hg
    simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36295 (p : Pattern) (guard : d317566 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317565 p = 1 := by simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36294 p hg
    simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36296 (p : Pattern) (guard : d317567 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317566 p = 1 := by simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36295 p hg
    simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36297 (p : Pattern) (guard : d317568 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317481 p = 1 := by simpa only [d317568, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36142 p hg
    simpa only [d317568, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317567 p = 1 := by simpa only [d317568, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36296 p hg
    simpa only [d317568, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36298 (p : Pattern) (guard : d317563 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317476 p = 1 := by simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36137 p hg
    simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36299 (p : Pattern) (guard : d317564 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317563 p = 1 := by simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d317564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36300 (p : Pattern) (guard : d317565 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317564 p = 1 := by simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36299 p hg
    simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36301 (p : Pattern) (guard : d317566 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317565 p = 1 := by simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36300 p hg
    simpa only [d317566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36302 (p : Pattern) (guard : d317567 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317566 p = 1 := by simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36301 p hg
    simpa only [d317567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36303 (p : Pattern) (guard : d317569 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317486 p = 1 := by simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36144 p hg
    simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36304 (p : Pattern) (guard : d317570 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317569 p = 1 := by simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36303 p hg
    simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36305 (p : Pattern) (guard : d317571 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317570 p = 1 := by simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36306 (p : Pattern) (guard : d317572 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317571 p = 1 := by simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36307 (p : Pattern) (guard : d317573 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317572 p = 1 := by simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36308 (p : Pattern) (guard : d317574 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317567 p = 1 := by simpa only [d317574, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36302 p hg
    simpa only [d317574, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317573 p = 1 := by simpa only [d317574, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36307 p hg
    simpa only [d317574, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36309 (p : Pattern) (guard : d317575 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317568 p = 1 := by simpa only [d317575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36297 p hg
    simpa only [d317575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317574 p = 1 := by simpa only [d317575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36308 p hg
    simpa only [d317575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36310 (p : Pattern) (guard : d317576 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317562 p = 1 := by simpa only [d317576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36291 p hg
    simpa only [d317576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317575 p = 1 := by simpa only [d317576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d317576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36311 (p : Pattern) (guard : d317577 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317576 p = 1 := by simpa only [d317577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d317577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36312 (p : Pattern) (guard : d317578 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317495 p = 1 := by simpa only [d317578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36153 p hg
    simpa only [d317578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317577 p = 1 := by simpa only [d317578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36311 p hg
    simpa only [d317578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36313 (p : Pattern) (guard : d34355 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35813 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36314 (p : Pattern) (guard : d34356 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36313 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36315 (p : Pattern) (guard : d34357 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36314 p hg
    simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36316 (p : Pattern) (guard : d316571 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36315 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316356 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36317 (p : Pattern) (guard : d316572 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316571 p = 1 := by simpa only [d316572, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36316 p hg
    simpa only [d316572, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316572, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316572, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36318 (p : Pattern) (guard : d316573 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316572 p = 1 := by simpa only [d316573, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36317 p hg
    simpa only [d316573, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316573, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316573, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36319 (p : Pattern) (guard : d316574 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316574, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316574, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316573 p = 1 := by simpa only [d316574, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36318 p hg
    simpa only [d316574, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36320 (p : Pattern) (guard : d316575 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316574 p = 1 := by simpa only [d316575, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d316575, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316575, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316575, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36321 (p : Pattern) (guard : d34366 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare36322 (p : Pattern) (guard : d34367 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36321 p hg
    simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d34367, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36323 (p : Pattern) (guard : d316576 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36322 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36324 (p : Pattern) (guard : d316577 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36323 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36325 (p : Pattern) (guard : d316578 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d316578, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36326 (p : Pattern) (guard : d316579 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36325 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36327 (p : Pattern) (guard : d316580 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316579 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36326 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36328 (p : Pattern) (guard : d316581 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316580 p = 1 := by simpa only [d316581, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36327 p hg
    simpa only [d316581, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316581, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316581, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36329 (p : Pattern) (guard : d316582 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36328 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36330 (p : Pattern) (guard : d316583 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316582 p = 1 := by simpa only [d316583, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36329 p hg
    simpa only [d316583, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316583, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316583, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36331 (p : Pattern) (guard : d316584 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316583 p = 1 := by simpa only [d316584, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36330 p hg
    simpa only [d316584, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316584, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316584, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36332 (p : Pattern) (guard : d316585 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316585, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316585, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316584 p = 1 := by simpa only [d316585, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36331 p hg
    simpa only [d316585, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36333 (p : Pattern) (guard : d316586 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316585 p = 1 := by simpa only [d316586, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36332 p hg
    simpa only [d316586, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316586, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316586, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36334 (p : Pattern) (guard : d316587 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316575 p = 1 := by simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36320 p hg
    simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316586 p = 1 := by simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36333 p hg
    simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36335 (p : Pattern) (guard : d316588 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36325 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36336 (p : Pattern) (guard : d316589 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36335 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36337 (p : Pattern) (guard : d316590 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36336 p hg
    simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d316590, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36338 (p : Pattern) (guard : d316591 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36337 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36328 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36339 (p : Pattern) (guard : d316592 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316591 p = 1 := by simpa only [d316592, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d316592, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316592, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316592, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36340 (p : Pattern) (guard : d316593 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316592 p = 1 := by simpa only [d316593, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d316593, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316593, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316593, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36341 (p : Pattern) (guard : d316594 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316594, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d316594, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316593 p = 1 := by simpa only [d316594, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36340 p hg
    simpa only [d316594, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36342 (p : Pattern) (guard : d316595 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316594 p = 1 := by simpa only [d316595, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36341 p hg
    simpa only [d316595, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316595, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d316595, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36343 (p : Pattern) (guard : d316596 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316595 p = 1 := by simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36342 p hg
    simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316380 p = 1 := by simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36344 (p : Pattern) (guard : d316597 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316587 p = 1 := by simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36334 p hg
    simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316596 p = 1 := by simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36343 p hg
    simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36345 (p : Pattern) (guard : d40149 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare36346 (p : Pattern) (guard : d317407 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36345 p hg
    simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36347 (p : Pattern) (guard : d317408 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36346 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36348 (p : Pattern) (guard : d317409 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36347 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36349 (p : Pattern) (guard : d317410 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36348 p hg
    simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36350 (p : Pattern) (guard : d317411 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36351 (p : Pattern) (guard : d317412 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36350 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35436 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36352 (p : Pattern) (guard : d317413 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36351 p hg
    simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36353 (p : Pattern) (guard : d317414 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35816 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36354 (p : Pattern) (guard : d317415 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36353 p hg
    simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36355 (p : Pattern) (guard : d317416 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36356 (p : Pattern) (guard : d317417 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36355 p hg
    simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36357 (p : Pattern) (guard : d317418 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317417 p = 1 := by simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36356 p hg
    simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36358 (p : Pattern) (guard : d317419 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35829 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36359 (p : Pattern) (guard : d317420 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36358 p hg
    simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36360 (p : Pattern) (guard : d317421 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36359 p hg
    simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36361 (p : Pattern) (guard : d317422 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36360 p hg
    simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36362 (p : Pattern) (guard : d317423 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317422 p = 1 := by simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36361 p hg
    simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36363 (p : Pattern) (guard : d317424 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317418 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36357 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317423 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36362 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36364 (p : Pattern) (guard : d317425 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36365 (p : Pattern) (guard : d317426 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36364 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36366 (p : Pattern) (guard : d317427 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36365 p hg
    simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36367 (p : Pattern) (guard : d317428 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36366 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36368 (p : Pattern) (guard : d317429 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36367 p hg
    simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36369 (p : Pattern) (guard : d317430 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36368 p hg
    simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36370 (p : Pattern) (guard : d317431 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36369 p hg
    simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36371 (p : Pattern) (guard : d317432 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317431 p = 1 := by simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36370 p hg
    simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36372 (p : Pattern) (guard : d317433 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317432 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36371 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36373 (p : Pattern) (guard : d317434 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317424 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36363 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317433 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36372 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36374 (p : Pattern) (guard : d317513 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316597 p = 1 := by simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317434 p = 1 := by simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36373 p hg
    simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36375 (p : Pattern) (guard : d317514 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317514, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317514, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317513 p = 1 := by simpa only [d317514, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36374 p hg
    simpa only [d317514, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36376 (p : Pattern) (guard : d317515 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317515, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317515, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317514 p = 1 := by simpa only [d317515, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36375 p hg
    simpa only [d317515, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36377 (p : Pattern) (guard : d317449 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317432 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36371 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36378 (p : Pattern) (guard : d317516 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317433 p = 1 := by simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36372 p hg
    simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36377 p hg
    simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36379 (p : Pattern) (guard : d317517 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36373 p hg
    simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317516 p = 1 := by simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36378 p hg
    simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36380 (p : Pattern) (guard : d317518 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317518, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317518, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317517 p = 1 := by simpa only [d317518, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36379 p hg
    simpa only [d317518, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36381 (p : Pattern) (guard : d317519 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317519, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317519, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317518 p = 1 := by simpa only [d317519, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36380 p hg
    simpa only [d317519, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36382 (p : Pattern) (guard : d317520 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317515 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36376 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317519 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36381 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36383 (p : Pattern) (guard : d317435 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36384 (p : Pattern) (guard : d317436 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36383 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36385 (p : Pattern) (guard : d317437 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36384 p hg
    simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36386 (p : Pattern) (guard : d317438 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36385 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36387 (p : Pattern) (guard : d317439 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36386 p hg
    simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36388 (p : Pattern) (guard : d317440 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36387 p hg
    simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36389 (p : Pattern) (guard : d317441 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36388 p hg
    simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36390 (p : Pattern) (guard : d317442 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317441 p = 1 := by simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36389 p hg
    simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36391 (p : Pattern) (guard : d317443 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36385 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36392 (p : Pattern) (guard : d317444 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36391 p hg
    simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36393 (p : Pattern) (guard : d317445 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36392 p hg
    simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36394 (p : Pattern) (guard : d317446 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36393 p hg
    simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36395 (p : Pattern) (guard : d317447 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317446 p = 1 := by simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36394 p hg
    simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36396 (p : Pattern) (guard : d317448 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317442 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36390 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317447 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36397 (p : Pattern) (guard : d317450 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317448 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36396 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36377 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36398 (p : Pattern) (guard : d317451 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36373 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317450 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36399 (p : Pattern) (guard : d317452 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317451 p = 1 := by simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36398 p hg
    simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36400 (p : Pattern) (guard : d317453 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36399 p hg
    simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36401 (p : Pattern) (guard : d317454 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317447 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36402 (p : Pattern) (guard : d317455 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317454 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36401 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36403 (p : Pattern) (guard : d317456 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317450 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317455 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36402 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36404 (p : Pattern) (guard : d317457 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317456 p = 1 := by simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36403 p hg
    simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36405 (p : Pattern) (guard : d317458 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36404 p hg
    simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36406 (p : Pattern) (guard : d317459 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36405 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36407 (p : Pattern) (guard : d317521 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317520 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36382 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317459 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36406 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36408 (p : Pattern) (guard : d317522 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317521 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36407 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36409 (p : Pattern) (guard : d317523 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317522 p = 1 := by simpa only [d317523, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36408 p hg
    simpa only [d317523, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317523, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317523, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36410 (p : Pattern) (guard : d317524 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317524, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317524, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317523 p = 1 := by simpa only [d317524, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36409 p hg
    simpa only [d317524, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36411 (p : Pattern) (guard : d317460 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36405 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36412 (p : Pattern) (guard : d317461 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36406 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36411 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36413 (p : Pattern) (guard : d317462 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36412 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36414 (p : Pattern) (guard : d317463 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36413 p hg
    simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36415 (p : Pattern) (guard : d317464 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36414 p hg
    simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36416 (p : Pattern) (guard : d317525 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317524 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36410 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317464 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36415 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36417 (p : Pattern) (guard : d317526 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317525 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36416 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36418 (p : Pattern) (guard : d317527 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317526 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36417 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36419 (p : Pattern) (guard : d317552 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317527 p = 1 := by simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36418 p hg
    simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36420 (p : Pattern) (guard : d317465 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36411 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36421 (p : Pattern) (guard : d317466 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36420 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36422 (p : Pattern) (guard : d317467 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36421 p hg
    simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36423 (p : Pattern) (guard : d317468 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36422 p hg
    simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36424 (p : Pattern) (guard : d317469 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36415 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36423 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36425 (p : Pattern) (guard : d317470 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36424 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36426 (p : Pattern) (guard : d317471 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36427 (p : Pattern) (guard : d317485 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317471 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36426 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36428 (p : Pattern) (guard : d317553 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317552 p = 1 := by simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36419 p hg
    simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317485 p = 1 := by simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36427 p hg
    simpa only [d317553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36429 (p : Pattern) (guard : d317554 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317553 p = 1 := by simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36428 p hg
    simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36430 (p : Pattern) (guard : d317531 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36415 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36431 (p : Pattern) (guard : d317532 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317531 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36430 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36432 (p : Pattern) (guard : d317533 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317532 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36433 (p : Pattern) (guard : d317555 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317533 p = 1 := by simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36432 p hg
    simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36434 (p : Pattern) (guard : d317556 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317555 p = 1 := by simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36433 p hg
    simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36435 (p : Pattern) (guard : d317557 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317556 p = 1 := by simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36436 (p : Pattern) (guard : d317558 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317554 p = 1 := by simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36429 p hg
    simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317557 p = 1 := by simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36435 p hg
    simpa only [d317558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36437 (p : Pattern) (guard : d317579 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317558 p = 1 := by simpa only [d317579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36436 p hg
    simpa only [d317579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36438 (p : Pattern) (guard : d317580 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317579 p = 1 := by simpa only [d317580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d317580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36439 (p : Pattern) (guard : d317581 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317581, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317581, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317580 p = 1 := by simpa only [d317581, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36438 p hg
    simpa only [d317581, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36440 (p : Pattern) (guard : d317582 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317581 p = 1 := by simpa only [d317582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36439 p hg
    simpa only [d317582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36441 (p : Pattern) (guard : d317473 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36423 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36442 (p : Pattern) (guard : d317474 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36441 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36443 (p : Pattern) (guard : d317475 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36442 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36444 (p : Pattern) (guard : d317486 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317475 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36443 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36445 (p : Pattern) (guard : d317569 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317486 p = 1 := by simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36444 p hg
    simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36446 (p : Pattern) (guard : d317570 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317569 p = 1 := by simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36445 p hg
    simpa only [d317570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36447 (p : Pattern) (guard : d317571 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317570 p = 1 := by simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36446 p hg
    simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36448 (p : Pattern) (guard : d317572 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317571 p = 1 := by simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36447 p hg
    simpa only [d317572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36449 (p : Pattern) (guard : d317573 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317572 p = 1 := by simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36448 p hg
    simpa only [d317573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36450 (p : Pattern) (guard : d317583 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317583, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317583, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317573 p = 1 := by simpa only [d317583, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36449 p hg
    simpa only [d317583, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36451 (p : Pattern) (guard : d317584 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317583 p = 1 := by simpa only [d317584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36450 p hg
    simpa only [d317584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36452 (p : Pattern) (guard : d317585 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317582 p = 1 := by simpa only [d317585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36440 p hg
    simpa only [d317585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317584 p = 1 := by simpa only [d317585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d317585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36453 (p : Pattern) (guard : d317586 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317585 p = 1 := by simpa only [d317586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36452 p hg
    simpa only [d317586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36454 (p : Pattern) (guard : d317587 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317586 p = 1 := by simpa only [d317587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36453 p hg
    simpa only [d317587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d317587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36455 (p : Pattern) (guard : d317588 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d317578 p = 1 := by simpa only [d317588, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36312 p hg
    simpa only [d317588, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317587 p = 1 := by simpa only [d317588, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36454 p hg
    simpa only [d317588, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36456 (p : Pattern) (guard : d34355 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35908 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36457 (p : Pattern) (guard : d34356 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36456 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36458 (p : Pattern) (guard : d34357 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36457 p hg
    simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d34357, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36459 (p : Pattern) (guard : d316571 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36458 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316356 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35911 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36460 (p : Pattern) (guard : d316674 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316571 p = 1 := by simpa only [d316674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d316674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36461 (p : Pattern) (guard : d316572 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316571 p = 1 := by simpa only [d316572, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36174 p hg
    simpa only [d316572, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316572, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316572, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36462 (p : Pattern) (guard : d316675 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316674 p = 1 := by simpa only [d316675, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36460 p hg
    simpa only [d316675, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316572 p = 1 := by simpa only [d316675, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d316675, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36463 (p : Pattern) (guard : d34355 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35921 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36464 (p : Pattern) (guard : d34356 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36463 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36465 (p : Pattern) (guard : d34357 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36464 p hg
    simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d34357, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36466 (p : Pattern) (guard : d316571 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316356 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36467 (p : Pattern) (guard : d316572 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316571 p = 1 := by simpa only [d316572, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36466 p hg
    simpa only [d316572, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316572, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316572, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36468 (p : Pattern) (guard : d316573 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316572 p = 1 := by simpa only [d316573, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36467 p hg
    simpa only [d316573, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316573, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316573, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36469 (p : Pattern) (guard : d316676 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316675 p = 1 := by simpa only [d316676, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36462 p hg
    simpa only [d316676, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316573 p = 1 := by simpa only [d316676, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36468 p hg
    simpa only [d316676, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36470 (p : Pattern) (guard : d316677 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316676 p = 1 := by simpa only [d316677, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d316677, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316677, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316677, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36471 (p : Pattern) (guard : d34366 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare36472 (p : Pattern) (guard : d34367 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36471 p hg
    simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d34367, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36473 (p : Pattern) (guard : d316576 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36472 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36474 (p : Pattern) (guard : d316577 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36475 (p : Pattern) (guard : d316578 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36474 p hg
    simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d316578, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36476 (p : Pattern) (guard : d316579 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36475 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35934 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36477 (p : Pattern) (guard : d316580 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316579 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36476 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36478 (p : Pattern) (guard : d316581 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316580 p = 1 := by simpa only [d316581, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36477 p hg
    simpa only [d316581, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316581, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316581, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36479 (p : Pattern) (guard : d316582 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35911 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36480 (p : Pattern) (guard : d316678 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316582 p = 1 := by simpa only [d316678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36479 p hg
    simpa only [d316678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36481 (p : Pattern) (guard : d316583 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316582 p = 1 := by simpa only [d316583, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36187 p hg
    simpa only [d316583, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316583, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316583, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36482 (p : Pattern) (guard : d316679 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316678 p = 1 := by simpa only [d316679, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36480 p hg
    simpa only [d316679, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316583 p = 1 := by simpa only [d316679, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36481 p hg
    simpa only [d316679, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36483 (p : Pattern) (guard : d34366 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare36484 (p : Pattern) (guard : d34367 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36483 p hg
    simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d34367, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36485 (p : Pattern) (guard : d316576 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36484 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36486 (p : Pattern) (guard : d316577 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36485 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36487 (p : Pattern) (guard : d316578 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36486 p hg
    simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d316578, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36488 (p : Pattern) (guard : d316579 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36487 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35946 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36489 (p : Pattern) (guard : d316580 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316579 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36488 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36490 (p : Pattern) (guard : d316581 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316580 p = 1 := by simpa only [d316581, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36489 p hg
    simpa only [d316581, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316581, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316581, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36491 (p : Pattern) (guard : d316582 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36490 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36492 (p : Pattern) (guard : d316583 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316582 p = 1 := by simpa only [d316583, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36491 p hg
    simpa only [d316583, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316583, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316583, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36493 (p : Pattern) (guard : d316584 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316583 p = 1 := by simpa only [d316584, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36492 p hg
    simpa only [d316584, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316584, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316584, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36494 (p : Pattern) (guard : d316680 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316679 p = 1 := by simpa only [d316680, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36482 p hg
    simpa only [d316680, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316584 p = 1 := by simpa only [d316680, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36493 p hg
    simpa only [d316680, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36495 (p : Pattern) (guard : d316681 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316680 p = 1 := by simpa only [d316681, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36494 p hg
    simpa only [d316681, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316681, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316681, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36496 (p : Pattern) (guard : d316682 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316677 p = 1 := by simpa only [d316682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36470 p hg
    simpa only [d316682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316681 p = 1 := by simpa only [d316682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36495 p hg
    simpa only [d316682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36497 (p : Pattern) (guard : d316588 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36475 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36498 (p : Pattern) (guard : d316589 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36497 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36499 (p : Pattern) (guard : d316590 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36498 p hg
    simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d316590, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
