import NetHack.Soko22Hazard87.Compare157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39500 (p : Pattern) (guard : d27032 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39473 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39501 (p : Pattern) (guard : d235783 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39500 p hg
    simpa only [d235783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39502 (p : Pattern) (guard : d235784 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d235783 p = 1 := by simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39501 p hg
    simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d235784, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39503 (p : Pattern) (guard : d317976 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317064 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39476 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235784 p = 1 := by simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39502 p hg
    simpa only [d317976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39504 (p : Pattern) (guard : d317977 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317976 p = 1 := by simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39503 p hg
    simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317977, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39505 (p : Pattern) (guard : d317978 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317977 p = 1 := by simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39504 p hg
    simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317978, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39506 (p : Pattern) (guard : d318113 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d318112 p = 1 := by simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39499 p hg
    simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317978 p = 1 := by simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39505 p hg
    simpa only [d318113, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39507 (p : Pattern) (guard : d318114 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d318113 p = 1 := by simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39506 p hg
    simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d318114, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39508 (p : Pattern) (guard : d317094 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39495 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39509 (p : Pattern) (guard : d317283 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317094 p = 1 := by simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39508 p hg
    simpa only [d317283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39510 (p : Pattern) (guard : d317095 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39309 p hg
    simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317095, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39511 (p : Pattern) (guard : d317284 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317283 p = 1 := by simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39509 p hg
    simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317095 p = 1 := by simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39510 p hg
    simpa only [d317284, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39512 (p : Pattern) (guard : d317094 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d235784 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39502 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39513 (p : Pattern) (guard : d317095 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317094 p = 1 := by simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39512 p hg
    simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317095, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39514 (p : Pattern) (guard : d317096 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317095 p = 1 := by simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39513 p hg
    simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317096, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39515 (p : Pattern) (guard : d317285 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317284 p = 1 := by simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39511 p hg
    simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317096 p = 1 := by simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39514 p hg
    simpa only [d317285, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39516 (p : Pattern) (guard : d317286 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317285 p = 1 := by simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39515 p hg
    simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317286, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39517 (p : Pattern) (guard : d318115 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d318114 p = 1 := by simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39507 p hg
    simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317286 p = 1 := by simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39516 p hg
    simpa only [d318115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39518 (p : Pattern) (guard : d318116 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d318115 p = 1 := by simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39517 p hg
    simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d318116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39519 (p : Pattern) (guard : d318117 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317262 p = 1 := by simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39492 p hg
    simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318116 p = 1 := by simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d318117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39520 (p : Pattern) (guard : d318118 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318117 p = 1 := by simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d318118, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39521 (p : Pattern) (guard : d318119 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318118 p = 1 := by simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39520 p hg
    simpa only [d318119, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39522 (p : Pattern) (guard : d317287 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317286 p = 1 := by simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39516 p hg
    simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39523 (p : Pattern) (guard : d317288 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317287 p = 1 := by simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39522 p hg
    simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39524 (p : Pattern) (guard : d318120 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d318116 p = 1 := by simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317288 p = 1 := by simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39523 p hg
    simpa only [d318120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39525 (p : Pattern) (guard : d318121 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318120 p = 1 := by simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39524 p hg
    simpa only [d318121, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39526 (p : Pattern) (guard : d318122 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318121 p = 1 := by simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39525 p hg
    simpa only [d318122, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39527 (p : Pattern) (guard : d318123 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d318119 p = 1 := by simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39521 p hg
    simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318122 p = 1 := by simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39526 p hg
    simpa only [d318123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39528 (p : Pattern) (guard : d318128 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d318122 p = 1 := by simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39526 p hg
    simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d318128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39529 (p : Pattern) (guard : d318129 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d318123 p = 1 := by simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39527 p hg
    simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318128 p = 1 := by simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39528 p hg
    simpa only [d318129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39530 (p : Pattern) (guard : d318130 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318129 p = 1 := by simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39529 p hg
    simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d318130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39531 (p : Pattern) (guard : d318131 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318130 p = 1 := by simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39530 p hg
    simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d318131, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39532 (p : Pattern) (guard : d318132 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318131 p = 1 := by simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39531 p hg
    simpa only [d318132, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39533 (p : Pattern) (guard : d318137 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d318128 p = 1 := by simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39528 p hg
    simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d318137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39534 (p : Pattern) (guard : d318138 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d318137 p = 1 := by simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39533 p hg
    simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d318138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39535 (p : Pattern) (guard : d318139 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d318138 p = 1 := by simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39534 p hg
    simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d318139, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39536 (p : Pattern) (guard : d318140 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318139 p = 1 := by simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39535 p hg
    simpa only [d318140, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39537 (p : Pattern) (guard : d318141 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318132 p = 1 := by simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39532 p hg
    simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318140 p = 1 := by simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39536 p hg
    simpa only [d318141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39538 (p : Pattern) (guard : d318142 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318141 p = 1 := by simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39537 p hg
    simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39539 (p : Pattern) (guard : d318143 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318142 p = 1 := by simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39538 p hg
    simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39540 (p : Pattern) (guard : d318144 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318143 p = 1 := by simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39539 p hg
    simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39541 (p : Pattern) (guard : d318158 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d318140 p = 1 := by simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39536 p hg
    simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39542 (p : Pattern) (guard : d318159 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d318158 p = 1 := by simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39541 p hg
    simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39543 (p : Pattern) (guard : d318160 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d318159 p = 1 := by simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39542 p hg
    simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39544 (p : Pattern) (guard : d318161 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d318160 p = 1 := by simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39543 p hg
    simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39545 (p : Pattern) (guard : d318483 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d318144 p = 1 := by simpa only [d318483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39540 p hg
    simpa only [d318483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318161 p = 1 := by simpa only [d318483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39544 p hg
    simpa only [d318483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39546 (p : Pattern) (guard : d318484 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318483 p = 1 := by simpa only [d318484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39545 p hg
    simpa only [d318484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39547 (p : Pattern) (guard : d318485 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318484 p = 1 := by simpa only [d318485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39546 p hg
    simpa only [d318485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39548 (p : Pattern) (guard : d318486 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318485 p = 1 := by simpa only [d318486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39547 p hg
    simpa only [d318486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39549 (p : Pattern) (guard : d318487 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318486 p = 1 := by simpa only [d318487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39548 p hg
    simpa only [d318487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39550 (p : Pattern) (guard : d318488 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318488, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318488, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318487 p = 1 := by simpa only [d318488, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39549 p hg
    simpa only [d318488, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39551 (p : Pattern) (guard : d318489 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318488 p = 1 := by simpa only [d318489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39550 p hg
    simpa only [d318489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39552 (p : Pattern) (guard : d318490 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318489 p = 1 := by simpa only [d318490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39551 p hg
    simpa only [d318490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39553 (p : Pattern) (guard : d318491 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318490 p = 1 := by simpa only [d318491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39552 p hg
    simpa only [d318491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39554 (p : Pattern) (guard : d318492 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318491 p = 1 := by simpa only [d318492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39553 p hg
    simpa only [d318492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39555 (p : Pattern) (guard : d318493 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318492 p = 1 := by simpa only [d318493, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39554 p hg
    simpa only [d318493, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318493, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d318493, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39556 (p : Pattern) (guard : d318494 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d318482 p = 1 := by simpa only [d318494, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39456 p hg
    simpa only [d318494, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318493 p = 1 := by simpa only [d318494, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39555 p hg
    simpa only [d318494, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39557 (p : Pattern) (guard : d318495 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318494 p = 1 := by simpa only [d318495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39556 p hg
    simpa only [d318495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39558 (p : Pattern) (guard : d318496 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318495 p = 1 := by simpa only [d318496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39557 p hg
    simpa only [d318496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39559 (p : Pattern) (guard : d318497 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318496 p = 1 := by simpa only [d318497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39558 p hg
    simpa only [d318497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39560 (p : Pattern) (guard : d318498 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318497 p = 1 := by simpa only [d318498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39559 p hg
    simpa only [d318498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39561 (p : Pattern) (guard : d318499 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318498 p = 1 := by simpa only [d318499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39560 p hg
    simpa only [d318499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39562 (p : Pattern) (guard : d318500 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318499 p = 1 := by simpa only [d318500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39561 p hg
    simpa only [d318500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39563 (p : Pattern) (guard : d318501 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318500 p = 1 := by simpa only [d318501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d318501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39564 (p : Pattern) (guard : d318502 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318501 p = 1 := by simpa only [d318502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39563 p hg
    simpa only [d318502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39565 (p : Pattern) (guard : d318503 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318502 p = 1 := by simpa only [d318503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39564 p hg
    simpa only [d318503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39566 (p : Pattern) (guard : d318504 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318503 p = 1 := by simpa only [d318504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39565 p hg
    simpa only [d318504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39567 (p : Pattern) (guard : d318505 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d318474 p = 1 := by simpa only [d318505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39280 p hg
    simpa only [d318505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318504 p = 1 := by simpa only [d318505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39566 p hg
    simpa only [d318505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39568 (p : Pattern) (guard : d318506 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d318505 p = 1 := by simpa only [d318506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39567 p hg
    simpa only [d318506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39569 (p : Pattern) (guard : d318507 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d318506 p = 1 := by simpa only [d318507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39568 p hg
    simpa only [d318507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39570 (p : Pattern) (guard : d318508 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d318507 p = 1 := by simpa only [d318508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39569 p hg
    simpa only [d318508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39571 (p : Pattern) (guard : d318509 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d318508 p = 1 := by simpa only [d318509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39570 p hg
    simpa only [d318509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39572 (p : Pattern) (guard : d318510 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d318509 p = 1 := by simpa only [d318510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39571 p hg
    simpa only [d318510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39573 (p : Pattern) (guard : d318511 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d318510 p = 1 := by simpa only [d318511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39572 p hg
    simpa only [d318511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39574 (p : Pattern) (guard : d318512 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d318511 p = 1 := by simpa only [d318512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39573 p hg
    simpa only [d318512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39575 (p : Pattern) (guard : d318513 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d318512 p = 1 := by simpa only [d318513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39574 p hg
    simpa only [d318513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39576 (p : Pattern) (guard : d318514 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d318513 p = 1 := by simpa only [d318514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39575 p hg
    simpa only [d318514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39577 (p : Pattern) (guard : d318515 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d318514 p = 1 := by simpa only [d318515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39576 p hg
    simpa only [d318515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39578 (p : Pattern) (guard : d318516 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d318515 p = 1 := by simpa only [d318516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39577 p hg
    simpa only [d318516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39579 (p : Pattern) (guard : d318517 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d318516 p = 1 := by simpa only [d318517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39578 p hg
    simpa only [d318517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39580 (p : Pattern) (guard : d318518 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d318517 p = 1 := by simpa only [d318518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39579 p hg
    simpa only [d318518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39581 (p : Pattern) (guard : d318519 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d318518 p = 1 := by simpa only [d318519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39580 p hg
    simpa only [d318519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39582 (p : Pattern) (guard : d318520 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d318519 p = 1 := by simpa only [d318520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39581 p hg
    simpa only [d318520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39583 (p : Pattern) (guard : d318521 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d318520 p = 1 := by simpa only [d318521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39582 p hg
    simpa only [d318521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39584 (p : Pattern) (guard : d318522 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d318521 p = 1 := by simpa only [d318522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39583 p hg
    simpa only [d318522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39585 (p : Pattern) (guard : d318523 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d318522 p = 1 := by simpa only [d318523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39584 p hg
    simpa only [d318523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39586 (p : Pattern) (guard : d318524 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d318523 p = 1 := by simpa only [d318524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39585 p hg
    simpa only [d318524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39587 (p : Pattern) (guard : d318525 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d318524 p = 1 := by simpa only [d318525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39586 p hg
    simpa only [d318525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39588 (p : Pattern) (guard : d318526 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d318525 p = 1 := by simpa only [d318526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39587 p hg
    simpa only [d318526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39589 (p : Pattern) (guard : d318527 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d318526 p = 1 := by simpa only [d318527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39588 p hg
    simpa only [d318527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39590 (p : Pattern) (guard : d318528 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d318527 p = 1 := by simpa only [d318528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39589 p hg
    simpa only [d318528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39591 (p : Pattern) (guard : d318529 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d318528 p = 1 := by simpa only [d318529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39590 p hg
    simpa only [d318529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39592 (p : Pattern) (guard : d318530 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d318529 p = 1 := by simpa only [d318530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39591 p hg
    simpa only [d318530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39593 (p : Pattern) (guard : d318531 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d318530 p = 1 := by simpa only [d318531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39592 p hg
    simpa only [d318531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39594 (p : Pattern) (guard : d318532 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d318531 p = 1 := by simpa only [d318532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39593 p hg
    simpa only [d318532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39595 (p : Pattern) (guard : d318533 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d318532 p = 1 := by simpa only [d318533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39594 p hg
    simpa only [d318533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39596 (p : Pattern) (guard : d318534 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d318533 p = 1 := by simpa only [d318534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39595 p hg
    simpa only [d318534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39597 (p : Pattern) (guard : d318535 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d318534 p = 1 := by simpa only [d318535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39596 p hg
    simpa only [d318535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39598 (p : Pattern) (guard : d318536 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d318535 p = 1 := by simpa only [d318536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39597 p hg
    simpa only [d318536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39599 (p : Pattern) (guard : d318537 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d318536 p = 1 := by simpa only [d318537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39598 p hg
    simpa only [d318537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39600 (p : Pattern) (guard : d318538 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d318537 p = 1 := by simpa only [d318538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39599 p hg
    simpa only [d318538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39601 (p : Pattern) (guard : d318539 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d318538 p = 1 := by simpa only [d318539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39600 p hg
    simpa only [d318539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39602 (p : Pattern) (guard : d318540 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d318539 p = 1 := by simpa only [d318540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39601 p hg
    simpa only [d318540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39603 (p : Pattern) (guard : d318541 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d318540 p = 1 := by simpa only [d318541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39602 p hg
    simpa only [d318541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39604 (p : Pattern) (guard : d318542 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d318541 p = 1 := by simpa only [d318542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39603 p hg
    simpa only [d318542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39605 (p : Pattern) (guard : d318543 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d318542 p = 1 := by simpa only [d318543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39604 p hg
    simpa only [d318543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39606 (p : Pattern) (guard : d318544 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d318543 p = 1 := by simpa only [d318544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39605 p hg
    simpa only [d318544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39607 (p : Pattern) (guard : d318545 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d318544 p = 1 := by simpa only [d318545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39606 p hg
    simpa only [d318545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39608 (p : Pattern) (guard : d318546 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d318545 p = 1 := by simpa only [d318546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39607 p hg
    simpa only [d318546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39609 (p : Pattern) (guard : d318547 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d318546 p = 1 := by simpa only [d318547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39608 p hg
    simpa only [d318547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39610 (p : Pattern) (guard : d318548 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d318547 p = 1 := by simpa only [d318548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39609 p hg
    simpa only [d318548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39611 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39612 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39613 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39614 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39615 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39616 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39617 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-1 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39618 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (-2 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39619 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39620 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39621 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (1 : Int) + d324470 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39622 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (1 : Int) + d324444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39623 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (1 : Int) + d324451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39624 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39625 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (1 : Int) + d324454 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39626 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39627 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39628 (p : Pattern) (guard : d32155 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare39629 (p : Pattern) (guard : d324612 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39628 p hg
    simpa only [d324612, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39630 (p : Pattern) (guard : d0 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39631 (p : Pattern) (guard : d324613 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39629 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39632 (p : Pattern) (guard : d324614 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39631 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39633 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (1 : Int) + d49396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39634 (p : Pattern) (guard : d324615 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39632 p hg
    simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39633 p hg
    simpa only [d324615, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39635 (p : Pattern) (guard : d324616 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39634 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39636 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (1 : Int) + d49351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39637 (p : Pattern) (guard : d324617 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39635 p hg
    simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d324617, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39638 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (1 : Int) + d324430 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39639 (p : Pattern) (guard : d324618 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39637 p hg
    simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d324618, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39640 (p : Pattern) (guard : d324619 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39639 p hg
    simpa only [d324619, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39641 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (1 : Int) + d324442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39642 (p : Pattern) (guard : d324620 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324619 p = 1 := by simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39640 p hg
    simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d324620, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39643 (p : Pattern) (guard : d324621 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324620 p = 1 := by simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39642 p hg
    simpa only [d324621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39644 (p : Pattern) (guard : d1115 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare39645 (p : Pattern) (guard : d221076 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39644 p hg
    simpa only [d221076, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39646 (p : Pattern) (guard : d221096 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39645 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39647 (p : Pattern) (guard : d19 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare39648 (p : Pattern) (guard : d221097 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39647 p hg
    simpa only [d221097, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39649 (p : Pattern) (guard : d221098 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39648 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39650 (p : Pattern) (guard : d221099 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39646 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39649 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39651 (p : Pattern) (guard : d221100 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39650 p hg
    simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39633 p hg
    simpa only [d221100, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39652 (p : Pattern) (guard : d324622 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39634 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39651 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39653 (p : Pattern) (guard : d324623 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39652 p hg
    simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d324623, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39654 (p : Pattern) (guard : d324624 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39653 p hg
    simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d324624, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39655 (p : Pattern) (guard : d324625 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39654 p hg
    simpa only [d324625, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39656 (p : Pattern) (guard : d324626 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324625 p = 1 := by simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39655 p hg
    simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d324626, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39657 (p : Pattern) (guard : d324627 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324620 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39642 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324626 p = 1 := by simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39656 p hg
    simpa only [d324627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39658 (p : Pattern) (guard : d324628 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324621 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39643 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324627 p = 1 := by simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39657 p hg
    simpa only [d324628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39659 (p : Pattern) (guard : d324629 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324626 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39656 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39660 (p : Pattern) (guard : d324630 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324627 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39657 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324629 p = 1 := by simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39659 p hg
    simpa only [d324630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39661 (p : Pattern) (guard : d324631 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324628 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39658 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324630 p = 1 := by simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39660 p hg
    simpa only [d324631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39662 (p : Pattern) (guard : d324632 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324631 p = 1 := by simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39661 p hg
    simpa only [d324632, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39663 (p : Pattern) (guard : d324633 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324632 p = 1 := by simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39662 p hg
    simpa only [d324633, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39664 (p : Pattern) (guard : d221101 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39651 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39665 (p : Pattern) (guard : d221102 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39664 p hg
    simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d221102, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39666 (p : Pattern) (guard : d221103 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39665 p hg
    simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d221103, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39667 (p : Pattern) (guard : d221104 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39666 p hg
    simpa only [d221104, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39668 (p : Pattern) (guard : d221105 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221104 p = 1 := by simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39667 p hg
    simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d221105, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39669 (p : Pattern) (guard : d221106 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221105 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39668 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d221106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39670 (p : Pattern) (guard : d324634 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324629 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39659 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221106 p = 1 := by simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39669 p hg
    simpa only [d324634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39671 (p : Pattern) (guard : d324635 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324630 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39660 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324634 p = 1 := by simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39670 p hg
    simpa only [d324635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39672 (p : Pattern) (guard : d324636 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324635 p = 1 := by simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39671 p hg
    simpa only [d324636, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39673 (p : Pattern) (guard : d324637 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324636 p = 1 := by simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39672 p hg
    simpa only [d324637, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39674 (p : Pattern) (guard : d324638 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324633 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39663 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324637 p = 1 := by simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39673 p hg
    simpa only [d324638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39675 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39676 (p : Pattern) (guard : d324639 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324637 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39673 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39677 (p : Pattern) (guard : d324640 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324638 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39674 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324639 p = 1 := by simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39676 p hg
    simpa only [d324640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39678 (p : Pattern) (guard : d324641 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324640 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39677 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39679 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (1 : Int) + d324471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39680 (p : Pattern) (guard : d324642 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324641 p = 1 := by simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39678 p hg
    simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324642, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39681 (p : Pattern) (guard : d324643 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324642 p = 1 := by simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39680 p hg
    simpa only [d324643, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39682 (p : Pattern) (guard : d324644 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324639 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39676 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39683 (p : Pattern) (guard : d324645 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324644 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39682 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39684 (p : Pattern) (guard : d324646 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324645 p = 1 := by simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39683 p hg
    simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324646, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39685 (p : Pattern) (guard : d324647 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324646 p = 1 := by simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39684 p hg
    simpa only [d324647, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39686 (p : Pattern) (guard : d324648 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324643 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39681 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324647 p = 1 := by simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39685 p hg
    simpa only [d324648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39687 (p : Pattern) (guard : d324649 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324648 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39686 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39688 (p : Pattern) (guard : d324650 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324649 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39687 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39689 (p : Pattern) (guard : d324651 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324650 p = 1 := by simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d324651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39690 (p : Pattern) (guard : d324652 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324647 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39685 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39691 (p : Pattern) (guard : d324653 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324652 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39690 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39692 (p : Pattern) (guard : d324654 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324653 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39691 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39693 (p : Pattern) (guard : d324655 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324654 p = 1 := by simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39692 p hg
    simpa only [d324655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39694 (p : Pattern) (guard : d324656 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324651 p = 1 := by simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39689 p hg
    simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324655 p = 1 := by simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39693 p hg
    simpa only [d324656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39695 (p : Pattern) (guard : d324657 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324656 p = 1 := by simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39694 p hg
    simpa only [d324657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39696 (p : Pattern) (guard : d324658 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324657 p = 1 := by simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39695 p hg
    simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39697 (p : Pattern) (guard : d324659 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324658 p = 1 := by simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39696 p hg
    simpa only [d324659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39698 (p : Pattern) (guard : d324660 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324659 p = 1 := by simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39697 p hg
    simpa only [d324660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39699 (p : Pattern) (guard : d324661 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324660 p = 1 := by simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39698 p hg
    simpa only [d324661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39700 (p : Pattern) (guard : d324662 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324661 p = 1 := by simpa only [d324662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39699 p hg
    simpa only [d324662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39701 (p : Pattern) (guard : d324663 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324662 p = 1 := by simpa only [d324663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39700 p hg
    simpa only [d324663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39702 (p : Pattern) (guard : d324664 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324650 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39703 (p : Pattern) (guard : d324665 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324654 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39692 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39704 (p : Pattern) (guard : d324666 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324664 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39702 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324665 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39703 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39705 (p : Pattern) (guard : d324667 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324666 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39704 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39706 (p : Pattern) (guard : d324668 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324667 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39705 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39707 (p : Pattern) (guard : d324669 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324668 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39706 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39708 (p : Pattern) (guard : d324670 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324669 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39707 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39709 (p : Pattern) (guard : d324671 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324660 p = 1 := by simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39698 p hg
    simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324670 p = 1 := by simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39708 p hg
    simpa only [d324671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39710 (p : Pattern) (guard : d324672 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324661 p = 1 := by simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39699 p hg
    simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324671 p = 1 := by simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39709 p hg
    simpa only [d324672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39711 (p : Pattern) (guard : d324673 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324672 p = 1 := by simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39710 p hg
    simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39712 (p : Pattern) (guard : d324674 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324663 p = 1 := by simpa only [d324674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39701 p hg
    simpa only [d324674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324673 p = 1 := by simpa only [d324674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39711 p hg
    simpa only [d324674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39713 (p : Pattern) (guard : d324675 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324649 p = 1 := by simpa only [d324675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39687 p hg
    simpa only [d324675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39714 (p : Pattern) (guard : d324676 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324675 p = 1 := by simpa only [d324676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39713 p hg
    simpa only [d324676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39715 (p : Pattern) (guard : d324677 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324653 p = 1 := by simpa only [d324677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39691 p hg
    simpa only [d324677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39716 (p : Pattern) (guard : d324678 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324677 p = 1 := by simpa only [d324678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39715 p hg
    simpa only [d324678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39717 (p : Pattern) (guard : d324679 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324676 p = 1 := by simpa only [d324679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39714 p hg
    simpa only [d324679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324678 p = 1 := by simpa only [d324679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39716 p hg
    simpa only [d324679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39718 (p : Pattern) (guard : d324680 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324679 p = 1 := by simpa only [d324680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39717 p hg
    simpa only [d324680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39719 (p : Pattern) (guard : d324681 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324680 p = 1 := by simpa only [d324681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39718 p hg
    simpa only [d324681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39720 (p : Pattern) (guard : d324682 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324681 p = 1 := by simpa only [d324682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39719 p hg
    simpa only [d324682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39721 (p : Pattern) (guard : d324683 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324648 p = 1 := by simpa only [d324683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39686 p hg
    simpa only [d324683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39722 (p : Pattern) (guard : d324684 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324683 p = 1 := by simpa only [d324684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39721 p hg
    simpa only [d324684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39723 (p : Pattern) (guard : d324685 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324684 p = 1 := by simpa only [d324685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39722 p hg
    simpa only [d324685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39724 (p : Pattern) (guard : d324686 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324652 p = 1 := by simpa only [d324686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39690 p hg
    simpa only [d324686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39725 (p : Pattern) (guard : d324687 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324686 p = 1 := by simpa only [d324687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39724 p hg
    simpa only [d324687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39726 (p : Pattern) (guard : d324688 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324687 p = 1 := by simpa only [d324688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39725 p hg
    simpa only [d324688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39727 (p : Pattern) (guard : d324689 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324685 p = 1 := by simpa only [d324689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39723 p hg
    simpa only [d324689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324688 p = 1 := by simpa only [d324689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39726 p hg
    simpa only [d324689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39728 (p : Pattern) (guard : d324690 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324689 p = 1 := by simpa only [d324690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39727 p hg
    simpa only [d324690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39729 (p : Pattern) (guard : d324691 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324690 p = 1 := by simpa only [d324691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39728 p hg
    simpa only [d324691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39730 (p : Pattern) (guard : d324692 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324621 p = 1 := by simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39643 p hg
    simpa only [d324692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39731 (p : Pattern) (guard : d324693 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324692 p = 1 := by simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39730 p hg
    simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324628 p = 1 := by simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39658 p hg
    simpa only [d324693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39732 (p : Pattern) (guard : d324694 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324694, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324694, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324693 p = 1 := by simpa only [d324694, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39731 p hg
    simpa only [d324694, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39733 (p : Pattern) (guard : d324695 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324695, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324695, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324694 p = 1 := by simpa only [d324695, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39732 p hg
    simpa only [d324695, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39734 (p : Pattern) (guard : d324696 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324695 p = 1 := by simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39733 p hg
    simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324633 p = 1 := by simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39663 p hg
    simpa only [d324696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39735 (p : Pattern) (guard : d324697 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324696 p = 1 := by simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39734 p hg
    simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324638 p = 1 := by simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39674 p hg
    simpa only [d324697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39736 (p : Pattern) (guard : d324698 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324697 p = 1 := by simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39735 p hg
    simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39737 (p : Pattern) (guard : d324699 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324698 p = 1 := by simpa only [d324699, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39736 p hg
    simpa only [d324699, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324699, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324699, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39738 (p : Pattern) (guard : d324700 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324700, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324700, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324699 p = 1 := by simpa only [d324700, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39737 p hg
    simpa only [d324700, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39739 (p : Pattern) (guard : d324701 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324700 p = 1 := by simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39738 p hg
    simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324643 p = 1 := by simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39681 p hg
    simpa only [d324701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39740 (p : Pattern) (guard : d324702 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324701 p = 1 := by simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39739 p hg
    simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39741 (p : Pattern) (guard : d324703 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324702 p = 1 := by simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39740 p hg
    simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39742 (p : Pattern) (guard : d324704 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324703 p = 1 := by simpa only [d324704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39741 p hg
    simpa only [d324704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39743 (p : Pattern) (guard : d324705 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324704 p = 1 := by simpa only [d324705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39742 p hg
    simpa only [d324705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324651 p = 1 := by simpa only [d324705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39689 p hg
    simpa only [d324705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39744 (p : Pattern) (guard : d324706 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324705 p = 1 := by simpa only [d324706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39743 p hg
    simpa only [d324706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39745 (p : Pattern) (guard : d324707 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39634 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39746 (p : Pattern) (guard : d324708 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324707 p = 1 := by simpa only [d324708, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39745 p hg
    simpa only [d324708, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324708, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d324708, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39747 (p : Pattern) (guard : d324709 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324708 p = 1 := by simpa only [d324709, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39746 p hg
    simpa only [d324709, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324709, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d324709, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39748 (p : Pattern) (guard : d324710 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324710, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d324710, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324709 p = 1 := by simpa only [d324710, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39747 p hg
    simpa only [d324710, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39749 (p : Pattern) (guard : d324711 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324710 p = 1 := by simpa only [d324711, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39748 p hg
    simpa only [d324711, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324711, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d324711, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
