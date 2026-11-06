import NetHack.Soko22Hazard87.Compare030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7750 (p : Pattern) (guard : d2063 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7749 p hg
    simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d2063, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7751 (p : Pattern) (guard : d2064 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7750 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7752 (p : Pattern) (guard : d2065 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7751 p hg
    simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2065, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7753 (p : Pattern) (guard : d2066 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7752 p hg
    simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2066, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7754 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7744 p hg
    simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7753 p hg
    simpa only [d2348, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7755 (p : Pattern) (guard : d2349 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7754 p hg
    simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d2349, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7756 (p : Pattern) (guard : d2350 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2343 p = 1 := by simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7732 p hg
    simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2349 p = 1 := by simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7755 p hg
    simpa only [d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7757 (p : Pattern) (guard : d2351 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2344 p = 1 := by simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7733 p hg
    simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2350 p = 1 := by simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7756 p hg
    simpa only [d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7758 (p : Pattern) (guard : d2352 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2345 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7734 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2351 p = 1 := by simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7759 (p : Pattern) (guard : d2353 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2353, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d2353, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2352 p = 1 := by simpa only [d2353, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7758 p hg
    simpa only [d2353, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7760 (p : Pattern) (guard : d2354 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2354, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d2354, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2353 p = 1 := by simpa only [d2354, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7759 p hg
    simpa only [d2354, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7761 (p : Pattern) (guard : d2355 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2349 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7755 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7762 (p : Pattern) (guard : d2356 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2350 p = 1 := by simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7756 p hg
    simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2355 p = 1 := by simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7761 p hg
    simpa only [d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7763 (p : Pattern) (guard : d2357 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2351 p = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2356 p = 1 := by simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7762 p hg
    simpa only [d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7764 (p : Pattern) (guard : d2358 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2357 p = 1 := by simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7763 p hg
    simpa only [d2358, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7765 (p : Pattern) (guard : d2359 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2358 p = 1 := by simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7764 p hg
    simpa only [d2359, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7766 (p : Pattern) (guard : d2360 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2354 p = 1 := by simpa only [d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7760 p hg
    simpa only [d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2359 p = 1 := by simpa only [d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7765 p hg
    simpa only [d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7767 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7736 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7768 (p : Pattern) (guard : d2077 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7767 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7769 (p : Pattern) (guard : d2078 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7768 p hg
    simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d2078, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7770 (p : Pattern) (guard : d2079 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7769 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7771 (p : Pattern) (guard : d2361 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2079 p = 1 := by simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7770 p hg
    simpa only [d2361, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7772 (p : Pattern) (guard : d2080 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7251 p hg
    simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2080, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7773 (p : Pattern) (guard : d2362 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2361 p = 1 := by simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7771 p hg
    simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2080 p = 1 := by simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7772 p hg
    simpa only [d2362, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7774 (p : Pattern) (guard : d2076 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7775 (p : Pattern) (guard : d2077 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7774 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7776 (p : Pattern) (guard : d2078 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7775 p hg
    simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d2078, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7777 (p : Pattern) (guard : d2079 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7776 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7778 (p : Pattern) (guard : d2080 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7777 p hg
    simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2080, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7779 (p : Pattern) (guard : d2081 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7778 p hg
    simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2081, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7780 (p : Pattern) (guard : d2363 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2362 p = 1 := by simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7773 p hg
    simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7779 p hg
    simpa only [d2363, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7781 (p : Pattern) (guard : d2364 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2363 p = 1 := by simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7780 p hg
    simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d2364, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7782 (p : Pattern) (guard : d2365 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2364 p = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7783 (p : Pattern) (guard : d2366 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2355 p = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7761 p hg
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2365 p = 1 := by simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7782 p hg
    simpa only [d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7784 (p : Pattern) (guard : d2367 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2356 p = 1 := by simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7762 p hg
    simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2366 p = 1 := by simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7783 p hg
    simpa only [d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7785 (p : Pattern) (guard : d2368 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2367 p = 1 := by simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7784 p hg
    simpa only [d2368, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7786 (p : Pattern) (guard : d2369 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2368 p = 1 := by simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7785 p hg
    simpa only [d2369, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7787 (p : Pattern) (guard : d2370 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2359 p = 1 := by simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7765 p hg
    simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2369 p = 1 := by simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7788 (p : Pattern) (guard : d2371 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2360 p = 1 := by simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7766 p hg
    simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2370 p = 1 := by simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7789 (p : Pattern) (guard : d2372 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2371 p = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7788 p hg
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7790 (p : Pattern) (guard : d2373 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2372 p = 1 := by simpa only [d2373, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7789 p hg
    simpa only [d2373, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2373, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d2373, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7791 (p : Pattern) (guard : d2374 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2374, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2374, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2373 p = 1 := by simpa only [d2374, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d2374, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7792 (p : Pattern) (guard : d7161 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2359 p = 1 := by simpa only [d7161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7765 p hg
    simpa only [d7161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7793 (p : Pattern) (guard : d6642 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2350 p = 1 := by simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7756 p hg
    simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7794 (p : Pattern) (guard : d5238 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7795 (p : Pattern) (guard : d5239 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7794 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7796 (p : Pattern) (guard : d5240 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7795 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7797 (p : Pattern) (guard : d5241 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7708 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7798 (p : Pattern) (guard : d5242 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7797 p hg
    simpa only [d5242, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5242, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7799 (p : Pattern) (guard : d5243 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7795 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7800 (p : Pattern) (guard : d5244 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7801 (p : Pattern) (guard : d5245 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7800 p hg
    simpa only [d5245, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5245, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7802 (p : Pattern) (guard : d5246 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7798 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7801 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7803 (p : Pattern) (guard : d6643 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6643, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d6643, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5246 p = 1 := by simpa only [d6643, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7802 p hg
    simpa only [d6643, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7804 (p : Pattern) (guard : d5247 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d5247, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d5247, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7805 (p : Pattern) (guard : d6644 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6643 p = 1 := by simpa only [d6644, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7803 p hg
    simpa only [d6644, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5247 p = 1 := by simpa only [d6644, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7804 p hg
    simpa only [d6644, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7806 (p : Pattern) (guard : d5238 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7807 (p : Pattern) (guard : d5239 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7806 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7808 (p : Pattern) (guard : d5240 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7809 (p : Pattern) (guard : d5241 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7808 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7725 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7810 (p : Pattern) (guard : d5242 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7809 p hg
    simpa only [d5242, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5242, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7811 (p : Pattern) (guard : d5243 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7812 (p : Pattern) (guard : d5244 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7811 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7813 (p : Pattern) (guard : d5245 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d5245, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5245, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7814 (p : Pattern) (guard : d5246 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7810 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7815 (p : Pattern) (guard : d5247 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7814 p hg
    simpa only [d5247, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5247, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7816 (p : Pattern) (guard : d5248 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d5248, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5248, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7817 (p : Pattern) (guard : d6645 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6644 p = 1 := by simpa only [d6645, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d6645, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d6645, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7816 p hg
    simpa only [d6645, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7818 (p : Pattern) (guard : d6646 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6645 p = 1 := by simpa only [d6646, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d6646, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6646, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d6646, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7819 (p : Pattern) (guard : d6647 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6646 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7820 (p : Pattern) (guard : d6648 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6647 p = 1 := by simpa only [d6648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7819 p hg
    simpa only [d6648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7821 (p : Pattern) (guard : d6649 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d6642 p = 1 := by simpa only [d6649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d6649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6648 p = 1 := by simpa only [d6649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7820 p hg
    simpa only [d6649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7822 (p : Pattern) (guard : d6650 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6650, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d6650, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6649 p = 1 := by simpa only [d6650, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7821 p hg
    simpa only [d6650, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7823 (p : Pattern) (guard : d6651 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6651, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d6651, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6650 p = 1 := by simpa only [d6651, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d6651, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7824 (p : Pattern) (guard : d6652 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d6651 p = 1 := by simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7823 p hg
    simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7825 (p : Pattern) (guard : d7162 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7161 p = 1 := by simpa only [d7162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7792 p hg
    simpa only [d7162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6652 p = 1 := by simpa only [d7162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d7162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7826 (p : Pattern) (guard : d7163 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7162 p = 1 := by simpa only [d7163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7825 p hg
    simpa only [d7163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7827 (p : Pattern) (guard : d7164 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7163 p = 1 := by simpa only [d7164, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7826 p hg
    simpa only [d7164, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7164, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d7164, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7828 (p : Pattern) (guard : d7165 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7165, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d7165, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7164 p = 1 := by simpa only [d7165, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7827 p hg
    simpa only [d7165, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7829 (p : Pattern) (guard : d7166 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2374 p = 1 := by simpa only [d7166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7791 p hg
    simpa only [d7166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7165 p = 1 := by simpa only [d7166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7828 p hg
    simpa only [d7166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7830 (p : Pattern) (guard : d7167 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7166 p = 1 := by simpa only [d7167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d7167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7831 (p : Pattern) (guard : d7168 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7167 p = 1 := by simpa only [d7168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7830 p hg
    simpa only [d7168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7832 (p : Pattern) (guard : d7169 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7168 p = 1 := by simpa only [d7169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d7169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7833 (p : Pattern) (guard : d6653 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2370 p = 1 := by simpa only [d6653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d6653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6652 p = 1 := by simpa only [d6653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d6653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7834 (p : Pattern) (guard : d6654 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6653 p = 1 := by simpa only [d6654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7833 p hg
    simpa only [d6654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7835 (p : Pattern) (guard : d6655 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6654 p = 1 := by simpa only [d6655, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7834 p hg
    simpa only [d6655, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6655, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6655, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7836 (p : Pattern) (guard : d6656 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6656, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6656, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6655 p = 1 := by simpa only [d6656, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7835 p hg
    simpa only [d6656, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7837 (p : Pattern) (guard : d2375 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2369 p = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7838 (p : Pattern) (guard : d2384 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2375 p = 1 := by simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7839 (p : Pattern) (guard : d2385 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2384 p = 1 := by simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7838 p hg
    simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7840 (p : Pattern) (guard : d2386 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2385 p = 1 := by simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7839 p hg
    simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d2386, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7841 (p : Pattern) (guard : d2387 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2386 p = 1 := by simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7840 p hg
    simpa only [d2387, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7842 (p : Pattern) (guard : d7170 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d6656 p = 1 := by simpa only [d7170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7836 p hg
    simpa only [d7170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2387 p = 1 := by simpa only [d7170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7841 p hg
    simpa only [d7170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7843 (p : Pattern) (guard : d7171 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7170 p = 1 := by simpa only [d7171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d7171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7844 (p : Pattern) (guard : d7172 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7171 p = 1 := by simpa only [d7172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7843 p hg
    simpa only [d7172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7845 (p : Pattern) (guard : d7173 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7172 p = 1 := by simpa only [d7173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7844 p hg
    simpa only [d7173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7846 (p : Pattern) (guard : d7174 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7169 p = 1 := by simpa only [d7174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7832 p hg
    simpa only [d7174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7173 p = 1 := by simpa only [d7174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7845 p hg
    simpa only [d7174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7847 (p : Pattern) (guard : d82255 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7174 p = 1 := by simpa only [d82255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7846 p hg
    simpa only [d82255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7848 (p : Pattern) (guard : d2376 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2370 p = 1 := by simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2375 p = 1 := by simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7849 (p : Pattern) (guard : d2377 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2376 p = 1 := by simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7848 p hg
    simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7850 (p : Pattern) (guard : d2378 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2377 p = 1 := by simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7849 p hg
    simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d2378, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7851 (p : Pattern) (guard : d2379 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2378 p = 1 := by simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7850 p hg
    simpa only [d2379, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7852 (p : Pattern) (guard : d6668 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2379 p = 1 := by simpa only [d6668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7851 p hg
    simpa only [d6668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7853 (p : Pattern) (guard : d6669 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6668 p = 1 := by simpa only [d6669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7852 p hg
    simpa only [d6669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7854 (p : Pattern) (guard : d6670 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6669 p = 1 := by simpa only [d6670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7853 p hg
    simpa only [d6670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7855 (p : Pattern) (guard : d6671 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6670 p = 1 := by simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7854 p hg
    simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7856 (p : Pattern) (guard : d6672 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6671 p = 1 := by simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7855 p hg
    simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7857 (p : Pattern) (guard : d6673 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6672 p = 1 := by simpa only [d6673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7856 p hg
    simpa only [d6673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7858 (p : Pattern) (guard : d82256 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82255 p = 1 := by simpa only [d82256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7847 p hg
    simpa only [d82256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6673 p = 1 := by simpa only [d82256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7857 p hg
    simpa only [d82256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7859 (p : Pattern) (guard : d82257 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82256 p = 1 := by simpa only [d82257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7858 p hg
    simpa only [d82257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7860 (p : Pattern) (guard : d82258 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82257 p = 1 := by simpa only [d82258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7859 p hg
    simpa only [d82258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7861 (p : Pattern) (guard : d82259 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82259, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82259, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82258 p = 1 := by simpa only [d82259, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7860 p hg
    simpa only [d82259, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7862 (p : Pattern) (guard : d82260 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82259 p = 1 := by simpa only [d82260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7861 p hg
    simpa only [d82260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7863 (p : Pattern) (guard : d2449 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2387 p = 1 := by simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7841 p hg
    simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7864 (p : Pattern) (guard : d2450 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2449 p = 1 := by simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7863 p hg
    simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7865 (p : Pattern) (guard : d2451 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2450 p = 1 := by simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7864 p hg
    simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7866 (p : Pattern) (guard : d2452 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2451 p = 1 := by simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7865 p hg
    simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7867 (p : Pattern) (guard : d2453 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2452 p = 1 := by simpa only [d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7866 p hg
    simpa only [d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7868 (p : Pattern) (guard : d2454 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2453 p = 1 := by simpa only [d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7867 p hg
    simpa only [d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7869 (p : Pattern) (guard : d2455 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2454 p = 1 := by simpa only [d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7868 p hg
    simpa only [d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7870 (p : Pattern) (guard : d2456 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2455 p = 1 := by simpa only [d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7869 p hg
    simpa only [d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7871 (p : Pattern) (guard : d2457 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2456 p = 1 := by simpa only [d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7870 p hg
    simpa only [d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7872 (p : Pattern) (guard : d2458 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2458, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2458, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2457 p = 1 := by simpa only [d2458, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7871 p hg
    simpa only [d2458, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7873 (p : Pattern) (guard : d2459 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2458 p = 1 := by simpa only [d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7872 p hg
    simpa only [d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7874 (p : Pattern) (guard : d82261 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82260 p = 1 := by simpa only [d82261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7862 p hg
    simpa only [d82261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2459 p = 1 := by simpa only [d82261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7873 p hg
    simpa only [d82261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7875 (p : Pattern) (guard : d82262 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82261 p = 1 := by simpa only [d82262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7874 p hg
    simpa only [d82262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7876 (p : Pattern) (guard : d82263 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82262 p = 1 := by simpa only [d82263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7875 p hg
    simpa only [d82263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7877 (p : Pattern) (guard : d82264 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82263 p = 1 := by simpa only [d82264, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7876 p hg
    simpa only [d82264, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82264, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82264, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7878 (p : Pattern) (guard : d82265 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82254 p = 1 := by simpa only [d82265, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7604 p hg
    simpa only [d82265, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82264 p = 1 := by simpa only [d82265, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7877 p hg
    simpa only [d82265, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7879 (p : Pattern) (guard : d82266 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82265 p = 1 := by simpa only [d82266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7878 p hg
    simpa only [d82266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7880 (p : Pattern) (guard : d82267 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82266 p = 1 := by simpa only [d82267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7879 p hg
    simpa only [d82267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7881 (p : Pattern) (guard : d82268 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82267 p = 1 := by simpa only [d82268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7880 p hg
    simpa only [d82268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7882 (p : Pattern) (guard : d82269 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82268 p = 1 := by simpa only [d82269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7881 p hg
    simpa only [d82269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7883 (p : Pattern) (guard : d82270 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82269 p = 1 := by simpa only [d82270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7882 p hg
    simpa only [d82270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7884 (p : Pattern) (guard : d82271 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82270 p = 1 := by simpa only [d82271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d82271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7885 (p : Pattern) (guard : d82272 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82271 p = 1 := by simpa only [d82272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7884 p hg
    simpa only [d82272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7886 (p : Pattern) (guard : d82273 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82272 p = 1 := by simpa only [d82273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7885 p hg
    simpa only [d82273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7887 (p : Pattern) (guard : d82274 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82273 p = 1 := by simpa only [d82274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7886 p hg
    simpa only [d82274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7888 (p : Pattern) (guard : d82275 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82274 p = 1 := by simpa only [d82275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7887 p hg
    simpa only [d82275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7889 (p : Pattern) (guard : d82276 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d82232 p = 1 := by simpa only [d82276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d82276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82275 p = 1 := by simpa only [d82276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d82276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7890 (p : Pattern) (guard : d82277 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 260 with
  | false =>
    have hg : d82276 p = 1 := by simpa only [d82277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7889 p hg
    simpa only [d82277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7891 (p : Pattern) (guard : d82278 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 259 with
  | false =>
    have hg : d82277 p = 1 := by simpa only [d82278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7890 p hg
    simpa only [d82278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7892 (p : Pattern) (guard : d82279 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 258 with
  | false =>
    have hg : d82278 p = 1 := by simpa only [d82279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7891 p hg
    simpa only [d82279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7893 (p : Pattern) (guard : d82280 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 257 with
  | false =>
    have hg : d82279 p = 1 := by simpa only [d82280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d82280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7894 (p : Pattern) (guard : d82281 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 256 with
  | false =>
    have hg : d82280 p = 1 := by simpa only [d82281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7893 p hg
    simpa only [d82281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7895 (p : Pattern) (guard : d82282 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 255 with
  | false =>
    have hg : d82281 p = 1 := by simpa only [d82282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7894 p hg
    simpa only [d82282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7896 (p : Pattern) (guard : d82283 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 254 with
  | false =>
    have hg : d82282 p = 1 := by simpa only [d82283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7895 p hg
    simpa only [d82283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7897 (p : Pattern) (guard : d82284 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 253 with
  | false =>
    have hg : d82283 p = 1 := by simpa only [d82284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7896 p hg
    simpa only [d82284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7898 (p : Pattern) (guard : d82285 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 252 with
  | false =>
    have hg : d82284 p = 1 := by simpa only [d82285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7897 p hg
    simpa only [d82285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7899 (p : Pattern) (guard : d82286 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 251 with
  | false =>
    have hg : d82285 p = 1 := by simpa only [d82286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7898 p hg
    simpa only [d82286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7900 (p : Pattern) (guard : d82287 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 250 with
  | false =>
    have hg : d82286 p = 1 := by simpa only [d82287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7899 p hg
    simpa only [d82287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7901 (p : Pattern) (guard : d82288 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 249 with
  | false =>
    have hg : d82287 p = 1 := by simpa only [d82288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7900 p hg
    simpa only [d82288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7902 (p : Pattern) (guard : d82289 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 245 with
  | false =>
    have hg : d82288 p = 1 := by simpa only [d82289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7901 p hg
    simpa only [d82289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7903 (p : Pattern) (guard : d82290 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 200 with
  | false =>
    have hg : d82289 p = 1 := by simpa only [d82290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7902 p hg
    simpa only [d82290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7904 (p : Pattern) (guard : d82291 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 199 with
  | false =>
    have hg : d82290 p = 1 := by simpa only [d82291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7903 p hg
    simpa only [d82291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7905 (p : Pattern) (guard : d82292 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 186 with
  | false =>
    have hg : d82291 p = 1 := by simpa only [d82292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7904 p hg
    simpa only [d82292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7906 (p : Pattern) (guard : d82293 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 185 with
  | false =>
    have hg : d82292 p = 1 := by simpa only [d82293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7905 p hg
    simpa only [d82293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7907 (p : Pattern) (guard : d82294 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 184 with
  | false =>
    have hg : d82293 p = 1 := by simpa only [d82294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7906 p hg
    simpa only [d82294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7908 (p : Pattern) (guard : d82295 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 181 with
  | false =>
    have hg : d82294 p = 1 := by simpa only [d82295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7907 p hg
    simpa only [d82295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7909 (p : Pattern) (guard : d82296 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 177 with
  | false =>
    have hg : d82295 p = 1 := by simpa only [d82296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7908 p hg
    simpa only [d82296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7910 (p : Pattern) (guard : d82297 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 164 with
  | false =>
    have hg : d82296 p = 1 := by simpa only [d82297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7909 p hg
    simpa only [d82297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7911 (p : Pattern) (guard : d82298 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 156 with
  | false =>
    have hg : d82297 p = 1 := by simpa only [d82298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7910 p hg
    simpa only [d82298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7912 (p : Pattern) (guard : d82299 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 155 with
  | false =>
    have hg : d82298 p = 1 := by simpa only [d82299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7911 p hg
    simpa only [d82299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7913 (p : Pattern) (guard : d82300 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 134 with
  | false =>
    have hg : d82299 p = 1 := by simpa only [d82300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7912 p hg
    simpa only [d82300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7914 (p : Pattern) (guard : d82301 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 133 with
  | false =>
    have hg : d82300 p = 1 := by simpa only [d82301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d82301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7915 (p : Pattern) (guard : d82302 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 120 with
  | false =>
    have hg : d82301 p = 1 := by simpa only [d82302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7914 p hg
    simpa only [d82302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7916 (p : Pattern) (guard : d82303 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 118 with
  | false =>
    have hg : d82302 p = 1 := by simpa only [d82303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7915 p hg
    simpa only [d82303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7917 (p : Pattern) (guard : d82304 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 114 with
  | false =>
    have hg : d82303 p = 1 := by simpa only [d82304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7916 p hg
    simpa only [d82304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7918 (p : Pattern) (guard : d82305 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 111 with
  | false =>
    have hg : d82304 p = 1 := by simpa only [d82305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7917 p hg
    simpa only [d82305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7919 (p : Pattern) (guard : d82306 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 98 with
  | false =>
    have hg : d82305 p = 1 := by simpa only [d82306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7918 p hg
    simpa only [d82306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7920 (p : Pattern) (guard : d82307 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 97 with
  | false =>
    have hg : d82306 p = 1 := by simpa only [d82307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d82307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7921 (p : Pattern) (guard : d82308 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 94 with
  | false =>
    have hg : d82307 p = 1 := by simpa only [d82308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7920 p hg
    simpa only [d82308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7922 (p : Pattern) (guard : d82309 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 76 with
  | false =>
    have hg : d82308 p = 1 := by simpa only [d82309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7921 p hg
    simpa only [d82309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7923 (p : Pattern) (guard : d82310 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 67 with
  | false =>
    have hg : d82309 p = 1 := by simpa only [d82310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7922 p hg
    simpa only [d82310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7924 (p : Pattern) (guard : d82311 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 52 with
  | false =>
    have hg : d82310 p = 1 := by simpa only [d82311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7923 p hg
    simpa only [d82311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7925 (p : Pattern) (guard : d82312 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 47 with
  | false =>
    have hg : d82311 p = 1 := by simpa only [d82312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7924 p hg
    simpa only [d82312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7926 (p : Pattern) (guard : d82313 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 46 with
  | false =>
    have hg : d82312 p = 1 := by simpa only [d82313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7925 p hg
    simpa only [d82313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7927 (p : Pattern) (guard : d82314 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 45 with
  | false =>
    have hg : d82313 p = 1 := by simpa only [d82314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7926 p hg
    simpa only [d82314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7928 (p : Pattern) (guard : d82315 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 30 with
  | false =>
    have hg : d82314 p = 1 := by simpa only [d82315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7927 p hg
    simpa only [d82315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7929 (p : Pattern) (guard : d82316 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 29 with
  | false =>
    have hg : d82315 p = 1 := by simpa only [d82316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7928 p hg
    simpa only [d82316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7930 (p : Pattern) (guard : d82317 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 28 with
  | false =>
    have hg : d82316 p = 1 := by simpa only [d82317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7929 p hg
    simpa only [d82317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7931 (p : Pattern) (guard : d82318 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 27 with
  | false =>
    have hg : d82317 p = 1 := by simpa only [d82318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7930 p hg
    simpa only [d82318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7932 (p : Pattern) (guard : d82319 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 25 with
  | false =>
    have hg : d82318 p = 1 := by simpa only [d82319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7931 p hg
    simpa only [d82319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7933 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7934 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7935 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-2 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7936 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-2 : Int) + d47686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7937 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-2 : Int) + d47693 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7938 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-2 : Int) + d47690 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7939 (p : Pattern) (guard : d14 p = 1) : d4 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare7940 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7941 (p : Pattern) (guard : d15 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7939 p hg
    simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7940 p hg
    simpa only [d15, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7942 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7943 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7941 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7944 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7943 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7945 (p : Pattern) (guard : d18 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7946 (p : Pattern) (guard : d19 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7947 (p : Pattern) (guard : d20 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7946 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7948 (p : Pattern) (guard : d21 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7947 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7949 (p : Pattern) (guard : d22 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7948 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7950 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7951 (p : Pattern) (guard : d23 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7949 p hg
    simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d23, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7952 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7953 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7951 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7952 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7954 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7955 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7953 p hg
    simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d25, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7956 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7957 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7955 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7958 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d27, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7959 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7960 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7958 p hg
    simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d28, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7961 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7962 (p : Pattern) (guard : d29 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7960 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7963 (p : Pattern) (guard : d30 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7962 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7964 (p : Pattern) (guard : d31 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7963 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7965 (p : Pattern) (guard : d32 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7964 p hg
    simpa only [d32, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7966 (p : Pattern) (guard : d33 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7965 p hg
    simpa only [d33, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7967 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7968 (p : Pattern) (guard : d34 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7966 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7969 (p : Pattern) (guard : d35 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7968 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7970 (p : Pattern) (guard : d36 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7969 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7971 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-2 : Int) + d47696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7972 (p : Pattern) (guard : d37 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7970 p hg
    simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d37, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7973 (p : Pattern) (guard : d38 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7972 p hg
    simpa only [d38, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7974 (p : Pattern) (guard : d39 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7973 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7975 (p : Pattern) (guard : d40 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7974 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7976 (p : Pattern) (guard : d41 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7975 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7977 (p : Pattern) (guard : d42 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7976 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7978 (p : Pattern) (guard : d43 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7977 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7979 (p : Pattern) (guard : d100 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7978 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7980 (p : Pattern) (guard : d101 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7979 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7981 (p : Pattern) (guard : d102 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7980 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7982 (p : Pattern) (guard : d103 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7981 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7983 (p : Pattern) (guard : d104 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7982 p hg
    simpa only [d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7984 (p : Pattern) (guard : d49 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7976 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7985 (p : Pattern) (guard : d50 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7984 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7986 (p : Pattern) (guard : d107 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7985 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7987 (p : Pattern) (guard : d108 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7986 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7988 (p : Pattern) (guard : d109 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7987 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7989 (p : Pattern) (guard : d110 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7988 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7990 (p : Pattern) (guard : d111 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7982 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7989 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7991 (p : Pattern) (guard : d112 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7983 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7990 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7992 (p : Pattern) (guard : d113 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7991 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7993 (p : Pattern) (guard : d53637 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d113 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7992 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7994 (p : Pattern) (guard : d53638 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53637 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7993 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7995 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7996 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7997 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-2 : Int) + d47762 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7998 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-2 : Int) + d47756 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7999 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-2 : Int) + d47760 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Soko22Hazard87
