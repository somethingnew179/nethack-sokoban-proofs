import NetHack.Soko22Hazard87.Compare124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31250 (p : Pattern) (guard : d258935 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31249 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31251 (p : Pattern) (guard : d258936 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31250 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31252 (p : Pattern) (guard : d258937 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31251 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31253 (p : Pattern) (guard : d258938 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31252 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31074 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31254 (p : Pattern) (guard : d258939 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31253 p hg
    simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d258939, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31255 (p : Pattern) (guard : d258940 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31074 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31256 (p : Pattern) (guard : d258941 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31255 p hg
    simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d258941, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31257 (p : Pattern) (guard : d258942 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31254 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31256 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31258 (p : Pattern) (guard : d258943 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31257 p hg
    simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258943, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31259 (p : Pattern) (guard : d258944 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31258 p hg
    simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258944, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31260 (p : Pattern) (guard : d259016 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259015 p = 1 := by simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31246 p hg
    simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31259 p hg
    simpa only [d259016, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31261 (p : Pattern) (guard : d259017 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259016 p = 1 := by simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31260 p hg
    simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259017, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31262 (p : Pattern) (guard : d259018 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259017 p = 1 := by simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31261 p hg
    simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258872 p = 1 := by simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31081 p hg
    simpa only [d259018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31263 (p : Pattern) (guard : d258948 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31242 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30904 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31264 (p : Pattern) (guard : d259019 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258948 p = 1 := by simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31263 p hg
    simpa only [d259019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31265 (p : Pattern) (guard : d258949 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31132 p hg
    simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258949, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31266 (p : Pattern) (guard : d259020 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259019 p = 1 := by simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31264 p hg
    simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258949 p = 1 := by simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31265 p hg
    simpa only [d259020, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31267 (p : Pattern) (guard : d258948 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31256 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30922 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31268 (p : Pattern) (guard : d258949 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31267 p hg
    simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258949, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31269 (p : Pattern) (guard : d258950 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31268 p hg
    simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258950, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31270 (p : Pattern) (guard : d259021 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259020 p = 1 := by simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31266 p hg
    simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31269 p hg
    simpa only [d259021, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31271 (p : Pattern) (guard : d259022 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259021 p = 1 := by simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31270 p hg
    simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259022, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31272 (p : Pattern) (guard : d259023 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259022 p = 1 := by simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31271 p hg
    simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258746 p = 1 := by simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30929 p hg
    simpa only [d259023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31273 (p : Pattern) (guard : d259024 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259018 p = 1 := by simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31262 p hg
    simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259023 p = 1 := by simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31272 p hg
    simpa only [d259024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31274 (p : Pattern) (guard : d259025 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259024 p = 1 := by simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31273 p hg
    simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258874 p = 1 := by simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31083 p hg
    simpa only [d259025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31275 (p : Pattern) (guard : d259026 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259025 p = 1 := by simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31274 p hg
    simpa only [d259026, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31276 (p : Pattern) (guard : d259027 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259026 p = 1 := by simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31275 p hg
    simpa only [d259027, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31277 (p : Pattern) (guard : d259028 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259027 p = 1 := by simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31276 p hg
    simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258877 p = 1 := by simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31086 p hg
    simpa only [d259028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31278 (p : Pattern) (guard : d259236 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258877 p = 1 := by simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31086 p hg
    simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31279 (p : Pattern) (guard : d259237 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259028 p = 1 := by simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31277 p hg
    simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259236 p = 1 := by simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31278 p hg
    simpa only [d259237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31280 (p : Pattern) (guard : d259238 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259237 p = 1 := by simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31279 p hg
    simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31281 (p : Pattern) (guard : d259239 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259238 p = 1 := by simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31280 p hg
    simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259239, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31282 (p : Pattern) (guard : d259240 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259239 p = 1 := by simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31281 p hg
    simpa only [d259240, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31283 (p : Pattern) (guard : d259245 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259236 p = 1 := by simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31278 p hg
    simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31284 (p : Pattern) (guard : d259246 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259245 p = 1 := by simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31283 p hg
    simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31285 (p : Pattern) (guard : d259247 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259246 p = 1 := by simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31284 p hg
    simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259247, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31286 (p : Pattern) (guard : d259248 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259247 p = 1 := by simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31285 p hg
    simpa only [d259248, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31287 (p : Pattern) (guard : d259249 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259240 p = 1 := by simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31282 p hg
    simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259248 p = 1 := by simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31286 p hg
    simpa only [d259249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31288 (p : Pattern) (guard : d259250 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259249 p = 1 := by simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31287 p hg
    simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31289 (p : Pattern) (guard : d259251 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259250 p = 1 := by simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31288 p hg
    simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31290 (p : Pattern) (guard : d259252 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259251 p = 1 := by simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31289 p hg
    simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31291 (p : Pattern) (guard : d259266 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259248 p = 1 := by simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31286 p hg
    simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31292 (p : Pattern) (guard : d259267 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259266 p = 1 := by simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31291 p hg
    simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31293 (p : Pattern) (guard : d259268 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259267 p = 1 := by simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31292 p hg
    simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31294 (p : Pattern) (guard : d259269 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259268 p = 1 := by simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31293 p hg
    simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31295 (p : Pattern) (guard : d260140 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259252 p = 1 := by simpa only [d260140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31290 p hg
    simpa only [d260140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259269 p = 1 := by simpa only [d260140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31294 p hg
    simpa only [d260140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31296 (p : Pattern) (guard : d260141 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260140 p = 1 := by simpa only [d260141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31295 p hg
    simpa only [d260141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31297 (p : Pattern) (guard : d260142 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d260141 p = 1 := by simpa only [d260142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31296 p hg
    simpa only [d260142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31298 (p : Pattern) (guard : d260143 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260142 p = 1 := by simpa only [d260143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31297 p hg
    simpa only [d260143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31299 (p : Pattern) (guard : d260144 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260143 p = 1 := by simpa only [d260144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31298 p hg
    simpa only [d260144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31300 (p : Pattern) (guard : d260145 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260145, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260145, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260144 p = 1 := by simpa only [d260145, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31299 p hg
    simpa only [d260145, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31301 (p : Pattern) (guard : d260146 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260145 p = 1 := by simpa only [d260146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31300 p hg
    simpa only [d260146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31302 (p : Pattern) (guard : d260147 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260146 p = 1 := by simpa only [d260147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31301 p hg
    simpa only [d260147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31303 (p : Pattern) (guard : d260148 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260147 p = 1 := by simpa only [d260148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31302 p hg
    simpa only [d260148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31304 (p : Pattern) (guard : d260149 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260148 p = 1 := by simpa only [d260149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31303 p hg
    simpa only [d260149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31305 (p : Pattern) (guard : d260150 p = 1) : d47865 p ≤ (-2 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260149 p = 1 := by simpa only [d260150, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31304 p hg
    simpa only [d260150, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260150, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d260150, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31306 (p : Pattern) (guard : d260151 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d260139 p = 1 := by simpa only [d260151, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31232 p hg
    simpa only [d260151, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260150 p = 1 := by simpa only [d260151, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31305 p hg
    simpa only [d260151, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31307 (p : Pattern) (guard : d260152 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260151 p = 1 := by simpa only [d260152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31306 p hg
    simpa only [d260152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31308 (p : Pattern) (guard : d260153 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260152 p = 1 := by simpa only [d260153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31307 p hg
    simpa only [d260153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31309 (p : Pattern) (guard : d260154 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260153 p = 1 := by simpa only [d260154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31308 p hg
    simpa only [d260154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31310 (p : Pattern) (guard : d260155 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260154 p = 1 := by simpa only [d260155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31309 p hg
    simpa only [d260155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31311 (p : Pattern) (guard : d260156 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260155 p = 1 := by simpa only [d260156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31310 p hg
    simpa only [d260156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31312 (p : Pattern) (guard : d260157 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260156 p = 1 := by simpa only [d260157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31311 p hg
    simpa only [d260157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31313 (p : Pattern) (guard : d260158 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260157 p = 1 := by simpa only [d260158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31312 p hg
    simpa only [d260158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31314 (p : Pattern) (guard : d260159 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260158 p = 1 := by simpa only [d260159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31313 p hg
    simpa only [d260159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31315 (p : Pattern) (guard : d260160 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d260131 p = 1 := by simpa only [d260160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31115 p hg
    simpa only [d260160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260159 p = 1 := by simpa only [d260160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31314 p hg
    simpa only [d260160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31316 (p : Pattern) (guard : d1999 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31116 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31317 (p : Pattern) (guard : d2000 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31316 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31318 (p : Pattern) (guard : d30077 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31317 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31319 (p : Pattern) (guard : d30078 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31318 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31320 (p : Pattern) (guard : d257870 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31319 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31321 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30968 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31322 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31116 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31321 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31323 (p : Pattern) (guard : d257871 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31322 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31324 (p : Pattern) (guard : d257872 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31323 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31325 (p : Pattern) (guard : d257873 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31324 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31326 (p : Pattern) (guard : d257874 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31325 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31327 (p : Pattern) (guard : d257875 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31320 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31328 (p : Pattern) (guard : d257876 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31327 p hg
    simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d257876, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31329 (p : Pattern) (guard : d259291 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31330 (p : Pattern) (guard : d259292 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31329 p hg
    simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d259292, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31331 (p : Pattern) (guard : d259293 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31328 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31330 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31332 (p : Pattern) (guard : d259294 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31331 p hg
    simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259294, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31333 (p : Pattern) (guard : d259295 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31332 p hg
    simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259295, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31334 (p : Pattern) (guard : d259296 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31333 p hg
    simpa only [d259296, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31335 (p : Pattern) (guard : d259297 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259296 p = 1 := by simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31334 p hg
    simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259297, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31336 (p : Pattern) (guard : d2027 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31321 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31337 (p : Pattern) (guard : d2028 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31336 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31338 (p : Pattern) (guard : d2029 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31337 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31339 (p : Pattern) (guard : d2030 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31338 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31340 (p : Pattern) (guard : d27032 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31339 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31341 (p : Pattern) (guard : d259298 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31326 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31340 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31342 (p : Pattern) (guard : d259299 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31341 p hg
    simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d259299, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31343 (p : Pattern) (guard : d259300 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31340 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31344 (p : Pattern) (guard : d259301 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31343 p hg
    simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d259301, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31345 (p : Pattern) (guard : d259302 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31342 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31344 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31346 (p : Pattern) (guard : d259303 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31345 p hg
    simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259303, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31347 (p : Pattern) (guard : d259304 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31346 p hg
    simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259304, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31348 (p : Pattern) (guard : d259305 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31347 p hg
    simpa only [d259305, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31349 (p : Pattern) (guard : d259306 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259305 p = 1 := by simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31348 p hg
    simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259306, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31350 (p : Pattern) (guard : d259307 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259297 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31335 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259306 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31349 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31351 (p : Pattern) (guard : d259308 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31330 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31344 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31352 (p : Pattern) (guard : d259309 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31351 p hg
    simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259309, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31353 (p : Pattern) (guard : d259310 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31352 p hg
    simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259310, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31354 (p : Pattern) (guard : d259311 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31353 p hg
    simpa only [d259311, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31355 (p : Pattern) (guard : d259312 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259311 p = 1 := by simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31354 p hg
    simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259312, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31356 (p : Pattern) (guard : d259313 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31344 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30787 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31357 (p : Pattern) (guard : d259314 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31356 p hg
    simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d259314, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31358 (p : Pattern) (guard : d259315 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31357 p hg
    simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d259315, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31359 (p : Pattern) (guard : d259316 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31358 p hg
    simpa only [d259316, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31360 (p : Pattern) (guard : d259317 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259316 p = 1 := by simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31359 p hg
    simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d259317, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31361 (p : Pattern) (guard : d259318 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259312 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31355 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31360 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31362 (p : Pattern) (guard : d259319 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259307 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31350 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259318 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31361 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31363 (p : Pattern) (guard : d259320 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259306 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31349 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31360 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31364 (p : Pattern) (guard : d259321 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259317 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31360 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31365 (p : Pattern) (guard : d259322 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259320 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31363 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31364 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31366 (p : Pattern) (guard : d259323 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31362 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259322 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31365 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31367 (p : Pattern) (guard : d259324 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259323 p = 1 := by simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31366 p hg
    simpa only [d259324, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31368 (p : Pattern) (guard : d259325 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259324 p = 1 := by simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31367 p hg
    simpa only [d259325, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31369 (p : Pattern) (guard : d259326 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259321 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31364 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30796 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31370 (p : Pattern) (guard : d259327 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259322 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31365 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259326 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31369 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31371 (p : Pattern) (guard : d259328 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259327 p = 1 := by simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31370 p hg
    simpa only [d259328, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31372 (p : Pattern) (guard : d259329 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259328 p = 1 := by simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31371 p hg
    simpa only [d259329, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31373 (p : Pattern) (guard : d259330 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259325 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31368 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259329 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31372 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31374 (p : Pattern) (guard : d259331 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259329 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31372 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31375 (p : Pattern) (guard : d259332 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259330 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31373 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259331 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31374 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31376 (p : Pattern) (guard : d259333 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259332 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31375 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31377 (p : Pattern) (guard : d259334 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259333 p = 1 := by simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31376 p hg
    simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259334, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31378 (p : Pattern) (guard : d259335 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259334 p = 1 := by simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31377 p hg
    simpa only [d259335, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31379 (p : Pattern) (guard : d259336 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259331 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31374 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31380 (p : Pattern) (guard : d259337 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259336 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31379 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31381 (p : Pattern) (guard : d259338 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259337 p = 1 := by simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31380 p hg
    simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259338, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31382 (p : Pattern) (guard : d259339 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259338 p = 1 := by simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31381 p hg
    simpa only [d259339, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31383 (p : Pattern) (guard : d259340 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31378 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259339 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31382 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31384 (p : Pattern) (guard : d259341 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259340 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31383 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31385 (p : Pattern) (guard : d259342 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259341 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31384 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31386 (p : Pattern) (guard : d259343 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259342 p = 1 := by simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31385 p hg
    simpa only [d259343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31387 (p : Pattern) (guard : d259344 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259339 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31382 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31388 (p : Pattern) (guard : d259345 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259344 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31387 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31389 (p : Pattern) (guard : d259346 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259345 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31388 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31390 (p : Pattern) (guard : d259347 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259346 p = 1 := by simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31389 p hg
    simpa only [d259347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31391 (p : Pattern) (guard : d259348 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259343 p = 1 := by simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31386 p hg
    simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259347 p = 1 := by simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31390 p hg
    simpa only [d259348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31392 (p : Pattern) (guard : d259349 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259348 p = 1 := by simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31391 p hg
    simpa only [d259349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31393 (p : Pattern) (guard : d259350 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259349 p = 1 := by simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31392 p hg
    simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31394 (p : Pattern) (guard : d259351 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259350 p = 1 := by simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31393 p hg
    simpa only [d259351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31395 (p : Pattern) (guard : d259352 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259351 p = 1 := by simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31394 p hg
    simpa only [d259352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31396 (p : Pattern) (guard : d259353 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259352 p = 1 := by simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31395 p hg
    simpa only [d259353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31397 (p : Pattern) (guard : d259356 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259342 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31385 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31398 (p : Pattern) (guard : d259357 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259346 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31389 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31399 (p : Pattern) (guard : d259358 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259356 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31397 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259357 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31398 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31400 (p : Pattern) (guard : d259359 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259358 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31399 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31401 (p : Pattern) (guard : d259360 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259359 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31400 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31402 (p : Pattern) (guard : d259361 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259360 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31401 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31403 (p : Pattern) (guard : d259362 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259361 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31402 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31404 (p : Pattern) (guard : d259363 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259352 p = 1 := by simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31395 p hg
    simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259362 p = 1 := by simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31403 p hg
    simpa only [d259363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31405 (p : Pattern) (guard : d259364 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259353 p = 1 := by simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31396 p hg
    simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259363 p = 1 := by simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31404 p hg
    simpa only [d259364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31406 (p : Pattern) (guard : d259365 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259364 p = 1 := by simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31405 p hg
    simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31407 (p : Pattern) (guard : d260161 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259365 p = 1 := by simpa only [d260161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31406 p hg
    simpa only [d260161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31408 (p : Pattern) (guard : d260162 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260161 p = 1 := by simpa only [d260162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31407 p hg
    simpa only [d260162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31409 (p : Pattern) (guard : d1999 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31178 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31410 (p : Pattern) (guard : d2000 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31409 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31411 (p : Pattern) (guard : d30077 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31410 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31412 (p : Pattern) (guard : d30078 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31411 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31413 (p : Pattern) (guard : d257870 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31412 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31414 (p : Pattern) (guard : d2013 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31014 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31415 (p : Pattern) (guard : d2014 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31178 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31414 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31416 (p : Pattern) (guard : d257871 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31415 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31417 (p : Pattern) (guard : d257872 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31416 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31418 (p : Pattern) (guard : d257873 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31417 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31419 (p : Pattern) (guard : d257874 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31418 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31420 (p : Pattern) (guard : d257875 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31413 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257874 p = 1 := by simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31419 p hg
    simpa only [d257875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31421 (p : Pattern) (guard : d257876 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257875 p = 1 := by simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31420 p hg
    simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d257876, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31422 (p : Pattern) (guard : d259291 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31419 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31423 (p : Pattern) (guard : d259292 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31422 p hg
    simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31424 (p : Pattern) (guard : d259293 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31421 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31423 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31425 (p : Pattern) (guard : d259294 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31424 p hg
    simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31426 (p : Pattern) (guard : d259295 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31425 p hg
    simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31427 (p : Pattern) (guard : d259296 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31426 p hg
    simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31428 (p : Pattern) (guard : d259297 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259296 p = 1 := by simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31427 p hg
    simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31429 (p : Pattern) (guard : d2027 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31414 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31430 (p : Pattern) (guard : d2028 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31429 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31431 (p : Pattern) (guard : d2029 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31430 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31432 (p : Pattern) (guard : d2030 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31431 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31433 (p : Pattern) (guard : d27032 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31432 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31434 (p : Pattern) (guard : d259298 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31419 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31433 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31435 (p : Pattern) (guard : d259299 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31434 p hg
    simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31436 (p : Pattern) (guard : d259300 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31433 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31437 (p : Pattern) (guard : d259301 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31436 p hg
    simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31438 (p : Pattern) (guard : d259302 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31435 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31437 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31439 (p : Pattern) (guard : d259303 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31438 p hg
    simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31440 (p : Pattern) (guard : d259304 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31439 p hg
    simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31441 (p : Pattern) (guard : d259305 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31440 p hg
    simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31442 (p : Pattern) (guard : d259306 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259305 p = 1 := by simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31441 p hg
    simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31443 (p : Pattern) (guard : d259307 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259297 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31428 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259306 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31442 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31444 (p : Pattern) (guard : d259308 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31423 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31437 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31445 (p : Pattern) (guard : d259309 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31444 p hg
    simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31446 (p : Pattern) (guard : d259310 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31445 p hg
    simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31447 (p : Pattern) (guard : d259311 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31446 p hg
    simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31448 (p : Pattern) (guard : d259312 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259311 p = 1 := by simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31447 p hg
    simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31449 (p : Pattern) (guard : d259313 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31437 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31450 (p : Pattern) (guard : d259314 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31449 p hg
    simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31451 (p : Pattern) (guard : d259315 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31450 p hg
    simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31452 (p : Pattern) (guard : d259316 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31451 p hg
    simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31453 (p : Pattern) (guard : d259317 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259316 p = 1 := by simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31452 p hg
    simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31454 (p : Pattern) (guard : d259318 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259312 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31448 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31453 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31455 (p : Pattern) (guard : d259319 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259307 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31443 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259318 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31454 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31456 (p : Pattern) (guard : d259320 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259306 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31442 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31453 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31457 (p : Pattern) (guard : d259321 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259317 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31453 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31458 (p : Pattern) (guard : d259322 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259320 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31456 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31457 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31459 (p : Pattern) (guard : d259323 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31455 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259322 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31458 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31460 (p : Pattern) (guard : d259324 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259323 p = 1 := by simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31459 p hg
    simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31461 (p : Pattern) (guard : d259325 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259324 p = 1 := by simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31460 p hg
    simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31462 (p : Pattern) (guard : d259326 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259321 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31457 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31463 (p : Pattern) (guard : d259327 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259322 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31458 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259326 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31462 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31464 (p : Pattern) (guard : d259328 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259327 p = 1 := by simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31463 p hg
    simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31465 (p : Pattern) (guard : d259329 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259328 p = 1 := by simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31464 p hg
    simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31466 (p : Pattern) (guard : d259330 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259325 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31461 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259329 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31465 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31467 (p : Pattern) (guard : d259331 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259329 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31465 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31468 (p : Pattern) (guard : d259332 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259330 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31466 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259331 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31467 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31469 (p : Pattern) (guard : d259333 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259332 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31468 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31470 (p : Pattern) (guard : d259334 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259333 p = 1 := by simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31469 p hg
    simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31471 (p : Pattern) (guard : d259335 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259334 p = 1 := by simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31470 p hg
    simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31472 (p : Pattern) (guard : d259336 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259331 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31467 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31473 (p : Pattern) (guard : d259337 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259336 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31472 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31474 (p : Pattern) (guard : d259338 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259337 p = 1 := by simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31473 p hg
    simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31475 (p : Pattern) (guard : d259339 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259338 p = 1 := by simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31474 p hg
    simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31476 (p : Pattern) (guard : d259340 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31471 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259339 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31475 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31477 (p : Pattern) (guard : d259341 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259340 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31476 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31478 (p : Pattern) (guard : d259342 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259341 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31477 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31479 (p : Pattern) (guard : d259356 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259342 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31478 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31480 (p : Pattern) (guard : d259344 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259339 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31475 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31481 (p : Pattern) (guard : d259345 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259344 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31480 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31482 (p : Pattern) (guard : d259346 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259345 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31481 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31483 (p : Pattern) (guard : d259357 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259346 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31482 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31484 (p : Pattern) (guard : d259358 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259356 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31479 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259357 p = 1 := by simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31483 p hg
    simpa only [d259358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31485 (p : Pattern) (guard : d259359 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259358 p = 1 := by simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31484 p hg
    simpa only [d259359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31486 (p : Pattern) (guard : d259360 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259359 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31485 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31487 (p : Pattern) (guard : d259361 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259360 p = 1 := by simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31486 p hg
    simpa only [d259361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31488 (p : Pattern) (guard : d259362 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259361 p = 1 := by simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31487 p hg
    simpa only [d259362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31489 (p : Pattern) (guard : d260163 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260163, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260163, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259362 p = 1 := by simpa only [d260163, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31488 p hg
    simpa only [d260163, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31490 (p : Pattern) (guard : d260164 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260163 p = 1 := by simpa only [d260164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31489 p hg
    simpa only [d260164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31491 (p : Pattern) (guard : d260165 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260164 p = 1 := by simpa only [d260165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31490 p hg
    simpa only [d260165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31492 (p : Pattern) (guard : d260166 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260165 p = 1 := by simpa only [d260166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31491 p hg
    simpa only [d260166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31493 (p : Pattern) (guard : d260167 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260166 p = 1 := by simpa only [d260167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31492 p hg
    simpa only [d260167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31494 (p : Pattern) (guard : d260168 p = 1) : d47768 p ≤ (-2 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260162 p = 1 := by simpa only [d260168, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31408 p hg
    simpa only [d260168, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260167 p = 1 := by simpa only [d260168, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31493 p hg
    simpa only [d260168, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31495 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31233 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31496 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31495 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31497 (p : Pattern) (guard : d30077 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31496 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d30077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31498 (p : Pattern) (guard : d30078 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d30077 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31497 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d30078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31499 (p : Pattern) (guard : d257870 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d30078 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d257870, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
