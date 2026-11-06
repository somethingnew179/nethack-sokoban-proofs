/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11340 (p : Pattern) (guard : d1984 p = 1) : d688 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11326 p hg
    simpa only [d1984, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11339 p hg
    simpa only [d1984, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11341 (p : Pattern) (guard : d1976 p = 1) : d673 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11301 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11342 (p : Pattern) (guard : d1977 p = 1) : d673 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11341 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11343 (p : Pattern) (guard : d1978 p = 1) : d674 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11318 p hg
    simpa only [d1978, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11342 p hg
    simpa only [d1978, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11344 (p : Pattern) (guard : d0 p = 1) : d659 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11345 (p : Pattern) (guard : d1981 p = 1) : d659 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11308 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11344 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11346 (p : Pattern) (guard : d1982 p = 1) : d689 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11295 p hg
    simpa only [d1982, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11345 p hg
    simpa only [d1982, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11347 (p : Pattern) (guard : d1983 p = 1) : d690 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d690, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11343 p hg
    simpa only [d1983, d690, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d690, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11346 p hg
    simpa only [d1983, d690, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11348 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11349 (p : Pattern) (guard : d1961 p = 1) : d653 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11239 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11348 p hg
    simpa only [d1961, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11350 (p : Pattern) (guard : d1966 p = 1) : d656 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d656, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11349 p hg
    simpa only [d1966, d656, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d656, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d1966, d656, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11351 (p : Pattern) (guard : d1971 p = 1) : d656 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11350 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11352 (p : Pattern) (guard : d0 p = 1) : d656 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11353 (p : Pattern) (guard : d1976 p = 1) : d656 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11351 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11352 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11354 (p : Pattern) (guard : d0 p = 1) : d668 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11355 (p : Pattern) (guard : d1981 p = 1) : d669 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11353 p hg
    simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11354 p hg
    simpa only [d1981, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11356 (p : Pattern) (guard : d1982 p = 1) : d691 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d1982, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11355 p hg
    simpa only [d1982, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11357 (p : Pattern) (guard : d1986 p = 1) : d692 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d1986, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11358 (p : Pattern) (guard : d1987 p = 1) : d693 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d693, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11356 p hg
    simpa only [d1987, d693, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d693, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11357 p hg
    simpa only [d1987, d693, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11359 (p : Pattern) (guard : d1988 p = 1) : d694 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11347 p hg
    simpa only [d1988, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11358 p hg
    simpa only [d1988, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11360 (p : Pattern) (guard : d1989 p = 1) : d695 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11340 p hg
    simpa only [d1989, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11359 p hg
    simpa only [d1989, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11361 (p : Pattern) (guard : d1990 p = 1) : d696 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11314 p hg
    simpa only [d1990, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11360 p hg
    simpa only [d1990, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11362 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11363 (p : Pattern) (guard : d1 p = 1) : d743 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11362 p hg
    simpa only [d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11364 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11365 (p : Pattern) (guard : d1 p = 1) : d744 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11366 (p : Pattern) (guard : d1 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11363 p hg
    simpa only [d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11365 p hg
    simpa only [d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11367 (p : Pattern) (guard : d1944 p = 1) : d744 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d1944, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11368 (p : Pattern) (guard : d1945 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11363 p hg
    simpa only [d1945, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11367 p hg
    simpa only [d1945, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11369 (p : Pattern) (guard : d1946 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11366 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11368 p hg
    simpa only [d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11370 (p : Pattern) (guard : d1 p = 1) : d743 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11371 (p : Pattern) (guard : d1944 p = 1) : d744 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1944, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1944, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11372 (p : Pattern) (guard : d1945 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11370 p hg
    simpa only [d1945, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d1945, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11373 (p : Pattern) (guard : d1943 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11374 (p : Pattern) (guard : d1944 p = 1) : d746 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d1944, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11373 p hg
    simpa only [d1944, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11375 (p : Pattern) (guard : d1943 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11376 (p : Pattern) (guard : d1947 p = 1) : d747 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11375 p hg
    simpa only [d1947, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11377 (p : Pattern) (guard : d1948 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11374 p hg
    simpa only [d1948, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11376 p hg
    simpa only [d1948, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11378 (p : Pattern) (guard : d1949 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11372 p hg
    simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11377 p hg
    simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11379 (p : Pattern) (guard : d1950 p = 1) : d750 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11369 p hg
    simpa only [d1950, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11378 p hg
    simpa only [d1950, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11380 (p : Pattern) (guard : d1944 p = 1) : d743 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1944, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1944, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11381 (p : Pattern) (guard : d1943 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11382 (p : Pattern) (guard : d1947 p = 1) : d744 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11381 p hg
    simpa only [d1947, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11383 (p : Pattern) (guard : d1948 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11380 p hg
    simpa only [d1948, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11382 p hg
    simpa only [d1948, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11384 (p : Pattern) (guard : d1949 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11372 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11383 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11385 (p : Pattern) (guard : d1293 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11386 (p : Pattern) (guard : d1947 p = 1) : d746 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11375 p hg
    simpa only [d1947, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d1947, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11387 (p : Pattern) (guard : d1293 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11388 (p : Pattern) (guard : d1951 p = 1) : d747 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11387 p hg
    simpa only [d1951, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11389 (p : Pattern) (guard : d1952 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11386 p hg
    simpa only [d1952, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11388 p hg
    simpa only [d1952, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11390 (p : Pattern) (guard : d1953 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11383 p hg
    simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11389 p hg
    simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11391 (p : Pattern) (guard : d1954 p = 1) : d750 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11384 p hg
    simpa only [d1954, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d1954, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11392 (p : Pattern) (guard : d1955 p = 1) : d750 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11379 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11391 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11393 (p : Pattern) (guard : d1 p = 1) : d743 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11394 (p : Pattern) (guard : d1945 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11393 p hg
    simpa only [d1945, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1944 p = 1 := by simpa only [d1945, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11371 p hg
    simpa only [d1945, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11395 (p : Pattern) (guard : d1944 p = 1) : d743 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11364 p hg
    simpa only [d1944, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1944, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11396 (p : Pattern) (guard : d1948 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d1948, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11382 p hg
    simpa only [d1948, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11397 (p : Pattern) (guard : d1949 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11396 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11398 (p : Pattern) (guard : d1954 p = 1) : d750 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11397 p hg
    simpa only [d1954, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d1954, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11399 (p : Pattern) (guard : d1948 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11380 p hg
    simpa only [d1948, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d1948, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11400 (p : Pattern) (guard : d1947 p = 1) : d743 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11381 p hg
    simpa only [d1947, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1947, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11401 (p : Pattern) (guard : d1952 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11400 p hg
    simpa only [d1952, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9795 p hg
    simpa only [d1952, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11402 (p : Pattern) (guard : d1953 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11399 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11401 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11403 (p : Pattern) (guard : d1951 p = 1) : d746 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11387 p hg
    simpa only [d1951, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d1951, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11404 (p : Pattern) (guard : d1956 p = 1) : d752 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11403 p hg
    simpa only [d1956, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d1956, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11405 (p : Pattern) (guard : d1957 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11401 p hg
    simpa only [d1957, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11404 p hg
    simpa only [d1957, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11406 (p : Pattern) (guard : d1958 p = 1) : d754 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11402 p hg
    simpa only [d1958, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11405 p hg
    simpa only [d1958, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11407 (p : Pattern) (guard : d1959 p = 1) : d755 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11398 p hg
    simpa only [d1959, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11406 p hg
    simpa only [d1959, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11408 (p : Pattern) (guard : d1960 p = 1) : d756 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11392 p hg
    simpa only [d1960, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11407 p hg
    simpa only [d1960, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11409 (p : Pattern) (guard : d1944 p = 1) : d743 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11362 p hg
    simpa only [d1944, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1944, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11410 (p : Pattern) (guard : d1943 p = 1) : d3 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11411 (p : Pattern) (guard : d1947 p = 1) : d744 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11410 p hg
    simpa only [d1947, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11412 (p : Pattern) (guard : d1948 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11409 p hg
    simpa only [d1948, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11411 p hg
    simpa only [d1948, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11413 (p : Pattern) (guard : d1949 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11368 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11412 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11414 (p : Pattern) (guard : d1954 p = 1) : d750 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11413 p hg
    simpa only [d1954, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d1954, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11415 (p : Pattern) (guard : d1959 p = 1) : d755 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11414 p hg
    simpa only [d1959, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11406 p hg
    simpa only [d1959, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11416 (p : Pattern) (guard : d1948 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11395 p hg
    simpa only [d1948, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d1948, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11417 (p : Pattern) (guard : d1947 p = 1) : d743 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11410 p hg
    simpa only [d1947, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1947, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11418 (p : Pattern) (guard : d1952 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11417 p hg
    simpa only [d1952, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9795 p hg
    simpa only [d1952, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11419 (p : Pattern) (guard : d1953 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11416 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11418 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11420 (p : Pattern) (guard : d1958 p = 1) : d754 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11419 p hg
    simpa only [d1958, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11405 p hg
    simpa only [d1958, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11421 (p : Pattern) (guard : d1293 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11422 (p : Pattern) (guard : d1951 p = 1) : d743 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11421 p hg
    simpa only [d1951, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1951, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11423 (p : Pattern) (guard : d1956 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11422 p hg
    simpa only [d1956, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d1956, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11424 (p : Pattern) (guard : d1957 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11401 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11423 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11425 (p : Pattern) (guard : d0 p = 1) : d752 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11426 (p : Pattern) (guard : d1961 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11423 p hg
    simpa only [d1961, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11425 p hg
    simpa only [d1961, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11427 (p : Pattern) (guard : d1962 p = 1) : d754 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11424 p hg
    simpa only [d1962, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d1962, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11428 (p : Pattern) (guard : d1963 p = 1) : d754 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11420 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11427 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11429 (p : Pattern) (guard : d1964 p = 1) : d757 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11415 p hg
    simpa only [d1964, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11428 p hg
    simpa only [d1964, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11430 (p : Pattern) (guard : d1965 p = 1) : d758 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11408 p hg
    simpa only [d1965, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11429 p hg
    simpa only [d1965, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11431 (p : Pattern) (guard : d1951 p = 1) : d744 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11421 p hg
    simpa only [d1951, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11432 (p : Pattern) (guard : d1952 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11400 p hg
    simpa only [d1952, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11431 p hg
    simpa only [d1952, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11433 (p : Pattern) (guard : d1953 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11383 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11434 (p : Pattern) (guard : d0 p = 1) : d747 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11435 (p : Pattern) (guard : d1956 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11403 p hg
    simpa only [d1956, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11434 p hg
    simpa only [d1956, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11436 (p : Pattern) (guard : d1957 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11437 (p : Pattern) (guard : d1958 p = 1) : d750 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11433 p hg
    simpa only [d1958, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1958, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11438 (p : Pattern) (guard : d1959 p = 1) : d750 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11414 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11437 p hg
    simpa only [d1959, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11439 (p : Pattern) (guard : d1952 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11417 p hg
    simpa only [d1952, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11431 p hg
    simpa only [d1952, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11440 (p : Pattern) (guard : d1953 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11396 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11441 (p : Pattern) (guard : d1958 p = 1) : d750 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11440 p hg
    simpa only [d1958, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1958, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11442 (p : Pattern) (guard : d1963 p = 1) : d755 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11441 p hg
    simpa only [d1963, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11427 p hg
    simpa only [d1963, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11443 (p : Pattern) (guard : d1964 p = 1) : d756 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11438 p hg
    simpa only [d1964, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11442 p hg
    simpa only [d1964, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11444 (p : Pattern) (guard : d1943 p = 1) : d3 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11445 (p : Pattern) (guard : d1947 p = 1) : d743 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11444 p hg
    simpa only [d1947, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1947, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11446 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d985, d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d985, d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11447 (p : Pattern) (guard : d1293 p = 1) : d3 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11446 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11448 (p : Pattern) (guard : d1951 p = 1) : d744 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d1951, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d744, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11449 (p : Pattern) (guard : d1952 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11445 p hg
    simpa only [d1952, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11448 p hg
    simpa only [d1952, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11450 (p : Pattern) (guard : d1953 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11412 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11449 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11451 (p : Pattern) (guard : d1958 p = 1) : d750 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11450 p hg
    simpa only [d1958, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1958, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11452 (p : Pattern) (guard : d1963 p = 1) : d755 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d1963, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11427 p hg
    simpa only [d1963, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11453 (p : Pattern) (guard : d1951 p = 1) : d743 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11447 p hg
    simpa only [d1951, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1951, d743, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11454 (p : Pattern) (guard : d1956 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11453 p hg
    simpa only [d1956, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d1956, d751, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11455 (p : Pattern) (guard : d1957 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11418 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11454 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11456 (p : Pattern) (guard : d1962 p = 1) : d754 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11455 p hg
    simpa only [d1962, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d1962, d754, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11457 (p : Pattern) (guard : d0 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11458 (p : Pattern) (guard : d1961 p = 1) : d751 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11423 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11457 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11459 (p : Pattern) (guard : d1966 p = 1) : d754 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d1966, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1966, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11460 (p : Pattern) (guard : d1967 p = 1) : d754 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11456 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11461 (p : Pattern) (guard : d1968 p = 1) : d757 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d1968, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d1968, d757, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11462 (p : Pattern) (guard : d1969 p = 1) : d758 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11443 p hg
    simpa only [d1969, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d1969, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11463 (p : Pattern) (guard : d1970 p = 1) : d758 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11430 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11464 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11465 (p : Pattern) (guard : d1944 p = 1) : d746 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d1944, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11373 p hg
    simpa only [d1944, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11466 (p : Pattern) (guard : d1948 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d1948, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11376 p hg
    simpa only [d1948, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11467 (p : Pattern) (guard : d1949 p = 1) : d749 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11394 p hg
    simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11466 p hg
    simpa only [d1949, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11468 (p : Pattern) (guard : d1954 p = 1) : d749 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d1954, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11469 (p : Pattern) (guard : d1958 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11390 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11470 (p : Pattern) (guard : d1959 p = 1) : d749 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11469 p hg
    simpa only [d1959, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11471 (p : Pattern) (guard : d1962 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11405 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11472 (p : Pattern) (guard : d1963 p = 1) : d759 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11469 p hg
    simpa only [d1963, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1963, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11473 (p : Pattern) (guard : d1964 p = 1) : d760 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11470 p hg
    simpa only [d1964, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11472 p hg
    simpa only [d1964, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11474 (p : Pattern) (guard : d1943 p = 1) : d9 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d1943, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11475 (p : Pattern) (guard : d1947 p = 1) : d746 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11474 p hg
    simpa only [d1947, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d1947, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11476 (p : Pattern) (guard : d1952 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11475 p hg
    simpa only [d1952, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11388 p hg
    simpa only [d1952, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11477 (p : Pattern) (guard : d1953 p = 1) : d749 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11396 p hg
    simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11476 p hg
    simpa only [d1953, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11478 (p : Pattern) (guard : d1958 p = 1) : d749 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1958, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11479 (p : Pattern) (guard : d1963 p = 1) : d759 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11478 p hg
    simpa only [d1963, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1963, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
