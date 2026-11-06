/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8400 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8401 (p : Pattern) (guard : d4765 p = 1) : d965 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8400 p hg
    simpa only [d4765, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8402 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8403 (p : Pattern) (guard : d4765 p = 1) : d966 p ≤ (4 : Int) + d4305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d966, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d966, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d966, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d4765, d966, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8404 (p : Pattern) (guard : d4765 p = 1) : d967 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d967, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8401 p hg
    simpa only [d967, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d967, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d967, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8405 (p : Pattern) (guard : d4147 p = 1) : d53 p ≤ (4 : Int) + d53 p := by
  omega
theorem compare8406 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8407 (p : Pattern) (guard : d4765 p = 1) : d968 p ≤ (4 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d968, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8405 p hg
    simpa only [d4765, d968, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d968, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d4765, d968, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8408 (p : Pattern) (guard : d4765 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare8409 (p : Pattern) (guard : d4765 p = 1) : d969 p ≤ (4 : Int) + d4319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d969, d4319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8407 p hg
    simpa only [d969, d4319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d969, d4319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d969, d4319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8410 (p : Pattern) (guard : d4765 p = 1) : d970 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d970, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8404 p hg
    simpa only [d970, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d970, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d970, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8411 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8412 (p : Pattern) (guard : d4765 p = 1) : d971 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d971, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d971, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d971, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8411 p hg
    simpa only [d4765, d971, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8413 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (4 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8383 p hg
    simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d20, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8414 (p : Pattern) (guard : d4147 p = 1) : d808 p ≤ (4 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d4147, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8415 (p : Pattern) (guard : d4765 p = 1) : d972 p ≤ (4 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d972, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d4765, d972, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d972, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d4765, d972, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8416 (p : Pattern) (guard : d4765 p = 1) : d973 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d973, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d973, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d973, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d973, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8417 (p : Pattern) (guard : d4765 p = 1) : d972 p ≤ (4 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d972, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d4765, d972, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d972, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d972, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8418 (p : Pattern) (guard : d4765 p = 1) : d974 p ≤ (4 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d974, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8417 p hg
    simpa only [d974, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d974, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d974, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8419 (p : Pattern) (guard : d4765 p = 1) : d975 p ≤ (4 : Int) + d4321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d975, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8416 p hg
    simpa only [d975, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d975, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d975, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8420 (p : Pattern) (guard : d4765 p = 1) : d976 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d976, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d976, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d976, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8419 p hg
    simpa only [d976, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8421 (p : Pattern) (guard : d4765 p = 1) : d977 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d977, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8399 p hg
    simpa only [d977, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d977, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8420 p hg
    simpa only [d977, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8422 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8423 (p : Pattern) (guard : d4765 p = 1) : d978 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8422 p hg
    simpa only [d4765, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8424 (p : Pattern) (guard : d4765 p = 1) : d979 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d979, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8423 p hg
    simpa only [d979, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d979, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d979, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8425 (p : Pattern) (guard : d4765 p = 1) : d980 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d980, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8424 p hg
    simpa only [d980, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d980, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d980, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8426 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8427 (p : Pattern) (guard : d4765 p = 1) : d981 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d981, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d981, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d981, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8426 p hg
    simpa only [d4765, d981, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8428 (p : Pattern) (guard : d4765 p = 1) : d982 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d982, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d982, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d982, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d982, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8429 (p : Pattern) (guard : d4765 p = 1) : d983 p ≤ (4 : Int) + d4321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d983, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8428 p hg
    simpa only [d983, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d983, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d983, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8430 (p : Pattern) (guard : d4765 p = 1) : d984 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d984, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d984, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d984, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8429 p hg
    simpa only [d984, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8431 (p : Pattern) (guard : d4765 p = 1) : d985 p ≤ (4 : Int) + d4324 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d985, d4324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d4765, d985, d4324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d985, d4324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d4765, d985, d4324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8432 (p : Pattern) (guard : d4765 p = 1) : d91 p ≤ (4 : Int) + d4160 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d4765, d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8433 (p : Pattern) (guard : d4765 p = 1) : d986 p ≤ (4 : Int) + d4325 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d986, d4325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8431 p hg
    simpa only [d986, d4325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d986, d4325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d986, d4325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8434 (p : Pattern) (guard : d4765 p = 1) : d93 p ≤ (4 : Int) + d4161 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8435 (p : Pattern) (guard : d4765 p = 1) : d987 p ≤ (4 : Int) + d4326 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d987, d4326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8433 p hg
    simpa only [d987, d4326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d987, d4326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d987, d4326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8436 (p : Pattern) (guard : d4765 p = 1) : d95 p ≤ (4 : Int) + d4162 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8437 (p : Pattern) (guard : d4765 p = 1) : d988 p ≤ (4 : Int) + d4327 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d988, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8435 p hg
    simpa only [d988, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d988, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8436 p hg
    simpa only [d988, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8438 (p : Pattern) (guard : d4765 p = 1) : d989 p ≤ (4 : Int) + d4328 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d989, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8430 p hg
    simpa only [d989, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d989, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8437 p hg
    simpa only [d989, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8439 (p : Pattern) (guard : d4765 p = 1) : d990 p ≤ (4 : Int) + d4329 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d990, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8421 p hg
    simpa only [d990, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d990, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8438 p hg
    simpa only [d990, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8440 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8441 (p : Pattern) (guard : d4765 p = 1) : d991 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8440 p hg
    simpa only [d4765, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8442 (p : Pattern) (guard : d4765 p = 1) : d992 p ≤ (4 : Int) + d4305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d992, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d4765, d992, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d992, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d4765, d992, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8443 (p : Pattern) (guard : d4765 p = 1) : d993 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d993, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8441 p hg
    simpa only [d993, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d993, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8442 p hg
    simpa only [d993, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8444 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8445 (p : Pattern) (guard : d4765 p = 1) : d994 p ≤ (4 : Int) + d4307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d994, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d4765, d994, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d994, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8444 p hg
    simpa only [d4765, d994, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8446 (p : Pattern) (guard : d4765 p = 1) : d995 p ≤ (4 : Int) + d4309 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d995, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8445 p hg
    simpa only [d995, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d995, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d995, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8447 (p : Pattern) (guard : d4765 p = 1) : d996 p ≤ (4 : Int) + d4310 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d996, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d996, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d996, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d996, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8448 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8449 (p : Pattern) (guard : d4765 p = 1) : d997 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d997, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d997, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d997, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8448 p hg
    simpa only [d4765, d997, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8450 (p : Pattern) (guard : d4765 p = 1) : d960 p ≤ (4 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d960, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8386 p hg
    simpa only [d4765, d960, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d960, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d4765, d960, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8451 (p : Pattern) (guard : d4765 p = 1) : d998 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d998, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8449 p hg
    simpa only [d998, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d998, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d998, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8452 (p : Pattern) (guard : d4765 p = 1) : d999 p ≤ (4 : Int) + d4317 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d999, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8451 p hg
    simpa only [d999, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d999, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d999, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8453 (p : Pattern) (guard : d4765 p = 1) : d1000 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1000, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8447 p hg
    simpa only [d1000, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1000, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8452 p hg
    simpa only [d1000, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8454 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8455 (p : Pattern) (guard : d4765 p = 1) : d1001 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d4765, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8456 (p : Pattern) (guard : d4765 p = 1) : d1002 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1002, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d1002, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1002, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d1002, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8457 (p : Pattern) (guard : d4765 p = 1) : d1003 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1003, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8456 p hg
    simpa only [d1003, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1003, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d1003, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8458 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8459 (p : Pattern) (guard : d4765 p = 1) : d966 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d966, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d966, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d966, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8458 p hg
    simpa only [d4765, d966, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8460 (p : Pattern) (guard : d4765 p = 1) : d1004 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1004, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8459 p hg
    simpa only [d1004, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1004, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d1004, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8461 (p : Pattern) (guard : d4765 p = 1) : d1005 p ≤ (4 : Int) + d4321 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1005, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8460 p hg
    simpa only [d1005, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1005, d4321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d1005, d4321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8462 (p : Pattern) (guard : d4765 p = 1) : d1006 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1006, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8457 p hg
    simpa only [d1006, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1006, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8461 p hg
    simpa only [d1006, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8463 (p : Pattern) (guard : d4765 p = 1) : d1007 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1007, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8453 p hg
    simpa only [d1007, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1007, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8462 p hg
    simpa only [d1007, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8464 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8465 (p : Pattern) (guard : d4765 p = 1) : d1008 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8464 p hg
    simpa only [d4765, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8466 (p : Pattern) (guard : d4765 p = 1) : d1009 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1009, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8465 p hg
    simpa only [d1009, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1009, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d1009, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8467 (p : Pattern) (guard : d4765 p = 1) : d1010 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1010, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8466 p hg
    simpa only [d1010, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1010, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d1010, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8468 (p : Pattern) (guard : d4765 p = 1) : d1011 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1011, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8467 p hg
    simpa only [d1011, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1011, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8461 p hg
    simpa only [d1011, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8469 (p : Pattern) (guard : d4765 p = 1) : d1012 p ≤ (4 : Int) + d4330 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1012, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d1012, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1012, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1012, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8470 (p : Pattern) (guard : d4765 p = 1) : d1013 p ≤ (4 : Int) + d4331 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1013, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8463 p hg
    simpa only [d1013, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1013, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8469 p hg
    simpa only [d1013, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8471 (p : Pattern) (guard : d4765 p = 1) : d1014 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1014, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8439 p hg
    simpa only [d1014, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1014, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8470 p hg
    simpa only [d1014, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8472 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8473 (p : Pattern) (guard : d4765 p = 1) : d1015 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8472 p hg
    simpa only [d4765, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8474 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8475 (p : Pattern) (guard : d4765 p = 1) : d1016 p ≤ (4 : Int) + d4305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1016, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d4765, d1016, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1016, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8474 p hg
    simpa only [d4765, d1016, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8476 (p : Pattern) (guard : d4765 p = 1) : d1017 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1017, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8473 p hg
    simpa only [d1017, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1017, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8475 p hg
    simpa only [d1017, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8477 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8478 (p : Pattern) (guard : d4765 p = 1) : d1018 p ≤ (4 : Int) + d4307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1018, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d4765, d1018, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1018, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8477 p hg
    simpa only [d4765, d1018, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8479 (p : Pattern) (guard : d4765 p = 1) : d1019 p ≤ (4 : Int) + d4309 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1019, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8478 p hg
    simpa only [d1019, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1019, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d1019, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8480 (p : Pattern) (guard : d4765 p = 1) : d1020 p ≤ (4 : Int) + d4310 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1020, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8476 p hg
    simpa only [d1020, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1020, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8479 p hg
    simpa only [d1020, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8481 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8482 (p : Pattern) (guard : d4765 p = 1) : d1021 p ≤ (4 : Int) + d4311 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1021, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d4765, d1021, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1021, d4311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8481 p hg
    simpa only [d4765, d1021, d4311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8483 (p : Pattern) (guard : d4765 p = 1) : d1022 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1022, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8482 p hg
    simpa only [d1022, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1022, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d1022, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8484 (p : Pattern) (guard : d4765 p = 1) : d1023 p ≤ (4 : Int) + d4317 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1023, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8483 p hg
    simpa only [d1023, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1023, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d1023, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8485 (p : Pattern) (guard : d4765 p = 1) : d1024 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1024, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8480 p hg
    simpa only [d1024, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1024, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8484 p hg
    simpa only [d1024, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8486 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8487 (p : Pattern) (guard : d4765 p = 1) : d1025 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d4765, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8486 p hg
    simpa only [d4765, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8488 (p : Pattern) (guard : d4765 p = 1) : d1026 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1026, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8487 p hg
    simpa only [d1026, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1026, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d1026, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8489 (p : Pattern) (guard : d4765 p = 1) : d1027 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1027, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8488 p hg
    simpa only [d1027, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1027, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d1027, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8490 (p : Pattern) (guard : d4765 p = 1) : d1028 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1028, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8489 p hg
    simpa only [d1028, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1028, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8461 p hg
    simpa only [d1028, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8491 (p : Pattern) (guard : d4765 p = 1) : d1029 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1029, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8485 p hg
    simpa only [d1029, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1029, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8490 p hg
    simpa only [d1029, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8492 (p : Pattern) (guard : d4765 p = 1) : d1030 p ≤ (4 : Int) + d4328 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1030, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8420 p hg
    simpa only [d1030, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1030, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8437 p hg
    simpa only [d1030, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8493 (p : Pattern) (guard : d4765 p = 1) : d1031 p ≤ (4 : Int) + d4329 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1031, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8491 p hg
    simpa only [d1031, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1031, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8492 p hg
    simpa only [d1031, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8494 (p : Pattern) (guard : d4765 p = 1) : d1032 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1032, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8423 p hg
    simpa only [d1032, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1032, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8442 p hg
    simpa only [d1032, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8495 (p : Pattern) (guard : d4765 p = 1) : d1033 p ≤ (4 : Int) + d4310 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1033, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8494 p hg
    simpa only [d1033, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1033, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d1033, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8496 (p : Pattern) (guard : d4765 p = 1) : d1034 p ≤ (4 : Int) + d4313 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1034, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d1034, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1034, d4313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d1034, d4313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8497 (p : Pattern) (guard : d4765 p = 1) : d1035 p ≤ (4 : Int) + d4317 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1035, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d1035, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1035, d4317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d1035, d4317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8498 (p : Pattern) (guard : d4765 p = 1) : d1036 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1036, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8495 p hg
    simpa only [d1036, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1036, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d1036, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8499 (p : Pattern) (guard : d4765 p = 1) : d1037 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1037, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8498 p hg
    simpa only [d1037, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1037, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8462 p hg
    simpa only [d1037, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8500 (p : Pattern) (guard : d4765 p = 1) : d1038 p ≤ (4 : Int) + d4330 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1038, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8462 p hg
    simpa only [d1038, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1038, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d1038, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8501 (p : Pattern) (guard : d4765 p = 1) : d1039 p ≤ (4 : Int) + d4331 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1039, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8499 p hg
    simpa only [d1039, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1039, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8500 p hg
    simpa only [d1039, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8502 (p : Pattern) (guard : d4765 p = 1) : d1040 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1040, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8493 p hg
    simpa only [d1040, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1040, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d1040, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8503 (p : Pattern) (guard : d4765 p = 1) : d1041 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8502 p hg
    simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8504 (p : Pattern) (guard : d0 p = 1) : d355 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8505 (p : Pattern) (guard : d4765 p = 1) : d1042 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8504 p hg
    simpa only [d4765, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8506 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d118, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8507 (p : Pattern) (guard : d4147 p = 1) : d1043 p ≤ (4 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8506 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8508 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8509 (p : Pattern) (guard : d4765 p = 1) : d1044 p ≤ (4 : Int) + d4333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1044, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8507 p hg
    simpa only [d4765, d1044, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1044, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8508 p hg
    simpa only [d4765, d1044, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8510 (p : Pattern) (guard : d4765 p = 1) : d1045 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1045, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8505 p hg
    simpa only [d1045, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1045, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8509 p hg
    simpa only [d1045, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8511 (p : Pattern) (guard : d4147 p = 1) : d118 p ≤ (4 : Int) + d118 p := by
  omega
theorem compare8512 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (4 : Int) + d124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8513 (p : Pattern) (guard : d4765 p = 1) : d1046 p ≤ (4 : Int) + d4335 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1046, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d4765, d1046, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1046, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8512 p hg
    simpa only [d4765, d1046, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8514 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8515 (p : Pattern) (guard : d4765 p = 1) : d1047 p ≤ (4 : Int) + d4336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1047, d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d4765, d1047, d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1047, d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8514 p hg
    simpa only [d4765, d1047, d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8516 (p : Pattern) (guard : d4765 p = 1) : d1048 p ≤ (4 : Int) + d4337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1048, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8513 p hg
    simpa only [d1048, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1048, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8515 p hg
    simpa only [d1048, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8517 (p : Pattern) (guard : d4765 p = 1) : d1049 p ≤ (4 : Int) + d4338 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1049, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8510 p hg
    simpa only [d1049, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1049, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d1049, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8518 (p : Pattern) (guard : d4147 p = 1) : d133 p ≤ (4 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8519 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8520 (p : Pattern) (guard : d4765 p = 1) : d1050 p ≤ (4 : Int) + d4339 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1050, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d4765, d1050, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1050, d4339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8519 p hg
    simpa only [d4765, d1050, d4339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8521 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (4 : Int) + d3 p := by
  change (5 : Int) ≤ (4 : Int) + 3
  decide
theorem compare8522 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (4 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d106, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8523 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (4 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8522 p hg
    simpa only [d107, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8524 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (4 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d108, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8525 (p : Pattern) (guard : d1 p = 1) : d861 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d861, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8526 (p : Pattern) (guard : d4147 p = 1) : d862 p ≤ (4 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8525 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8527 (p : Pattern) (guard : d4765 p = 1) : d1051 p ≤ (4 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1051, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d4765, d1051, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1051, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1051, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8528 (p : Pattern) (guard : d4765 p = 1) : d1052 p ≤ (4 : Int) + d4340 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1052, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d1052, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1052, d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8527 p hg
    simpa only [d1052, d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8529 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8530 (p : Pattern) (guard : d4765 p = 1) : d1051 p ≤ (4 : Int) + d4341 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1051, d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d4765, d1051, d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1051, d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d4765, d1051, d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8531 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (4 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8532 (p : Pattern) (guard : d1 p = 1) : d229 p ≤ (4 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d229, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d229, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d229, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d229, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8533 (p : Pattern) (guard : d4147 p = 1) : d1053 p ≤ (4 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8531 p hg
    simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8532 p hg
    simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8534 (p : Pattern) (guard : d4765 p = 1) : d1054 p ≤ (4 : Int) + d4342 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1054, d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8533 p hg
    simpa only [d4765, d1054, d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1054, d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4765, d1054, d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8535 (p : Pattern) (guard : d4765 p = 1) : d1055 p ≤ (4 : Int) + d4343 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1055, d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8530 p hg
    simpa only [d1055, d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1055, d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d1055, d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8536 (p : Pattern) (guard : d4765 p = 1) : d1056 p ≤ (4 : Int) + d4344 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1056, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8528 p hg
    simpa only [d1056, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1056, d4344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8535 p hg
    simpa only [d1056, d4344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8537 (p : Pattern) (guard : d4765 p = 1) : d1057 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1057, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8517 p hg
    simpa only [d1057, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1057, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8536 p hg
    simpa only [d1057, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8538 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8539 (p : Pattern) (guard : d4765 p = 1) : d1058 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d4765, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8538 p hg
    simpa only [d4765, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
