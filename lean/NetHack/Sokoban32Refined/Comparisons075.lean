/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons074
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10500 (p : Pattern) (guard : d1966 p = 1) : d553 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10442 p hg
    simpa only [d1966, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10499 p hg
    simpa only [d1966, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10501 (p : Pattern) (guard : d1967 p = 1) : d626 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d626, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10405 p hg
    simpa only [d1967, d626, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d626, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10500 p hg
    simpa only [d1967, d626, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10502 (p : Pattern) (guard : d0 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10503 (p : Pattern) (guard : d1966 p = 1) : d543 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10446 p hg
    simpa only [d1966, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1966, d543, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10504 (p : Pattern) (guard : d0 p = 1) : d548 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10505 (p : Pattern) (guard : d1971 p = 1) : d549 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10503 p hg
    simpa only [d1971, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10504 p hg
    simpa only [d1971, d549, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10506 (p : Pattern) (guard : d1972 p = 1) : d627 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d627, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10501 p hg
    simpa only [d1972, d627, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d627, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10505 p hg
    simpa only [d1972, d627, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10507 (p : Pattern) (guard : d1973 p = 1) : d628 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10402 p hg
    simpa only [d1973, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10506 p hg
    simpa only [d1973, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10508 (p : Pattern) (guard : d1974 p = 1) : d629 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10346 p hg
    simpa only [d1974, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10507 p hg
    simpa only [d1974, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10509 (p : Pattern) (guard : d1966 p = 1) : d552 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10499 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10510 (p : Pattern) (guard : d1967 p = 1) : d559 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10416 p hg
    simpa only [d1967, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10509 p hg
    simpa only [d1967, d559, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10511 (p : Pattern) (guard : d1966 p = 1) : d541 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10512 (p : Pattern) (guard : d1971 p = 1) : d557 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d1971, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d1971, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10513 (p : Pattern) (guard : d1972 p = 1) : d560 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10510 p hg
    simpa only [d1972, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10512 p hg
    simpa only [d1972, d560, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10514 (p : Pattern) (guard : d1973 p = 1) : d561 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10415 p hg
    simpa only [d1973, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10513 p hg
    simpa only [d1973, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10515 (p : Pattern) (guard : d0 p = 1) : d569 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10516 (p : Pattern) (guard : d1971 p = 1) : d570 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10426 p hg
    simpa only [d1971, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d1971, d570, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10517 (p : Pattern) (guard : d1976 p = 1) : d571 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10516 p hg
    simpa only [d1976, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d1976, d571, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10518 (p : Pattern) (guard : d1977 p = 1) : d572 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10423 p hg
    simpa only [d1977, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10517 p hg
    simpa only [d1977, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10519 (p : Pattern) (guard : d1978 p = 1) : d573 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d1978, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10518 p hg
    simpa only [d1978, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10520 (p : Pattern) (guard : d1979 p = 1) : d630 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d630, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10508 p hg
    simpa only [d1979, d630, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d630, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10519 p hg
    simpa only [d1979, d630, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10521 (p : Pattern) (guard : d1966 p = 1) : d543 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10477 p hg
    simpa only [d1966, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1966, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10522 (p : Pattern) (guard : d1967 p = 1) : d631 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10405 p hg
    simpa only [d1967, d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10521 p hg
    simpa only [d1967, d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10523 (p : Pattern) (guard : d1972 p = 1) : d632 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d632, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10522 p hg
    simpa only [d1972, d632, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d632, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10505 p hg
    simpa only [d1972, d632, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10524 (p : Pattern) (guard : d1966 p = 1) : d543 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d543, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10482 p hg
    simpa only [d1966, d543, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d543, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1966, d543, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10525 (p : Pattern) (guard : d1971 p = 1) : d549 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d549, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10524 p hg
    simpa only [d1971, d549, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d549, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10504 p hg
    simpa only [d1971, d549, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10526 (p : Pattern) (guard : d1976 p = 1) : d633 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d633, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10525 p hg
    simpa only [d1976, d633, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d633, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10485 p hg
    simpa only [d1976, d633, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10527 (p : Pattern) (guard : d1977 p = 1) : d634 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10523 p hg
    simpa only [d1977, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10526 p hg
    simpa only [d1977, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10528 (p : Pattern) (guard : d1978 p = 1) : d635 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10412 p hg
    simpa only [d1978, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10527 p hg
    simpa only [d1978, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10529 (p : Pattern) (guard : d1967 p = 1) : d541 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10416 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10530 (p : Pattern) (guard : d1972 p = 1) : d558 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10529 p hg
    simpa only [d1972, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10512 p hg
    simpa only [d1972, d558, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10531 (p : Pattern) (guard : d1966 p = 1) : d541 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10425 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10532 (p : Pattern) (guard : d1971 p = 1) : d557 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10531 p hg
    simpa only [d1971, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d1971, d557, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10533 (p : Pattern) (guard : d1976 p = 1) : d590 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10532 p hg
    simpa only [d1976, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d1976, d590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10534 (p : Pattern) (guard : d1977 p = 1) : d591 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10530 p hg
    simpa only [d1977, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10533 p hg
    simpa only [d1977, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10535 (p : Pattern) (guard : d0 p = 1) : d563 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10536 (p : Pattern) (guard : d1971 p = 1) : d563 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10426 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10535 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10537 (p : Pattern) (guard : d1976 p = 1) : d567 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10536 p hg
    simpa only [d1976, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d1976, d567, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10538 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10539 (p : Pattern) (guard : d1981 p = 1) : d593 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10537 p hg
    simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10538 p hg
    simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10540 (p : Pattern) (guard : d1982 p = 1) : d594 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10534 p hg
    simpa only [d1982, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10539 p hg
    simpa only [d1982, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10541 (p : Pattern) (guard : d1983 p = 1) : d636 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d636, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10528 p hg
    simpa only [d1983, d636, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d636, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10540 p hg
    simpa only [d1983, d636, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10542 (p : Pattern) (guard : d1984 p = 1) : d637 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10520 p hg
    simpa only [d1984, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10541 p hg
    simpa only [d1984, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10543 (p : Pattern) (guard : d0 p = 1) : d639 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10544 (p : Pattern) (guard : d1971 p = 1) : d640 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d640, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10483 p hg
    simpa only [d1971, d640, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d640, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10543 p hg
    simpa only [d1971, d640, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10545 (p : Pattern) (guard : d1976 p = 1) : d641 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d641, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10544 p hg
    simpa only [d1976, d641, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d641, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d1976, d641, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10546 (p : Pattern) (guard : d1977 p = 1) : d642 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10480 p hg
    simpa only [d1977, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10545 p hg
    simpa only [d1977, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10547 (p : Pattern) (guard : d1978 p = 1) : d643 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10507 p hg
    simpa only [d1978, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10546 p hg
    simpa only [d1978, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10548 (p : Pattern) (guard : d0 p = 1) : d586 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10549 (p : Pattern) (guard : d1981 p = 1) : d644 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10492 p hg
    simpa only [d1981, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10548 p hg
    simpa only [d1981, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10550 (p : Pattern) (guard : d1982 p = 1) : d645 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10473 p hg
    simpa only [d1982, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10549 p hg
    simpa only [d1982, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10551 (p : Pattern) (guard : d1983 p = 1) : d646 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d646, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10547 p hg
    simpa only [d1983, d646, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d646, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10550 p hg
    simpa only [d1983, d646, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10552 (p : Pattern) (guard : d0 p = 1) : d540 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10553 (p : Pattern) (guard : d1961 p = 1) : d541 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10403 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10552 p hg
    simpa only [d1961, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10554 (p : Pattern) (guard : d1966 p = 1) : d563 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d563, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10553 p hg
    simpa only [d1966, d563, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d563, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d1966, d563, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10555 (p : Pattern) (guard : d1971 p = 1) : d563 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10554 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10535 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10556 (p : Pattern) (guard : d0 p = 1) : d566 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10557 (p : Pattern) (guard : d1976 p = 1) : d567 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d567, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10555 p hg
    simpa only [d1976, d567, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d567, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10556 p hg
    simpa only [d1976, d567, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10558 (p : Pattern) (guard : d0 p = 1) : d592 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10559 (p : Pattern) (guard : d1981 p = 1) : d593 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10557 p hg
    simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10558 p hg
    simpa only [d1981, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10560 (p : Pattern) (guard : d1982 p = 1) : d647 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10527 p hg
    simpa only [d1982, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10559 p hg
    simpa only [d1982, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10561 (p : Pattern) (guard : d1986 p = 1) : d648 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10494 p hg
    simpa only [d1986, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10562 (p : Pattern) (guard : d1987 p = 1) : d649 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d649, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10560 p hg
    simpa only [d1987, d649, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d649, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d1987, d649, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10563 (p : Pattern) (guard : d1988 p = 1) : d650 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10551 p hg
    simpa only [d1988, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10562 p hg
    simpa only [d1988, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10564 (p : Pattern) (guard : d1989 p = 1) : d651 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10542 p hg
    simpa only [d1989, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10563 p hg
    simpa only [d1989, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10565 (p : Pattern) (guard : d1990 p = 1) : d652 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10498 p hg
    simpa only [d1990, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10564 p hg
    simpa only [d1990, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10566 (p : Pattern) (guard : d1945 p = 1) : d135 p ≤ (0 : Int) + d135 p := by
  omega
theorem compare10567 (p : Pattern) (guard : d1946 p = 1) : d456 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9485 p hg
    simpa only [d1946, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1945 p = 1 := by simpa only [d1946, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10566 p hg
    simpa only [d1946, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10568 (p : Pattern) (guard : d1948 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10569 (p : Pattern) (guard : d1949 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9493 p hg
    simpa only [d1949, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10568 p hg
    simpa only [d1949, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10570 (p : Pattern) (guard : d1950 p = 1) : d457 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10567 p hg
    simpa only [d1950, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10569 p hg
    simpa only [d1950, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10571 (p : Pattern) (guard : d1952 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10572 (p : Pattern) (guard : d1953 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9512 p hg
    simpa only [d1953, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10571 p hg
    simpa only [d1953, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10573 (p : Pattern) (guard : d1954 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10569 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10574 (p : Pattern) (guard : d1955 p = 1) : d458 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10570 p hg
    simpa only [d1955, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10573 p hg
    simpa only [d1955, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10575 (p : Pattern) (guard : d1948 p = 1) : d138 p ≤ (0 : Int) + d138 p := by
  omega
theorem compare10576 (p : Pattern) (guard : d1949 p = 1) : d459 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9504 p hg
    simpa only [d1949, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10575 p hg
    simpa only [d1949, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10577 (p : Pattern) (guard : d1954 p = 1) : d460 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10576 p hg
    simpa only [d1954, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d1954, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10578 (p : Pattern) (guard : d1953 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9792 p hg
    simpa only [d1953, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10571 p hg
    simpa only [d1953, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10579 (p : Pattern) (guard : d1957 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d1957, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10580 (p : Pattern) (guard : d1958 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10578 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10579 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10581 (p : Pattern) (guard : d1959 p = 1) : d461 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10577 p hg
    simpa only [d1959, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10580 p hg
    simpa only [d1959, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10582 (p : Pattern) (guard : d1960 p = 1) : d462 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10574 p hg
    simpa only [d1960, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10581 p hg
    simpa only [d1960, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10583 (p : Pattern) (guard : d1948 p = 1) : d135 p ≤ (0 : Int) + d135 p := by
  omega
theorem compare10584 (p : Pattern) (guard : d1949 p = 1) : d456 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9488 p hg
    simpa only [d1949, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10583 p hg
    simpa only [d1949, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10585 (p : Pattern) (guard : d1954 p = 1) : d457 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10584 p hg
    simpa only [d1954, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d1954, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10586 (p : Pattern) (guard : d1953 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9807 p hg
    simpa only [d1953, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10571 p hg
    simpa only [d1953, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10587 (p : Pattern) (guard : d1957 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d1957, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10588 (p : Pattern) (guard : d1958 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10586 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10587 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10589 (p : Pattern) (guard : d1959 p = 1) : d463 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10585 p hg
    simpa only [d1959, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10588 p hg
    simpa only [d1959, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10590 (p : Pattern) (guard : d1952 p = 1) : d138 p ≤ (0 : Int) + d138 p := by
  omega
theorem compare10591 (p : Pattern) (guard : d1953 p = 1) : d464 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9532 p hg
    simpa only [d1953, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10590 p hg
    simpa only [d1953, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10592 (p : Pattern) (guard : d1957 p = 1) : d61 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9539 p hg
    simpa only [d1957, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10593 (p : Pattern) (guard : d1958 p = 1) : d465 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10591 p hg
    simpa only [d1958, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10592 p hg
    simpa only [d1958, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10594 (p : Pattern) (guard : d1961 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9818 p hg
    simpa only [d1961, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10595 (p : Pattern) (guard : d1962 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10579 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10594 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10596 (p : Pattern) (guard : d1963 p = 1) : d466 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10593 p hg
    simpa only [d1963, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d1963, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10597 (p : Pattern) (guard : d1964 p = 1) : d467 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10589 p hg
    simpa only [d1964, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10596 p hg
    simpa only [d1964, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10598 (p : Pattern) (guard : d1965 p = 1) : d468 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10582 p hg
    simpa only [d1965, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10597 p hg
    simpa only [d1965, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10599 (p : Pattern) (guard : d1958 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10600 (p : Pattern) (guard : d1959 p = 1) : d458 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10585 p hg
    simpa only [d1959, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10599 p hg
    simpa only [d1959, d458, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10601 (p : Pattern) (guard : d1953 p = 1) : d459 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9509 p hg
    simpa only [d1953, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10590 p hg
    simpa only [d1953, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10602 (p : Pattern) (guard : d1958 p = 1) : d460 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10601 p hg
    simpa only [d1958, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1958, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10603 (p : Pattern) (guard : d1963 p = 1) : d461 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10602 p hg
    simpa only [d1963, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d1963, d461, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10604 (p : Pattern) (guard : d1964 p = 1) : d462 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10600 p hg
    simpa only [d1964, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10603 p hg
    simpa only [d1964, d462, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10605 (p : Pattern) (guard : d1952 p = 1) : d135 p ≤ (0 : Int) + d135 p := by
  omega
theorem compare10606 (p : Pattern) (guard : d1953 p = 1) : d456 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9527 p hg
    simpa only [d1953, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10605 p hg
    simpa only [d1953, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10607 (p : Pattern) (guard : d1958 p = 1) : d457 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10606 p hg
    simpa only [d1958, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1958, d457, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10608 (p : Pattern) (guard : d1961 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9831 p hg
    simpa only [d1961, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10609 (p : Pattern) (guard : d1962 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10587 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10608 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10610 (p : Pattern) (guard : d1963 p = 1) : d463 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10607 p hg
    simpa only [d1963, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10609 p hg
    simpa only [d1963, d463, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10611 (p : Pattern) (guard : d1957 p = 1) : d464 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9536 p hg
    simpa only [d1957, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1957, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10612 (p : Pattern) (guard : d1961 p = 1) : d61 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9570 p hg
    simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10613 (p : Pattern) (guard : d1962 p = 1) : d465 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10611 p hg
    simpa only [d1962, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10612 p hg
    simpa only [d1962, d465, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10614 (p : Pattern) (guard : d1966 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10594 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10615 (p : Pattern) (guard : d1967 p = 1) : d466 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10613 p hg
    simpa only [d1967, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1967, d466, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10616 (p : Pattern) (guard : d1968 p = 1) : d467 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10610 p hg
    simpa only [d1968, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10615 p hg
    simpa only [d1968, d467, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10617 (p : Pattern) (guard : d1969 p = 1) : d468 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10604 p hg
    simpa only [d1969, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10616 p hg
    simpa only [d1969, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10618 (p : Pattern) (guard : d1970 p = 1) : d468 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10598 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10617 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10619 (p : Pattern) (guard : d1959 p = 1) : d469 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1954 p = 1 := by simpa only [d1959, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10577 p hg
    simpa only [d1959, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1958 p = 1 := by simpa only [d1959, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10599 p hg
    simpa only [d1959, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10620 (p : Pattern) (guard : d1963 p = 1) : d470 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10599 p hg
    simpa only [d1963, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d1963, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10621 (p : Pattern) (guard : d1964 p = 1) : d471 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10619 p hg
    simpa only [d1964, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10620 p hg
    simpa only [d1964, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10622 (p : Pattern) (guard : d1963 p = 1) : d472 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10602 p hg
    simpa only [d1963, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10609 p hg
    simpa only [d1963, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10623 (p : Pattern) (guard : d1962 p = 1) : d61 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10592 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10612 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10624 (p : Pattern) (guard : d1967 p = 1) : d473 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10623 p hg
    simpa only [d1967, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1967, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10625 (p : Pattern) (guard : d1968 p = 1) : d474 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10622 p hg
    simpa only [d1968, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10624 p hg
    simpa only [d1968, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10626 (p : Pattern) (guard : d1969 p = 1) : d475 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10621 p hg
    simpa only [d1969, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10625 p hg
    simpa only [d1969, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10627 (p : Pattern) (guard : d1962 p = 1) : d52 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10628 (p : Pattern) (guard : d1963 p = 1) : d469 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10602 p hg
    simpa only [d1963, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10627 p hg
    simpa only [d1963, d469, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10629 (p : Pattern) (guard : d1967 p = 1) : d470 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10627 p hg
    simpa only [d1967, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d1967, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10630 (p : Pattern) (guard : d1968 p = 1) : d471 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10628 p hg
    simpa only [d1968, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10629 p hg
    simpa only [d1968, d471, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10631 (p : Pattern) (guard : d1957 p = 1) : d459 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9550 p hg
    simpa only [d1957, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1957, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10632 (p : Pattern) (guard : d1962 p = 1) : d460 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10631 p hg
    simpa only [d1962, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d460, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10633 (p : Pattern) (guard : d1966 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10608 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10634 (p : Pattern) (guard : d1967 p = 1) : d472 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d1967, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d1967, d472, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10635 (p : Pattern) (guard : d1966 p = 1) : d61 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10612 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10636 (p : Pattern) (guard : d1971 p = 1) : d473 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d1971, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1971, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10637 (p : Pattern) (guard : d1972 p = 1) : d474 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d1972, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d1972, d474, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10638 (p : Pattern) (guard : d1973 p = 1) : d475 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10630 p hg
    simpa only [d1973, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d1973, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10639 (p : Pattern) (guard : d1974 p = 1) : d475 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10626 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
