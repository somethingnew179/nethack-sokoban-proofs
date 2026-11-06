/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9660 (p : Pattern) (guard : d1976 p = 1) : d351 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d351, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9659 p hg
    simpa only [d1976, d351, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d351, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d1976, d351, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9661 (p : Pattern) (guard : d1977 p = 1) : d352 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9656 p hg
    simpa only [d1977, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9660 p hg
    simpa only [d1977, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9662 (p : Pattern) (guard : d1978 p = 1) : d353 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9653 p hg
    simpa only [d1978, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9661 p hg
    simpa only [d1978, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9663 (p : Pattern) (guard : d1979 p = 1) : d354 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d354, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9644 p hg
    simpa only [d1979, d354, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d354, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9662 p hg
    simpa only [d1979, d354, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9664 (p : Pattern) (guard : d1980 p = 1) : d355 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9616 p hg
    simpa only [d1980, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9663 p hg
    simpa only [d1980, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9665 (p : Pattern) (guard : d1958 p = 1) : d86 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9563 p hg
    simpa only [d1958, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9597 p hg
    simpa only [d1958, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9666 (p : Pattern) (guard : d1963 p = 1) : d356 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9665 p hg
    simpa only [d1963, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9667 (p : Pattern) (guard : d1962 p = 1) : d86 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9627 p hg
    simpa only [d1962, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9668 (p : Pattern) (guard : d1967 p = 1) : d356 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9667 p hg
    simpa only [d1967, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9669 (p : Pattern) (guard : d1968 p = 1) : d356 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9666 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9668 p hg
    simpa only [d1968, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9670 (p : Pattern) (guard : d1962 p = 1) : d86 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1962, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1962, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9671 (p : Pattern) (guard : d1967 p = 1) : d356 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9670 p hg
    simpa only [d1967, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9672 (p : Pattern) (guard : d1961 p = 1) : d38 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9567 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1602 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9673 (p : Pattern) (guard : d1966 p = 1) : d92 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d92, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9672 p hg
    simpa only [d1966, d92, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d92, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1966, d92, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9674 (p : Pattern) (guard : d1971 p = 1) : d357 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d357, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9673 p hg
    simpa only [d1971, d357, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d357, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d357, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9675 (p : Pattern) (guard : d1972 p = 1) : d358 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9671 p hg
    simpa only [d1972, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9674 p hg
    simpa only [d1972, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9676 (p : Pattern) (guard : d1973 p = 1) : d359 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9669 p hg
    simpa only [d1973, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9675 p hg
    simpa only [d1973, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9677 (p : Pattern) (guard : d1974 p = 1) : d360 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9576 p hg
    simpa only [d1974, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9676 p hg
    simpa only [d1974, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9678 (p : Pattern) (guard : d1953 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9579 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9588 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9679 (p : Pattern) (guard : d1957 p = 1) : d97 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9518 p hg
    simpa only [d1957, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9680 (p : Pattern) (guard : d1958 p = 1) : d98 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9678 p hg
    simpa only [d1958, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9679 p hg
    simpa only [d1958, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9681 (p : Pattern) (guard : d1963 p = 1) : d361 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9680 p hg
    simpa only [d1963, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9544 p hg
    simpa only [d1963, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9682 (p : Pattern) (guard : d1957 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9518 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9553 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9683 (p : Pattern) (guard : d1961 p = 1) : d97 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9553 p hg
    simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9684 (p : Pattern) (guard : d1962 p = 1) : d98 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9682 p hg
    simpa only [d1962, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9685 (p : Pattern) (guard : d1967 p = 1) : d361 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9684 p hg
    simpa only [d1967, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9686 (p : Pattern) (guard : d1968 p = 1) : d361 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9681 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9685 p hg
    simpa only [d1968, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9687 (p : Pattern) (guard : d1957 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9588 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9688 (p : Pattern) (guard : d1962 p = 1) : d98 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9687 p hg
    simpa only [d1962, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1962, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9689 (p : Pattern) (guard : d1967 p = 1) : d361 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1967, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9573 p hg
    simpa only [d1967, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9690 (p : Pattern) (guard : d1961 p = 1) : d40 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9541 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1604 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9691 (p : Pattern) (guard : d1966 p = 1) : d69 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9690 p hg
    simpa only [d1966, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1966, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9692 (p : Pattern) (guard : d1971 p = 1) : d342 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9691 p hg
    simpa only [d1971, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9693 (p : Pattern) (guard : d1972 p = 1) : d362 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9689 p hg
    simpa only [d1972, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9692 p hg
    simpa only [d1972, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9694 (p : Pattern) (guard : d1973 p = 1) : d363 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9686 p hg
    simpa only [d1973, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9693 p hg
    simpa only [d1973, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9695 (p : Pattern) (guard : d1961 p = 1) : d14 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9553 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9696 (p : Pattern) (guard : d1966 p = 1) : d98 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9695 p hg
    simpa only [d1966, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9697 (p : Pattern) (guard : d1971 p = 1) : d361 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1971, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9698 (p : Pattern) (guard : d1972 p = 1) : d361 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9689 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9697 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9699 (p : Pattern) (guard : d1961 p = 1) : d14 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9700 (p : Pattern) (guard : d1966 p = 1) : d98 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9699 p hg
    simpa only [d1966, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d98, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9701 (p : Pattern) (guard : d1971 p = 1) : d361 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9700 p hg
    simpa only [d1971, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d361, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9702 (p : Pattern) (guard : d1976 p = 1) : d362 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9701 p hg
    simpa only [d1976, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d1976, d362, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9703 (p : Pattern) (guard : d1977 p = 1) : d363 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9698 p hg
    simpa only [d1977, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9702 p hg
    simpa only [d1977, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9704 (p : Pattern) (guard : d1978 p = 1) : d363 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9703 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9705 (p : Pattern) (guard : d1979 p = 1) : d364 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d364, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9677 p hg
    simpa only [d1979, d364, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d364, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9704 p hg
    simpa only [d1979, d364, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9706 (p : Pattern) (guard : d1961 p = 1) : d8 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1587 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9707 (p : Pattern) (guard : d1966 p = 1) : d86 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9706 p hg
    simpa only [d1966, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d86, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9708 (p : Pattern) (guard : d1971 p = 1) : d356 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9707 p hg
    simpa only [d1971, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d356, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9709 (p : Pattern) (guard : d1972 p = 1) : d356 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9671 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9708 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9710 (p : Pattern) (guard : d1961 p = 1) : d8 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9634 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9711 (p : Pattern) (guard : d1966 p = 1) : d86 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9710 p hg
    simpa only [d1966, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d86, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9712 (p : Pattern) (guard : d1971 p = 1) : d356 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9711 p hg
    simpa only [d1971, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d356, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9713 (p : Pattern) (guard : d0 p = 1) : d345 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9714 (p : Pattern) (guard : d1976 p = 1) : d365 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d365, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9712 p hg
    simpa only [d1976, d365, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d365, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9713 p hg
    simpa only [d1976, d365, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9715 (p : Pattern) (guard : d1977 p = 1) : d366 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9709 p hg
    simpa only [d1977, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9714 p hg
    simpa only [d1977, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9716 (p : Pattern) (guard : d1978 p = 1) : d367 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9643 p hg
    simpa only [d1978, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9715 p hg
    simpa only [d1978, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9717 (p : Pattern) (guard : d1976 p = 1) : d368 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d368, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9701 p hg
    simpa only [d1976, d368, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d368, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d368, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9718 (p : Pattern) (guard : d1977 p = 1) : d369 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9698 p hg
    simpa only [d1977, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9717 p hg
    simpa only [d1977, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9719 (p : Pattern) (guard : d1961 p = 1) : d97 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9607 p hg
    simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9720 (p : Pattern) (guard : d1966 p = 1) : d97 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9719 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9721 (p : Pattern) (guard : d1971 p = 1) : d370 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d370, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9720 p hg
    simpa only [d1971, d370, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d370, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d370, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9722 (p : Pattern) (guard : d1976 p = 1) : d370 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9721 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9723 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9724 (p : Pattern) (guard : d1981 p = 1) : d372 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9722 p hg
    simpa only [d1981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9723 p hg
    simpa only [d1981, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9725 (p : Pattern) (guard : d1982 p = 1) : d373 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9718 p hg
    simpa only [d1982, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9724 p hg
    simpa only [d1982, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9726 (p : Pattern) (guard : d1983 p = 1) : d374 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d374, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9716 p hg
    simpa only [d1983, d374, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d374, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9725 p hg
    simpa only [d1983, d374, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9727 (p : Pattern) (guard : d1984 p = 1) : d375 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9705 p hg
    simpa only [d1984, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9726 p hg
    simpa only [d1984, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9728 (p : Pattern) (guard : d1985 p = 1) : d376 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9664 p hg
    simpa only [d1985, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9727 p hg
    simpa only [d1985, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9729 (p : Pattern) (guard : d1966 p = 1) : d42 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9672 p hg
    simpa only [d1966, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1966, d42, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9730 (p : Pattern) (guard : d1971 p = 1) : d329 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9729 p hg
    simpa only [d1971, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d329, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9731 (p : Pattern) (guard : d1972 p = 1) : d330 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9637 p hg
    simpa only [d1972, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9730 p hg
    simpa only [d1972, d330, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9732 (p : Pattern) (guard : d1973 p = 1) : d331 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9631 p hg
    simpa only [d1973, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9731 p hg
    simpa only [d1973, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9733 (p : Pattern) (guard : d1974 p = 1) : d331 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9576 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9732 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9734 (p : Pattern) (guard : d1966 p = 1) : d41 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9571 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1443 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9735 (p : Pattern) (guard : d1971 p = 1) : d333 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9734 p hg
    simpa only [d1971, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9736 (p : Pattern) (guard : d1972 p = 1) : d334 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9649 p hg
    simpa only [d1972, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9735 p hg
    simpa only [d1972, d334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9737 (p : Pattern) (guard : d1973 p = 1) : d335 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9647 p hg
    simpa only [d1973, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9736 p hg
    simpa only [d1973, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9738 (p : Pattern) (guard : d1976 p = 1) : d338 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9659 p hg
    simpa only [d1976, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3822 p hg
    simpa only [d1976, d338, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9739 (p : Pattern) (guard : d1977 p = 1) : d339 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9656 p hg
    simpa only [d1977, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9738 p hg
    simpa only [d1977, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9740 (p : Pattern) (guard : d1978 p = 1) : d340 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9737 p hg
    simpa only [d1978, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9739 p hg
    simpa only [d1978, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9741 (p : Pattern) (guard : d1979 p = 1) : d341 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9733 p hg
    simpa only [d1979, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9740 p hg
    simpa only [d1979, d341, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9742 (p : Pattern) (guard : d1966 p = 1) : d16 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9706 p hg
    simpa only [d1966, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1966, d16, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9743 (p : Pattern) (guard : d1971 p = 1) : d328 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9742 p hg
    simpa only [d1971, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d328, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9744 (p : Pattern) (guard : d1972 p = 1) : d328 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9637 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9743 p hg
    simpa only [d1972, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9745 (p : Pattern) (guard : d1966 p = 1) : d16 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9710 p hg
    simpa only [d1966, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1966, d16, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9746 (p : Pattern) (guard : d1971 p = 1) : d328 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9745 p hg
    simpa only [d1971, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d328, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9747 (p : Pattern) (guard : d1976 p = 1) : d346 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9746 p hg
    simpa only [d1976, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9713 p hg
    simpa only [d1976, d346, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9748 (p : Pattern) (guard : d1977 p = 1) : d347 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9744 p hg
    simpa only [d1977, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9747 p hg
    simpa only [d1977, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9749 (p : Pattern) (guard : d1978 p = 1) : d347 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9643 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9748 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9750 (p : Pattern) (guard : d1966 p = 1) : d15 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9628 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9751 (p : Pattern) (guard : d1971 p = 1) : d332 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9750 p hg
    simpa only [d1971, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9752 (p : Pattern) (guard : d1972 p = 1) : d332 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9649 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9751 p hg
    simpa only [d1972, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9753 (p : Pattern) (guard : d1966 p = 1) : d15 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9657 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9754 (p : Pattern) (guard : d1971 p = 1) : d332 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9753 p hg
    simpa only [d1971, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d332, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9755 (p : Pattern) (guard : d1976 p = 1) : d349 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9754 p hg
    simpa only [d1976, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d1976, d349, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9756 (p : Pattern) (guard : d1977 p = 1) : d350 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9752 p hg
    simpa only [d1977, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9755 p hg
    simpa only [d1977, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9757 (p : Pattern) (guard : d1976 p = 1) : d336 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9659 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3820 p hg
    simpa only [d1976, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9758 (p : Pattern) (guard : d0 p = 1) : d351 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9759 (p : Pattern) (guard : d1981 p = 1) : d352 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9757 p hg
    simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9758 p hg
    simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9760 (p : Pattern) (guard : d1982 p = 1) : d353 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9756 p hg
    simpa only [d1982, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9759 p hg
    simpa only [d1982, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9761 (p : Pattern) (guard : d1983 p = 1) : d377 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d377, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9749 p hg
    simpa only [d1983, d377, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d377, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9760 p hg
    simpa only [d1983, d377, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9762 (p : Pattern) (guard : d1984 p = 1) : d378 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9741 p hg
    simpa only [d1984, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9761 p hg
    simpa only [d1984, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9763 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9764 (p : Pattern) (guard : d1976 p = 1) : d358 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9712 p hg
    simpa only [d1976, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9763 p hg
    simpa only [d1976, d358, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9765 (p : Pattern) (guard : d1977 p = 1) : d359 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9709 p hg
    simpa only [d1977, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9764 p hg
    simpa only [d1977, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9766 (p : Pattern) (guard : d1978 p = 1) : d360 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9732 p hg
    simpa only [d1978, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9765 p hg
    simpa only [d1978, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9767 (p : Pattern) (guard : d0 p = 1) : d379 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9768 (p : Pattern) (guard : d1981 p = 1) : d380 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9722 p hg
    simpa only [d1981, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9767 p hg
    simpa only [d1981, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9769 (p : Pattern) (guard : d1982 p = 1) : d381 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9703 p hg
    simpa only [d1982, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9768 p hg
    simpa only [d1982, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9770 (p : Pattern) (guard : d1983 p = 1) : d382 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d382, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9766 p hg
    simpa only [d1983, d382, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d382, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9769 p hg
    simpa only [d1983, d382, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9771 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9772 (p : Pattern) (guard : d1961 p = 1) : d15 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9634 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9771 p hg
    simpa only [d1961, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9773 (p : Pattern) (guard : d1966 p = 1) : d53 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d53, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d1966, d53, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d53, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1966, d53, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9774 (p : Pattern) (guard : d1971 p = 1) : d336 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d336, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9773 p hg
    simpa only [d1971, d336, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d336, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d336, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9775 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9776 (p : Pattern) (guard : d1976 p = 1) : d336 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9774 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9775 p hg
    simpa only [d1976, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9777 (p : Pattern) (guard : d0 p = 1) : d351 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9778 (p : Pattern) (guard : d1981 p = 1) : d352 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9776 p hg
    simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9777 p hg
    simpa only [d1981, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9779 (p : Pattern) (guard : d1982 p = 1) : d383 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9748 p hg
    simpa only [d1982, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9778 p hg
    simpa only [d1982, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9780 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9781 (p : Pattern) (guard : d1986 p = 1) : d384 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9724 p hg
    simpa only [d1986, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9782 (p : Pattern) (guard : d1987 p = 1) : d385 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d385, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9779 p hg
    simpa only [d1987, d385, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d385, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9781 p hg
    simpa only [d1987, d385, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9783 (p : Pattern) (guard : d1988 p = 1) : d386 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9770 p hg
    simpa only [d1988, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9782 p hg
    simpa only [d1988, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9784 (p : Pattern) (guard : d1989 p = 1) : d387 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9762 p hg
    simpa only [d1989, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9783 p hg
    simpa only [d1989, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9785 (p : Pattern) (guard : d1990 p = 1) : d388 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9728 p hg
    simpa only [d1990, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9784 p hg
    simpa only [d1990, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9786 (p : Pattern) (guard : d1949 p = 1) : d8 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1945 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9493 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1948 p = 1 := by simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9512 p hg
    simpa only [d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9787 (p : Pattern) (guard : d1954 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1949 p = 1 := by simpa only [d1954, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9786 p hg
    simpa only [d1954, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1953 p = 1 := by simpa only [d1954, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9519 p hg
    simpa only [d1954, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9788 (p : Pattern) (guard : d1955 p = 1) : d16 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1950 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9500 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1954 p = 1 := by simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9787 p hg
    simpa only [d1955, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9789 (p : Pattern) (guard : d1943 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d1943, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9790 (p : Pattern) (guard : d1944 p = 1) : d18 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1944, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d1944, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1943 p = 1 := by simpa only [d1944, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1944, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9791 (p : Pattern) (guard : d1947 p = 1) : d19 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d1947, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9792 (p : Pattern) (guard : d1948 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1944 p = 1 := by simpa only [d1948, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d1948, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1947 p = 1 := by simpa only [d1948, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d1948, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9793 (p : Pattern) (guard : d1293 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9794 (p : Pattern) (guard : d1947 p = 1) : d18 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1943 p = 1 := by simpa only [d1947, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9507 p hg
    simpa only [d1947, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1947, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1947, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9795 (p : Pattern) (guard : d1951 p = 1) : d19 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9796 (p : Pattern) (guard : d1952 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9794 p hg
    simpa only [d1952, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9795 p hg
    simpa only [d1952, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9797 (p : Pattern) (guard : d1953 p = 1) : d20 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9792 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9798 (p : Pattern) (guard : d1951 p = 1) : d22 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9516 p hg
    simpa only [d1951, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d1951, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9799 (p : Pattern) (guard : d1956 p = 1) : d24 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9798 p hg
    simpa only [d1956, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d1956, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
