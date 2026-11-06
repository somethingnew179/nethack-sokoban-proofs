/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9940 (p : Pattern) (guard : d1984 p = 1) : d115 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9921 p hg
    simpa only [d1984, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9939 p hg
    simpa only [d1984, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9941 (p : Pattern) (guard : d1985 p = 1) : d116 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9894 p hg
    simpa only [d1985, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9940 p hg
    simpa only [d1985, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9942 (p : Pattern) (guard : d1966 p = 1) : d35 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d1966, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d1966, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9943 (p : Pattern) (guard : d1967 p = 1) : d36 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9636 p hg
    simpa only [d1967, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9942 p hg
    simpa only [d1967, d36, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9944 (p : Pattern) (guard : d1971 p = 1) : d43 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9729 p hg
    simpa only [d1971, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d1971, d43, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9945 (p : Pattern) (guard : d1972 p = 1) : d44 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d1972, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9944 p hg
    simpa only [d1972, d44, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9946 (p : Pattern) (guard : d1973 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9873 p hg
    simpa only [d1973, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9945 p hg
    simpa only [d1973, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9947 (p : Pattern) (guard : d1974 p = 1) : d45 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9840 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9948 (p : Pattern) (guard : d1966 p = 1) : d34 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9833 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9949 (p : Pattern) (guard : d1967 p = 1) : d48 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9648 p hg
    simpa only [d1967, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9948 p hg
    simpa only [d1967, d48, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9950 (p : Pattern) (guard : d1971 p = 1) : d49 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9734 p hg
    simpa only [d1971, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1971, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9951 (p : Pattern) (guard : d1972 p = 1) : d50 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9949 p hg
    simpa only [d1972, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9950 p hg
    simpa only [d1972, d50, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9952 (p : Pattern) (guard : d1973 p = 1) : d51 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9881 p hg
    simpa only [d1973, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9951 p hg
    simpa only [d1973, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9953 (p : Pattern) (guard : d1971 p = 1) : d60 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1971, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d1971, d60, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9954 (p : Pattern) (guard : d1976 p = 1) : d64 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9953 p hg
    simpa only [d1976, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1124 p hg
    simpa only [d1976, d64, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9955 (p : Pattern) (guard : d1977 p = 1) : d65 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9888 p hg
    simpa only [d1977, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9954 p hg
    simpa only [d1977, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9956 (p : Pattern) (guard : d1978 p = 1) : d66 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9952 p hg
    simpa only [d1978, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9955 p hg
    simpa only [d1978, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9957 (p : Pattern) (guard : d1979 p = 1) : d67 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9947 p hg
    simpa only [d1979, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9956 p hg
    simpa only [d1979, d67, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9958 (p : Pattern) (guard : d1966 p = 1) : d16 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9922 p hg
    simpa only [d1966, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1966, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9959 (p : Pattern) (guard : d1967 p = 1) : d16 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9636 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9958 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9960 (p : Pattern) (guard : d1971 p = 1) : d27 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9742 p hg
    simpa only [d1971, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d1971, d27, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9961 (p : Pattern) (guard : d1972 p = 1) : d28 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9959 p hg
    simpa only [d1972, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9960 p hg
    simpa only [d1972, d28, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9962 (p : Pattern) (guard : d1971 p = 1) : d27 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9745 p hg
    simpa only [d1971, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d1971, d27, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9963 (p : Pattern) (guard : d1976 p = 1) : d76 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9962 p hg
    simpa only [d1976, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9928 p hg
    simpa only [d1976, d76, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9964 (p : Pattern) (guard : d1977 p = 1) : d77 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9961 p hg
    simpa only [d1977, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9963 p hg
    simpa only [d1977, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9965 (p : Pattern) (guard : d1978 p = 1) : d77 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9877 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9966 (p : Pattern) (guard : d1967 p = 1) : d15 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9648 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9750 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9967 (p : Pattern) (guard : d1971 p = 1) : d46 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9750 p hg
    simpa only [d1971, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1971, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9968 (p : Pattern) (guard : d1972 p = 1) : d47 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1972, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9967 p hg
    simpa only [d1972, d47, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9969 (p : Pattern) (guard : d1971 p = 1) : d46 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9753 p hg
    simpa only [d1971, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1971, d46, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9970 (p : Pattern) (guard : d1976 p = 1) : d79 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9969 p hg
    simpa only [d1976, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1976, d79, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9971 (p : Pattern) (guard : d1977 p = 1) : d80 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9968 p hg
    simpa only [d1977, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9970 p hg
    simpa only [d1977, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9972 (p : Pattern) (guard : d1971 p = 1) : d53 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9973 (p : Pattern) (guard : d1976 p = 1) : d57 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d1976, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d1976, d57, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9974 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9975 (p : Pattern) (guard : d1981 p = 1) : d82 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9973 p hg
    simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9974 p hg
    simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9976 (p : Pattern) (guard : d1982 p = 1) : d83 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9971 p hg
    simpa only [d1982, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9975 p hg
    simpa only [d1982, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9977 (p : Pattern) (guard : d1983 p = 1) : d117 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d117, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9965 p hg
    simpa only [d1983, d117, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d117, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9976 p hg
    simpa only [d1983, d117, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9978 (p : Pattern) (guard : d1984 p = 1) : d118 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9957 p hg
    simpa only [d1984, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9977 p hg
    simpa only [d1984, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9979 (p : Pattern) (guard : d1971 p = 1) : d121 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d121, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9711 p hg
    simpa only [d1971, d121, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d121, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d1971, d121, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9980 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9981 (p : Pattern) (guard : d1976 p = 1) : d122 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d122, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9979 p hg
    simpa only [d1976, d122, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d122, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9980 p hg
    simpa only [d1976, d122, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9982 (p : Pattern) (guard : d1977 p = 1) : d123 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d1977, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9981 p hg
    simpa only [d1977, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9983 (p : Pattern) (guard : d1978 p = 1) : d124 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9946 p hg
    simpa only [d1978, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9982 p hg
    simpa only [d1978, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9984 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9985 (p : Pattern) (guard : d1981 p = 1) : d126 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9935 p hg
    simpa only [d1981, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9984 p hg
    simpa only [d1981, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9986 (p : Pattern) (guard : d1982 p = 1) : d127 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9919 p hg
    simpa only [d1982, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9985 p hg
    simpa only [d1982, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9987 (p : Pattern) (guard : d1983 p = 1) : d128 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d128, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9983 p hg
    simpa only [d1983, d128, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d128, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9986 p hg
    simpa only [d1983, d128, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9988 (p : Pattern) (guard : d1971 p = 1) : d53 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9773 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9989 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9990 (p : Pattern) (guard : d1976 p = 1) : d57 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d57, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9988 p hg
    simpa only [d1976, d57, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d57, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9989 p hg
    simpa only [d1976, d57, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9991 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9992 (p : Pattern) (guard : d1981 p = 1) : d82 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9990 p hg
    simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9991 p hg
    simpa only [d1981, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9993 (p : Pattern) (guard : d1982 p = 1) : d129 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9964 p hg
    simpa only [d1982, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9992 p hg
    simpa only [d1982, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9994 (p : Pattern) (guard : d1986 p = 1) : d130 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9937 p hg
    simpa only [d1986, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9995 (p : Pattern) (guard : d1987 p = 1) : d131 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d131, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9993 p hg
    simpa only [d1987, d131, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d131, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9994 p hg
    simpa only [d1987, d131, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9996 (p : Pattern) (guard : d1988 p = 1) : d132 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9987 p hg
    simpa only [d1988, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9995 p hg
    simpa only [d1988, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9997 (p : Pattern) (guard : d1989 p = 1) : d133 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9978 p hg
    simpa only [d1989, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9996 p hg
    simpa only [d1989, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9998 (p : Pattern) (guard : d1990 p = 1) : d134 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9941 p hg
    simpa only [d1990, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9997 p hg
    simpa only [d1990, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9999 (p : Pattern) (guard : d1959 p = 1) : d140 p ≤ (0 : Int) + d140 p := by
  omega
theorem compare10000 (p : Pattern) (guard : d1960 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1955 p = 1 := by simpa only [d1960, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9788 p hg
    simpa only [d1960, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1959 p = 1 := by simpa only [d1960, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9999 p hg
    simpa only [d1960, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10001 (p : Pattern) (guard : d1963 p = 1) : d140 p ≤ (0 : Int) + d140 p := by
  omega
theorem compare10002 (p : Pattern) (guard : d1964 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d1964, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10001 p hg
    simpa only [d1964, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10003 (p : Pattern) (guard : d1965 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1960 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10000 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1964 p = 1 := by simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10002 p hg
    simpa only [d1965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10004 (p : Pattern) (guard : d1967 p = 1) : d140 p ≤ (0 : Int) + d140 p := by
  omega
theorem compare10005 (p : Pattern) (guard : d1968 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d1968, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10004 p hg
    simpa only [d1968, d293, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10006 (p : Pattern) (guard : d1969 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10002 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10005 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10007 (p : Pattern) (guard : d1970 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1965 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10003 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1969 p = 1 := by simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10006 p hg
    simpa only [d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10008 (p : Pattern) (guard : d1963 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10009 (p : Pattern) (guard : d1964 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1959 p = 1 := by simpa only [d1964, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9842 p hg
    simpa only [d1964, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1963 p = 1 := by simpa only [d1964, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10008 p hg
    simpa only [d1964, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10010 (p : Pattern) (guard : d1967 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10011 (p : Pattern) (guard : d1968 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9879 p hg
    simpa only [d1968, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10010 p hg
    simpa only [d1968, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10012 (p : Pattern) (guard : d1969 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10011 p hg
    simpa only [d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10013 (p : Pattern) (guard : d1968 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9852 p hg
    simpa only [d1968, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10010 p hg
    simpa only [d1968, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10014 (p : Pattern) (guard : d1971 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10015 (p : Pattern) (guard : d1972 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9886 p hg
    simpa only [d1972, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10014 p hg
    simpa only [d1972, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10016 (p : Pattern) (guard : d1973 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10013 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10015 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10017 (p : Pattern) (guard : d1974 p = 1) : d296 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10012 p hg
    simpa only [d1974, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10016 p hg
    simpa only [d1974, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10018 (p : Pattern) (guard : d1975 p = 1) : d297 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d297, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10007 p hg
    simpa only [d1975, d297, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d297, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10017 p hg
    simpa only [d1975, d297, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10019 (p : Pattern) (guard : d1956 p = 1) : d138 p ≤ (0 : Int) + d138 p := by
  omega
theorem compare10020 (p : Pattern) (guard : d1961 p = 1) : d146 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d1961, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10021 (p : Pattern) (guard : d1966 p = 1) : d147 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d147, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10020 p hg
    simpa only [d1966, d147, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d147, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1966, d147, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10022 (p : Pattern) (guard : d1971 p = 1) : d148 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d148, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10021 p hg
    simpa only [d1971, d148, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d148, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1971, d148, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10023 (p : Pattern) (guard : d1972 p = 1) : d298 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d298, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9959 p hg
    simpa only [d1972, d298, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d298, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d1972, d298, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10024 (p : Pattern) (guard : d1973 p = 1) : d299 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10005 p hg
    simpa only [d1973, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10023 p hg
    simpa only [d1973, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10025 (p : Pattern) (guard : d1974 p = 1) : d300 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10006 p hg
    simpa only [d1974, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10024 p hg
    simpa only [d1974, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10026 (p : Pattern) (guard : d1972 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9966 p hg
    simpa only [d1972, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10014 p hg
    simpa only [d1972, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10027 (p : Pattern) (guard : d1973 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10011 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10026 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10028 (p : Pattern) (guard : d1976 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9972 p hg
    simpa only [d1976, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d295, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10029 (p : Pattern) (guard : d1977 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10015 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10028 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10030 (p : Pattern) (guard : d1978 p = 1) : d296 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10027 p hg
    simpa only [d1978, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10029 p hg
    simpa only [d1978, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10031 (p : Pattern) (guard : d1979 p = 1) : d301 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d301, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10025 p hg
    simpa only [d1979, d301, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d301, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10030 p hg
    simpa only [d1979, d301, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10032 (p : Pattern) (guard : d1980 p = 1) : d302 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10018 p hg
    simpa only [d1980, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10031 p hg
    simpa only [d1980, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10033 (p : Pattern) (guard : d1968 p = 1) : d303 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d303, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9896 p hg
    simpa only [d1968, d303, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d303, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10004 p hg
    simpa only [d1968, d303, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10034 (p : Pattern) (guard : d1972 p = 1) : d304 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d304, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9924 p hg
    simpa only [d1972, d304, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d304, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d1972, d304, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10035 (p : Pattern) (guard : d1973 p = 1) : d305 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10033 p hg
    simpa only [d1973, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10034 p hg
    simpa only [d1973, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10036 (p : Pattern) (guard : d1974 p = 1) : d306 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10006 p hg
    simpa only [d1974, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10035 p hg
    simpa only [d1974, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10037 (p : Pattern) (guard : d1968 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9907 p hg
    simpa only [d1968, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10010 p hg
    simpa only [d1968, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10038 (p : Pattern) (guard : d1972 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9914 p hg
    simpa only [d1972, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10014 p hg
    simpa only [d1972, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10039 (p : Pattern) (guard : d1973 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10037 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10038 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10040 (p : Pattern) (guard : d1971 p = 1) : d98 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9700 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10041 (p : Pattern) (guard : d1976 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10040 p hg
    simpa only [d1976, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d307, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10042 (p : Pattern) (guard : d1977 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10038 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10041 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10043 (p : Pattern) (guard : d1978 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10039 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10042 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10044 (p : Pattern) (guard : d1979 p = 1) : d308 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d308, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10036 p hg
    simpa only [d1979, d308, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d308, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10043 p hg
    simpa only [d1979, d308, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10045 (p : Pattern) (guard : d1971 p = 1) : d86 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9711 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10046 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10047 (p : Pattern) (guard : d1976 p = 1) : d309 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d309, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10045 p hg
    simpa only [d1976, d309, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d309, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10046 p hg
    simpa only [d1976, d309, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10048 (p : Pattern) (guard : d1977 p = 1) : d310 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10034 p hg
    simpa only [d1977, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10047 p hg
    simpa only [d1977, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10049 (p : Pattern) (guard : d1978 p = 1) : d311 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10024 p hg
    simpa only [d1978, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10048 p hg
    simpa only [d1978, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10050 (p : Pattern) (guard : d1976 p = 1) : d312 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d312, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9934 p hg
    simpa only [d1976, d312, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d312, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d312, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10051 (p : Pattern) (guard : d0 p = 1) : d312 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10052 (p : Pattern) (guard : d1981 p = 1) : d312 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10050 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10051 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10053 (p : Pattern) (guard : d1982 p = 1) : d313 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10042 p hg
    simpa only [d1982, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10052 p hg
    simpa only [d1982, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10054 (p : Pattern) (guard : d1983 p = 1) : d314 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d314, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10049 p hg
    simpa only [d1983, d314, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d314, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10053 p hg
    simpa only [d1983, d314, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10055 (p : Pattern) (guard : d1984 p = 1) : d315 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10044 p hg
    simpa only [d1984, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10054 p hg
    simpa only [d1984, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10056 (p : Pattern) (guard : d1985 p = 1) : d316 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1980 p = 1 := by simpa only [d1985, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10032 p hg
    simpa only [d1985, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1984 p = 1 := by simpa only [d1985, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10055 p hg
    simpa only [d1985, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10057 (p : Pattern) (guard : d1971 p = 1) : d16 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9745 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare842 p hg
    simpa only [d1971, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10058 (p : Pattern) (guard : d1976 p = 1) : d317 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d317, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10057 p hg
    simpa only [d1976, d317, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d317, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10046 p hg
    simpa only [d1976, d317, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10059 (p : Pattern) (guard : d1977 p = 1) : d318 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10023 p hg
    simpa only [d1977, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10058 p hg
    simpa only [d1977, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10060 (p : Pattern) (guard : d1978 p = 1) : d319 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10024 p hg
    simpa only [d1978, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10059 p hg
    simpa only [d1978, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10061 (p : Pattern) (guard : d1971 p = 1) : d15 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9753 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10062 (p : Pattern) (guard : d1976 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10061 p hg
    simpa only [d1976, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1976, d294, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10063 (p : Pattern) (guard : d1977 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10026 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10062 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10064 (p : Pattern) (guard : d1981 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10028 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3158 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10065 (p : Pattern) (guard : d1982 p = 1) : d296 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10063 p hg
    simpa only [d1982, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10064 p hg
    simpa only [d1982, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10066 (p : Pattern) (guard : d1983 p = 1) : d320 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1978 p = 1 := by simpa only [d1983, d320, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10060 p hg
    simpa only [d1983, d320, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1982 p = 1 := by simpa only [d1983, d320, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10065 p hg
    simpa only [d1983, d320, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10067 (p : Pattern) (guard : d1984 p = 1) : d321 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1979 p = 1 := by simpa only [d1984, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10031 p hg
    simpa only [d1984, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1983 p = 1 := by simpa only [d1984, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10066 p hg
    simpa only [d1984, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10068 (p : Pattern) (guard : d1976 p = 1) : d295 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d295, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9988 p hg
    simpa only [d1976, d295, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d295, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10046 p hg
    simpa only [d1976, d295, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10069 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10070 (p : Pattern) (guard : d1981 p = 1) : d295 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10068 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10069 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10071 (p : Pattern) (guard : d1982 p = 1) : d322 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1977 p = 1 := by simpa only [d1982, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10059 p hg
    simpa only [d1982, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d1982, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10070 p hg
    simpa only [d1982, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10072 (p : Pattern) (guard : d1986 p = 1) : d323 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1981 p = 1 := by simpa only [d1986, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10052 p hg
    simpa only [d1986, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1986, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d1986, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10073 (p : Pattern) (guard : d1987 p = 1) : d324 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1982 p = 1 := by simpa only [d1987, d324, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10071 p hg
    simpa only [d1987, d324, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1986 p = 1 := by simpa only [d1987, d324, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10072 p hg
    simpa only [d1987, d324, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10074 (p : Pattern) (guard : d1988 p = 1) : d325 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1983 p = 1 := by simpa only [d1988, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10054 p hg
    simpa only [d1988, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1987 p = 1 := by simpa only [d1988, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10073 p hg
    simpa only [d1988, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10075 (p : Pattern) (guard : d1989 p = 1) : d326 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1984 p = 1 := by simpa only [d1989, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10067 p hg
    simpa only [d1989, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1988 p = 1 := by simpa only [d1989, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10074 p hg
    simpa only [d1989, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10076 (p : Pattern) (guard : d1990 p = 1) : d327 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1985 p = 1 := by simpa only [d1990, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10056 p hg
    simpa only [d1990, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1989 p = 1 := by simpa only [d1990, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10075 p hg
    simpa only [d1990, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10077 (p : Pattern) (guard : d1949 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare10078 (p : Pattern) (guard : d1950 p = 1) : d389 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1946 p = 1 := by simpa only [d1950, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9489 p hg
    simpa only [d1950, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1949 p = 1 := by simpa only [d1950, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10077 p hg
    simpa only [d1950, d389, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10079 (p : Pattern) (guard : d1953 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
end NetHack.Sokoban32Refined
