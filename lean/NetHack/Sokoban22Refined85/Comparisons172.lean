/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24080 (p : Pattern) (guard : d4474 p = 1) : d3040 p ≤ (0 : Int) + d1953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3040, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24079 p hg
    simpa only [d3040, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3040, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16539 p hg
    simpa only [d3040, d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24081 (p : Pattern) (guard : d4474 p = 1) : d3041 p ≤ (0 : Int) + d1954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3041, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24077 p hg
    simpa only [d3041, d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3041, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24080 p hg
    simpa only [d3041, d1954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24082 (p : Pattern) (guard : d4474 p = 1) : d3042 p ≤ (0 : Int) + d1959 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3042, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24038 p hg
    simpa only [d3042, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3042, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16542 p hg
    simpa only [d3042, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24083 (p : Pattern) (guard : d4474 p = 1) : d3043 p ≤ (0 : Int) + d1968 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3043, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24044 p hg
    simpa only [d3043, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3043, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16544 p hg
    simpa only [d3043, d1968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24084 (p : Pattern) (guard : d4474 p = 1) : d3044 p ≤ (0 : Int) + d1969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3044, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24082 p hg
    simpa only [d3044, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3044, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3044, d1969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24085 (p : Pattern) (guard : d4474 p = 1) : d3045 p ≤ (0 : Int) + d1970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3045, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24081 p hg
    simpa only [d3045, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3045, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24084 p hg
    simpa only [d3045, d1970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24086 (p : Pattern) (guard : d4474 p = 1) : d3046 p ≤ (0 : Int) + d1971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3046, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24084 p hg
    simpa only [d3046, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3046, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24034 p hg
    simpa only [d3046, d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24087 (p : Pattern) (guard : d4474 p = 1) : d3047 p ≤ (0 : Int) + d1972 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3047, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24085 p hg
    simpa only [d3047, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3047, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24086 p hg
    simpa only [d3047, d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24088 (p : Pattern) (guard : d4474 p = 1) : d3048 p ≤ (0 : Int) + d1973 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3048, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24065 p hg
    simpa only [d3048, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3048, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d3048, d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24089 (p : Pattern) (guard : d0 p = 1) : d1905 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24090 (p : Pattern) (guard : d4474 p = 1) : d3049 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3049, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4474, d3049, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3049, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24089 p hg
    simpa only [d4474, d3049, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24091 (p : Pattern) (guard : d4474 p = 1) : d3050 p ≤ (0 : Int) + d1974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3050, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24090 p hg
    simpa only [d3050, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3050, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d3050, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24092 (p : Pattern) (guard : d4474 p = 1) : d3051 p ≤ (0 : Int) + d1975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3051, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3051, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3051, d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24091 p hg
    simpa only [d3051, d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24093 (p : Pattern) (guard : d4474 p = 1) : d3052 p ≤ (0 : Int) + d1976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3052, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24092 p hg
    simpa only [d3052, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3052, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3052, d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24094 (p : Pattern) (guard : d4474 p = 1) : d3053 p ≤ (0 : Int) + d1977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3053, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24093 p hg
    simpa only [d3053, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3053, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3053, d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24095 (p : Pattern) (guard : d4474 p = 1) : d3054 p ≤ (0 : Int) + d1978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3054, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24087 p hg
    simpa only [d3054, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3054, d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24094 p hg
    simpa only [d3054, d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24096 (p : Pattern) (guard : d4474 p = 1) : d3055 p ≤ (0 : Int) + d1979 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3055, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24080 p hg
    simpa only [d3055, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3055, d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3055, d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24097 (p : Pattern) (guard : d4474 p = 1) : d3056 p ≤ (0 : Int) + d1980 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3056, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3056, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3056, d1980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d3056, d1980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24098 (p : Pattern) (guard : d4474 p = 1) : d3057 p ≤ (0 : Int) + d1981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3057, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24096 p hg
    simpa only [d3057, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3057, d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24097 p hg
    simpa only [d3057, d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24099 (p : Pattern) (guard : d4474 p = 1) : d3058 p ≤ (0 : Int) + d1982 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3058, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3058, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3058, d1982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d3058, d1982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24100 (p : Pattern) (guard : d4474 p = 1) : d3059 p ≤ (0 : Int) + d1983 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3059, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24099 p hg
    simpa only [d3059, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3059, d1983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3059, d1983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24101 (p : Pattern) (guard : d4474 p = 1) : d3060 p ≤ (0 : Int) + d1984 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3060, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24098 p hg
    simpa only [d3060, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3060, d1984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24100 p hg
    simpa only [d3060, d1984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24102 (p : Pattern) (guard : d4474 p = 1) : d3061 p ≤ (0 : Int) + d1985 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3061, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24091 p hg
    simpa only [d3061, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3061, d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3061, d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24103 (p : Pattern) (guard : d4474 p = 1) : d3062 p ≤ (0 : Int) + d1986 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3062, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24102 p hg
    simpa only [d3062, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3062, d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3062, d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24104 (p : Pattern) (guard : d4474 p = 1) : d3063 p ≤ (0 : Int) + d1987 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3063, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24103 p hg
    simpa only [d3063, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3063, d1987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3063, d1987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24105 (p : Pattern) (guard : d4474 p = 1) : d3064 p ≤ (0 : Int) + d1988 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3064, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24101 p hg
    simpa only [d3064, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3064, d1988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24104 p hg
    simpa only [d3064, d1988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24106 (p : Pattern) (guard : d4474 p = 1) : d3065 p ≤ (0 : Int) + d1989 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3065, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24095 p hg
    simpa only [d3065, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3065, d1989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24105 p hg
    simpa only [d3065, d1989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24107 (p : Pattern) (guard : d4474 p = 1) : d3066 p ≤ (0 : Int) + d1990 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3066, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24074 p hg
    simpa only [d3066, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3066, d1990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24106 p hg
    simpa only [d3066, d1990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24108 (p : Pattern) (guard : d4474 p = 1) : d3067 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3067, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24034 p hg
    simpa only [d3067, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3067, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3067, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24109 (p : Pattern) (guard : d4474 p = 1) : d3068 p ≤ (0 : Int) + d1992 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3068, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24108 p hg
    simpa only [d3068, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3068, d1992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3068, d1992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24110 (p : Pattern) (guard : d4474 p = 1) : d3069 p ≤ (0 : Int) + d1993 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3069, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24109 p hg
    simpa only [d3069, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3069, d1993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3069, d1993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24111 (p : Pattern) (guard : d4474 p = 1) : d3070 p ≤ (0 : Int) + d1994 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3070, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24110 p hg
    simpa only [d3070, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3070, d1994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3070, d1994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24112 (p : Pattern) (guard : d4474 p = 1) : d3071 p ≤ (0 : Int) + d1995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3071, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24106 p hg
    simpa only [d3071, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3071, d1995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24111 p hg
    simpa only [d3071, d1995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24113 (p : Pattern) (guard : d4474 p = 1) : d3072 p ≤ (0 : Int) + d1996 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3072, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24107 p hg
    simpa only [d3072, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3072, d1996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24112 p hg
    simpa only [d3072, d1996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24114 (p : Pattern) (guard : d4474 p = 1) : d2998 p ≤ (0 : Int) + d1997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2998, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24027 p hg
    simpa only [d2998, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2998, d1997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24032 p hg
    simpa only [d2998, d1997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24115 (p : Pattern) (guard : d4474 p = 1) : d3001 p ≤ (0 : Int) + d1998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3001, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24114 p hg
    simpa only [d3001, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3001, d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24035 p hg
    simpa only [d3001, d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24116 (p : Pattern) (guard : d4474 p = 1) : d3014 p ≤ (0 : Int) + d1999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3014, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24115 p hg
    simpa only [d3014, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3014, d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24050 p hg
    simpa only [d3014, d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24117 (p : Pattern) (guard : d4474 p = 1) : d3017 p ≤ (0 : Int) + d2000 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3017, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24027 p hg
    simpa only [d3017, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3017, d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24057 p hg
    simpa only [d3017, d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24118 (p : Pattern) (guard : d4474 p = 1) : d3019 p ≤ (0 : Int) + d2001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3019, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24117 p hg
    simpa only [d3019, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3019, d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24059 p hg
    simpa only [d3019, d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24119 (p : Pattern) (guard : d4474 p = 1) : d3022 p ≤ (0 : Int) + d2002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3022, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24118 p hg
    simpa only [d3022, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3022, d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24062 p hg
    simpa only [d3022, d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24120 (p : Pattern) (guard : d4474 p = 1) : d3031 p ≤ (0 : Int) + d2003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3031, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24119 p hg
    simpa only [d3031, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3031, d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24072 p hg
    simpa only [d3031, d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24121 (p : Pattern) (guard : d4474 p = 1) : d3032 p ≤ (0 : Int) + d2004 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3032, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24116 p hg
    simpa only [d3032, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3032, d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24120 p hg
    simpa only [d3032, d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24122 (p : Pattern) (guard : d4474 p = 1) : d3066 p ≤ (0 : Int) + d2005 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3066, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24121 p hg
    simpa only [d3066, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3066, d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24106 p hg
    simpa only [d3066, d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24123 (p : Pattern) (guard : d4474 p = 1) : d3073 p ≤ (0 : Int) + d2006 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3073, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24106 p hg
    simpa only [d3073, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3073, d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3073, d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24124 (p : Pattern) (guard : d4474 p = 1) : d3074 p ≤ (0 : Int) + d2007 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3074, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24122 p hg
    simpa only [d3074, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3074, d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24123 p hg
    simpa only [d3074, d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24125 (p : Pattern) (guard : d4474 p = 1) : d3075 p ≤ (0 : Int) + d2008 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3075, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24113 p hg
    simpa only [d3075, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3075, d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24124 p hg
    simpa only [d3075, d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24126 (p : Pattern) (guard : d4474 p = 1) : d3076 p ≤ (0 : Int) + d2009 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3076, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23999 p hg
    simpa only [d3076, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3076, d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24125 p hg
    simpa only [d3076, d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24127 (p : Pattern) (guard : d4474 p = 1) : d3077 p ≤ (0 : Int) + d2010 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3077, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24021 p hg
    simpa only [d3077, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3077, d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24126 p hg
    simpa only [d3077, d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24128 (p : Pattern) (guard : d0 p = 1) : d3079 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24129 (p : Pattern) (guard : d4474 p = 1) : d3080 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3080, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d3080, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3080, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24128 p hg
    simpa only [d4474, d3080, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24130 (p : Pattern) (guard : d4474 p = 1) : d3081 p ≤ (0 : Int) + d2014 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3081, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24129 p hg
    simpa only [d3081, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3081, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d3081, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24131 (p : Pattern) (guard : d4474 p = 1) : d3082 p ≤ (0 : Int) + d2015 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3082, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23944 p hg
    simpa only [d3082, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3082, d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24130 p hg
    simpa only [d3082, d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24132 (p : Pattern) (guard : d4474 p = 1) : d3083 p ≤ (0 : Int) + d2016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3083, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23944 p hg
    simpa only [d3083, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3083, d2016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24131 p hg
    simpa only [d3083, d2016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24133 (p : Pattern) (guard : d4474 p = 1) : d3084 p ≤ (0 : Int) + d2017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3084, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24131 p hg
    simpa only [d3084, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3084, d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23954 p hg
    simpa only [d3084, d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24134 (p : Pattern) (guard : d4474 p = 1) : d3085 p ≤ (0 : Int) + d2018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3085, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24132 p hg
    simpa only [d3085, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3085, d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24133 p hg
    simpa only [d3085, d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24135 (p : Pattern) (guard : d4474 p = 1) : d3086 p ≤ (0 : Int) + d2019 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3086, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d3086, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3086, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d3086, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24136 (p : Pattern) (guard : d4474 p = 1) : d3087 p ≤ (0 : Int) + d2020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3087, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23957 p hg
    simpa only [d3087, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3087, d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24135 p hg
    simpa only [d3087, d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24137 (p : Pattern) (guard : d4474 p = 1) : d3088 p ≤ (0 : Int) + d2021 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3088, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d3088, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3088, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d3088, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24138 (p : Pattern) (guard : d4474 p = 1) : d3089 p ≤ (0 : Int) + d2022 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3089, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23959 p hg
    simpa only [d3089, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3089, d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3089, d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24139 (p : Pattern) (guard : d4474 p = 1) : d3090 p ≤ (0 : Int) + d2023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3090, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24137 p hg
    simpa only [d3090, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3090, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d3090, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24140 (p : Pattern) (guard : d4474 p = 1) : d3091 p ≤ (0 : Int) + d2024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3091, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24136 p hg
    simpa only [d3091, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3091, d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24139 p hg
    simpa only [d3091, d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24141 (p : Pattern) (guard : d4474 p = 1) : d3092 p ≤ (0 : Int) + d2025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3092, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23930 p hg
    simpa only [d3092, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3092, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d3092, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24142 (p : Pattern) (guard : d4474 p = 1) : d3093 p ≤ (0 : Int) + d2026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3093, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24141 p hg
    simpa only [d3093, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3093, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23937 p hg
    simpa only [d3093, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24143 (p : Pattern) (guard : d4474 p = 1) : d3094 p ≤ (0 : Int) + d2027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3094, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24140 p hg
    simpa only [d3094, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3094, d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24142 p hg
    simpa only [d3094, d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24144 (p : Pattern) (guard : d4474 p = 1) : d3095 p ≤ (0 : Int) + d2028 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3095, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24134 p hg
    simpa only [d3095, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3095, d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24143 p hg
    simpa only [d3095, d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24145 (p : Pattern) (guard : d0 p = 1) : d3097 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24146 (p : Pattern) (guard : d4474 p = 1) : d3098 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3098, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d3098, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3098, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24145 p hg
    simpa only [d4474, d3098, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24147 (p : Pattern) (guard : d4474 p = 1) : d3099 p ≤ (0 : Int) + d2032 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3099, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24146 p hg
    simpa only [d3099, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3099, d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16609 p hg
    simpa only [d3099, d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24148 (p : Pattern) (guard : d4474 p = 1) : d3100 p ≤ (0 : Int) + d2033 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3100, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23944 p hg
    simpa only [d3100, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3100, d2033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24147 p hg
    simpa only [d3100, d2033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24149 (p : Pattern) (guard : d4474 p = 1) : d3101 p ≤ (0 : Int) + d2034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3101, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24130 p hg
    simpa only [d3101, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3101, d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d3101, d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24150 (p : Pattern) (guard : d4474 p = 1) : d3102 p ≤ (0 : Int) + d2035 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3102, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24148 p hg
    simpa only [d3102, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3102, d2035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24149 p hg
    simpa only [d3102, d2035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24151 (p : Pattern) (guard : d4474 p = 1) : d3103 p ≤ (0 : Int) + d2036 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3103, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24130 p hg
    simpa only [d3103, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3103, d2036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d3103, d2036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24152 (p : Pattern) (guard : d4474 p = 1) : d3104 p ≤ (0 : Int) + d2037 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3104, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24151 p hg
    simpa only [d3104, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3104, d2037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d3104, d2037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24153 (p : Pattern) (guard : d4474 p = 1) : d3105 p ≤ (0 : Int) + d2038 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3105, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24150 p hg
    simpa only [d3105, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3105, d2038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24152 p hg
    simpa only [d3105, d2038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24154 (p : Pattern) (guard : d4474 p = 1) : d3106 p ≤ (0 : Int) + d2039 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3106, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24135 p hg
    simpa only [d3106, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3106, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d3106, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24155 (p : Pattern) (guard : d4474 p = 1) : d3107 p ≤ (0 : Int) + d2040 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3107, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d3107, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3107, d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23936 p hg
    simpa only [d3107, d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24156 (p : Pattern) (guard : d4474 p = 1) : d3108 p ≤ (0 : Int) + d2041 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3108, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24154 p hg
    simpa only [d3108, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3108, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24155 p hg
    simpa only [d3108, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24157 (p : Pattern) (guard : d4474 p = 1) : d3109 p ≤ (0 : Int) + d2042 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3109, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24138 p hg
    simpa only [d3109, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3109, d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3109, d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24158 (p : Pattern) (guard : d4474 p = 1) : d3110 p ≤ (0 : Int) + d2043 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3110, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24157 p hg
    simpa only [d3110, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3110, d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3110, d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24159 (p : Pattern) (guard : d4474 p = 1) : d3111 p ≤ (0 : Int) + d2044 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3111, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24156 p hg
    simpa only [d3111, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3111, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24158 p hg
    simpa only [d3111, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24160 (p : Pattern) (guard : d4474 p = 1) : d3112 p ≤ (0 : Int) + d2045 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3112, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24153 p hg
    simpa only [d3112, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3112, d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24159 p hg
    simpa only [d3112, d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24161 (p : Pattern) (guard : d4474 p = 1) : d3113 p ≤ (0 : Int) + d2046 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3113, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24144 p hg
    simpa only [d3113, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3113, d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24160 p hg
    simpa only [d3113, d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24162 (p : Pattern) (guard : d0 p = 1) : d1781 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24163 (p : Pattern) (guard : d4474 p = 1) : d3114 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3114, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d3114, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3114, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24162 p hg
    simpa only [d4474, d3114, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24164 (p : Pattern) (guard : d4474 p = 1) : d3115 p ≤ (0 : Int) + d2050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3115, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24163 p hg
    simpa only [d3115, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3115, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16626 p hg
    simpa only [d3115, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24165 (p : Pattern) (guard : d4474 p = 1) : d3116 p ≤ (0 : Int) + d2056 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3116, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d3116, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3116, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16628 p hg
    simpa only [d3116, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24166 (p : Pattern) (guard : d4474 p = 1) : d3117 p ≤ (0 : Int) + d2057 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3117, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24164 p hg
    simpa only [d3117, d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3117, d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24165 p hg
    simpa only [d3117, d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24167 (p : Pattern) (guard : d4474 p = 1) : d3118 p ≤ (0 : Int) + d2058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3118, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24166 p hg
    simpa only [d3118, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3118, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23961 p hg
    simpa only [d3118, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24168 (p : Pattern) (guard : d4474 p = 1) : d3119 p ≤ (0 : Int) + d2059 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3119, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24167 p hg
    simpa only [d3119, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3119, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23962 p hg
    simpa only [d3119, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24169 (p : Pattern) (guard : d0 p = 1) : d2061 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24170 (p : Pattern) (guard : d4474 p = 1) : d3120 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3120, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4474, d3120, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3120, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24169 p hg
    simpa only [d4474, d3120, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24171 (p : Pattern) (guard : d4474 p = 1) : d3121 p ≤ (0 : Int) + d2063 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3121, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24170 p hg
    simpa only [d3121, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3121, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16634 p hg
    simpa only [d3121, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24172 (p : Pattern) (guard : d4474 p = 1) : d3122 p ≤ (0 : Int) + d2064 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3122, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d3122, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3122, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24171 p hg
    simpa only [d3122, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24173 (p : Pattern) (guard : d4474 p = 1) : d3123 p ≤ (0 : Int) + d2065 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24172 p hg
    simpa only [d3123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24174 (p : Pattern) (guard : d4474 p = 1) : d3124 p ≤ (0 : Int) + d2066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3124, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24173 p hg
    simpa only [d3124, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3124, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3124, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24175 (p : Pattern) (guard : d4474 p = 1) : d3125 p ≤ (0 : Int) + d2067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3125, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24168 p hg
    simpa only [d3125, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3125, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24174 p hg
    simpa only [d3125, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24176 (p : Pattern) (guard : d4474 p = 1) : d3126 p ≤ (0 : Int) + d2073 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3126, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d3126, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3126, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16640 p hg
    simpa only [d3126, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24177 (p : Pattern) (guard : d4474 p = 1) : d3127 p ≤ (0 : Int) + d2074 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3127, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24176 p hg
    simpa only [d3127, d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3127, d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23957 p hg
    simpa only [d3127, d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24178 (p : Pattern) (guard : d4474 p = 1) : d3128 p ≤ (0 : Int) + d2075 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3128, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23950 p hg
    simpa only [d3128, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3128, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d3128, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24179 (p : Pattern) (guard : d4474 p = 1) : d3129 p ≤ (0 : Int) + d2076 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3129, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24177 p hg
    simpa only [d3129, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3129, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24178 p hg
    simpa only [d3129, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24180 (p : Pattern) (guard : d4474 p = 1) : d3130 p ≤ (0 : Int) + d2077 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3130, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24179 p hg
    simpa only [d3130, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3130, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23972 p hg
    simpa only [d3130, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24181 (p : Pattern) (guard : d4474 p = 1) : d3131 p ≤ (0 : Int) + d2078 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3131, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24171 p hg
    simpa only [d3131, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3131, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3131, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24182 (p : Pattern) (guard : d4474 p = 1) : d3132 p ≤ (0 : Int) + d2079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3132, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24181 p hg
    simpa only [d3132, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3132, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3132, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24183 (p : Pattern) (guard : d4474 p = 1) : d3133 p ≤ (0 : Int) + d2080 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3133, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24182 p hg
    simpa only [d3133, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3133, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3133, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24184 (p : Pattern) (guard : d4474 p = 1) : d3134 p ≤ (0 : Int) + d2081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3134, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24180 p hg
    simpa only [d3134, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3134, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24183 p hg
    simpa only [d3134, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24185 (p : Pattern) (guard : d4474 p = 1) : d3135 p ≤ (0 : Int) + d2082 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3135, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24175 p hg
    simpa only [d3135, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3135, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24184 p hg
    simpa only [d3135, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24186 (p : Pattern) (guard : d4474 p = 1) : d3136 p ≤ (0 : Int) + d2083 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3136, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24161 p hg
    simpa only [d3136, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3136, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24185 p hg
    simpa only [d3136, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24187 (p : Pattern) (guard : d4474 p = 1) : d3137 p ≤ (0 : Int) + d2084 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3137, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24185 p hg
    simpa only [d3137, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3137, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3137, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24188 (p : Pattern) (guard : d4474 p = 1) : d3138 p ≤ (0 : Int) + d2085 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3138, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24186 p hg
    simpa only [d3138, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3138, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24187 p hg
    simpa only [d3138, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24189 (p : Pattern) (guard : d4474 p = 1) : d3139 p ≤ (0 : Int) + d2086 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3139, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24013 p hg
    simpa only [d3139, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3139, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24188 p hg
    simpa only [d3139, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24190 (p : Pattern) (guard : d4474 p = 1) : d3140 p ≤ (0 : Int) + d2087 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3140, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23999 p hg
    simpa only [d3140, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3140, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24189 p hg
    simpa only [d3140, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24191 (p : Pattern) (guard : d4474 p = 1) : d3141 p ≤ (0 : Int) + d2088 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3141, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24031 p hg
    simpa only [d3141, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3141, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3141, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24192 (p : Pattern) (guard : d4474 p = 1) : d3142 p ≤ (0 : Int) + d2089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3142, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24058 p hg
    simpa only [d3142, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3142, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24191 p hg
    simpa only [d3142, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24193 (p : Pattern) (guard : d4474 p = 1) : d3143 p ≤ (0 : Int) + d2090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3143, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24191 p hg
    simpa only [d3143, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3143, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3143, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24194 (p : Pattern) (guard : d4474 p = 1) : d3144 p ≤ (0 : Int) + d2091 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3144, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24192 p hg
    simpa only [d3144, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3144, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24193 p hg
    simpa only [d3144, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24195 (p : Pattern) (guard : d4474 p = 1) : d3145 p ≤ (0 : Int) + d2092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3145, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d3145, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3145, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3145, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24196 (p : Pattern) (guard : d4474 p = 1) : d3146 p ≤ (0 : Int) + d2093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3146, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24067 p hg
    simpa only [d3146, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3146, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24195 p hg
    simpa only [d3146, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24197 (p : Pattern) (guard : d4474 p = 1) : d3147 p ≤ (0 : Int) + d2094 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3147, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24195 p hg
    simpa only [d3147, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3147, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3147, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24198 (p : Pattern) (guard : d4474 p = 1) : d3148 p ≤ (0 : Int) + d2095 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3148, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24196 p hg
    simpa only [d3148, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3148, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24197 p hg
    simpa only [d3148, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24199 (p : Pattern) (guard : d4474 p = 1) : d3149 p ≤ (0 : Int) + d2096 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3149, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24194 p hg
    simpa only [d3149, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3149, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24198 p hg
    simpa only [d3149, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24200 (p : Pattern) (guard : d4474 p = 1) : d3150 p ≤ (0 : Int) + d2097 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3150, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24051 p hg
    simpa only [d3150, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3150, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24199 p hg
    simpa only [d3150, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24201 (p : Pattern) (guard : d4474 p = 1) : d3151 p ≤ (0 : Int) + d2098 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3151, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3151, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3151, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3151, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24202 (p : Pattern) (guard : d4474 p = 1) : d3152 p ≤ (0 : Int) + d2099 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3152, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24096 p hg
    simpa only [d3152, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3152, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24201 p hg
    simpa only [d3152, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24203 (p : Pattern) (guard : d4474 p = 1) : d3153 p ≤ (0 : Int) + d2100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3153, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24201 p hg
    simpa only [d3153, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3153, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3153, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24204 (p : Pattern) (guard : d4474 p = 1) : d3154 p ≤ (0 : Int) + d2101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3154, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24202 p hg
    simpa only [d3154, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3154, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24203 p hg
    simpa only [d3154, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24205 (p : Pattern) (guard : d4474 p = 1) : d3155 p ≤ (0 : Int) + d2102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3155, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24204 p hg
    simpa only [d3155, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3155, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24104 p hg
    simpa only [d3155, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24206 (p : Pattern) (guard : d4474 p = 1) : d3156 p ≤ (0 : Int) + d2103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3156, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24095 p hg
    simpa only [d3156, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3156, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24205 p hg
    simpa only [d3156, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24207 (p : Pattern) (guard : d4474 p = 1) : d3157 p ≤ (0 : Int) + d2104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3157, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24200 p hg
    simpa only [d3157, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3157, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24206 p hg
    simpa only [d3157, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24208 (p : Pattern) (guard : d4474 p = 1) : d3158 p ≤ (0 : Int) + d2105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3158, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24206 p hg
    simpa only [d3158, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3158, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24111 p hg
    simpa only [d3158, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24209 (p : Pattern) (guard : d4474 p = 1) : d3159 p ≤ (0 : Int) + d2106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3159, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24207 p hg
    simpa only [d3159, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3159, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24208 p hg
    simpa only [d3159, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24210 (p : Pattern) (guard : d0 p = 1) : d1951 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24211 (p : Pattern) (guard : d4474 p = 1) : d3160 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3160, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d3160, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3160, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24210 p hg
    simpa only [d4474, d3160, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24212 (p : Pattern) (guard : d4474 p = 1) : d3161 p ≤ (0 : Int) + d2110 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3161, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24211 p hg
    simpa only [d3161, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3161, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16676 p hg
    simpa only [d3161, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24213 (p : Pattern) (guard : d4474 p = 1) : d3162 p ≤ (0 : Int) + d2111 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3162, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24212 p hg
    simpa only [d3162, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3162, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3162, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24214 (p : Pattern) (guard : d4474 p = 1) : d3163 p ≤ (0 : Int) + d2112 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3163, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24077 p hg
    simpa only [d3163, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3163, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24213 p hg
    simpa only [d3163, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24215 (p : Pattern) (guard : d4474 p = 1) : d3164 p ≤ (0 : Int) + d2113 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3164, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24080 p hg
    simpa only [d3164, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3164, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3164, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24216 (p : Pattern) (guard : d4474 p = 1) : d3165 p ≤ (0 : Int) + d2114 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3165, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24215 p hg
    simpa only [d3165, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3165, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24034 p hg
    simpa only [d3165, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24217 (p : Pattern) (guard : d4474 p = 1) : d3166 p ≤ (0 : Int) + d2115 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3166, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24214 p hg
    simpa only [d3166, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3166, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24216 p hg
    simpa only [d3166, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24218 (p : Pattern) (guard : d4474 p = 1) : d3167 p ≤ (0 : Int) + d2116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3167, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24065 p hg
    simpa only [d3167, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3167, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d3167, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24219 (p : Pattern) (guard : d4474 p = 1) : d3168 p ≤ (0 : Int) + d2117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3168, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3168, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3168, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24218 p hg
    simpa only [d3168, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
