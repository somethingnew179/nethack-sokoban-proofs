/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons234
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32900 (p : Pattern) (guard : d6558 p = 1) : d1873 p ≤ (2 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32898 p hg
    simpa only [d6558, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32899 p hg
    simpa only [d6558, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32901 (p : Pattern) (guard : d6558 p = 1) : d1874 p ≤ (2 : Int) + d7391 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1874, d7391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d1874, d7391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1874, d7391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32900 p hg
    simpa only [d1874, d7391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32902 (p : Pattern) (guard : d6558 p = 1) : d1875 p ≤ (2 : Int) + d7392 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1875, d7392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32901 p hg
    simpa only [d1875, d7392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1875, d7392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32900 p hg
    simpa only [d1875, d7392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32903 (p : Pattern) (guard : d6558 p = 1) : d1876 p ≤ (2 : Int) + d7393 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1876, d7393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32902 p hg
    simpa only [d1876, d7393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1876, d7393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1876, d7393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32904 (p : Pattern) (guard : d6558 p = 1) : d2994 p ≤ (2 : Int) + d7394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2994, d7394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32896 p hg
    simpa only [d2994, d7394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2994, d7394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32903 p hg
    simpa only [d2994, d7394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32905 (p : Pattern) (guard : d5842 p = 1) : d5 p ≤ (2 : Int) + d5 p := by
  omega
theorem compare32906 (p : Pattern) (guard : d6558 p = 1) : d107 p ≤ (2 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32905 p hg
    simpa only [d6558, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32892 p hg
    simpa only [d6558, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32907 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32908 (p : Pattern) (guard : d5842 p = 1) : d1963 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32907 p hg
    simpa only [d5842, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d5842, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32909 (p : Pattern) (guard : d6558 p = 1) : d1964 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32908 p hg
    simpa only [d6558, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32910 (p : Pattern) (guard : d6558 p = 1) : d2129 p ≤ (2 : Int) + d7395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2129, d7395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d2129, d7395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2129, d7395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d2129, d7395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32911 (p : Pattern) (guard : d6558 p = 1) : d2130 p ≤ (2 : Int) + d7396 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2130, d7396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32910 p hg
    simpa only [d2130, d7396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2130, d7396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d2130, d7396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32912 (p : Pattern) (guard : d6558 p = 1) : d2995 p ≤ (2 : Int) + d7397 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2995, d7397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d2995, d7397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2995, d7397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32911 p hg
    simpa only [d2995, d7397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32913 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32914 (p : Pattern) (guard : d5842 p = 1) : d1880 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32913 p hg
    simpa only [d5842, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d5842, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32915 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32916 (p : Pattern) (guard : d6558 p = 1) : d1881 p ≤ (2 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32914 p hg
    simpa only [d6558, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32915 p hg
    simpa only [d6558, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32917 (p : Pattern) (guard : d6558 p = 1) : d1882 p ≤ (2 : Int) + d7398 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1882, d7398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d1882, d7398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1882, d7398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32916 p hg
    simpa only [d1882, d7398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32918 (p : Pattern) (guard : d6558 p = 1) : d1883 p ≤ (2 : Int) + d7399 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1883, d7399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32917 p hg
    simpa only [d1883, d7399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1883, d7399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32916 p hg
    simpa only [d1883, d7399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32919 (p : Pattern) (guard : d6558 p = 1) : d1884 p ≤ (2 : Int) + d7400 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1884, d7400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32918 p hg
    simpa only [d1884, d7400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1884, d7400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1884, d7400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32920 (p : Pattern) (guard : d6558 p = 1) : d2996 p ≤ (2 : Int) + d7401 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2996, d7401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32912 p hg
    simpa only [d2996, d7401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2996, d7401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32919 p hg
    simpa only [d2996, d7401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32921 (p : Pattern) (guard : d6558 p = 1) : d2997 p ≤ (2 : Int) + d7402 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2997, d7402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32904 p hg
    simpa only [d2997, d7402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2997, d7402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32920 p hg
    simpa only [d2997, d7402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32922 (p : Pattern) (guard : d6558 p = 1) : d2998 p ≤ (2 : Int) + d7403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2998, d7403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32904 p hg
    simpa only [d2998, d7403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2998, d7403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32921 p hg
    simpa only [d2998, d7403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32923 (p : Pattern) (guard : d6558 p = 1) : d2999 p ≤ (2 : Int) + d7404 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2999, d7404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d2999, d7404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2999, d7404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2999, d7404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32924 (p : Pattern) (guard : d6558 p = 1) : d3000 p ≤ (2 : Int) + d7405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3000, d7405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32921 p hg
    simpa only [d3000, d7405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3000, d7405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d3000, d7405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32925 (p : Pattern) (guard : d6558 p = 1) : d3001 p ≤ (2 : Int) + d7406 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3001, d7406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32922 p hg
    simpa only [d3001, d7406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3001, d7406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32924 p hg
    simpa only [d3001, d7406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32926 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32927 (p : Pattern) (guard : d5842 p = 1) : d1945 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32926 p hg
    simpa only [d5842, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d5842, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32928 (p : Pattern) (guard : d6558 p = 1) : d1946 p ≤ (2 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32927 p hg
    simpa only [d6558, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32915 p hg
    simpa only [d6558, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32929 (p : Pattern) (guard : d6558 p = 1) : d1947 p ≤ (2 : Int) + d7407 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1947, d7407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d1947, d7407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1947, d7407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32928 p hg
    simpa only [d1947, d7407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32930 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32931 (p : Pattern) (guard : d5842 p = 1) : d102 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32930 p hg
    simpa only [d5842, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d5842, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32932 (p : Pattern) (guard : d6558 p = 1) : d1955 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32931 p hg
    simpa only [d6558, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32933 (p : Pattern) (guard : d6558 p = 1) : d1956 p ≤ (2 : Int) + d7408 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1956, d7408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d1956, d7408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1956, d7408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32932 p hg
    simpa only [d1956, d7408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32934 (p : Pattern) (guard : d6558 p = 1) : d1957 p ≤ (2 : Int) + d7409 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1957, d7409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d1957, d7409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1957, d7409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32933 p hg
    simpa only [d1957, d7409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32935 (p : Pattern) (guard : d6558 p = 1) : d3002 p ≤ (2 : Int) + d7410 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3002, d7410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d3002, d7410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3002, d7410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32934 p hg
    simpa only [d3002, d7410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32936 (p : Pattern) (guard : d5842 p = 1) : d3 p ≤ (2 : Int) + d3 p := by
  omega
theorem compare32937 (p : Pattern) (guard : d6558 p = 1) : d116 p ≤ (2 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32936 p hg
    simpa only [d6558, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32899 p hg
    simpa only [d6558, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32938 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32939 (p : Pattern) (guard : d5842 p = 1) : d1891 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32938 p hg
    simpa only [d5842, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d5842, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32940 (p : Pattern) (guard : d6558 p = 1) : d1892 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32939 p hg
    simpa only [d6558, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32941 (p : Pattern) (guard : d6558 p = 1) : d1893 p ≤ (2 : Int) + d7411 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1893, d7411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d1893, d7411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1893, d7411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32940 p hg
    simpa only [d1893, d7411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32942 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32943 (p : Pattern) (guard : d5842 p = 1) : d1894 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32942 p hg
    simpa only [d5842, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d5842, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32944 (p : Pattern) (guard : d6558 p = 1) : d1895 p ≤ (2 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32943 p hg
    simpa only [d6558, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32915 p hg
    simpa only [d6558, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32945 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32946 (p : Pattern) (guard : d5842 p = 1) : d115 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32945 p hg
    simpa only [d5842, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32947 (p : Pattern) (guard : d6558 p = 1) : d1896 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32946 p hg
    simpa only [d6558, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32948 (p : Pattern) (guard : d6558 p = 1) : d1897 p ≤ (2 : Int) + d7412 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1897, d7412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d1897, d7412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1897, d7412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32947 p hg
    simpa only [d1897, d7412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32949 (p : Pattern) (guard : d6558 p = 1) : d1898 p ≤ (2 : Int) + d7413 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1898, d7413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32941 p hg
    simpa only [d1898, d7413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1898, d7413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32948 p hg
    simpa only [d1898, d7413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32950 (p : Pattern) (guard : d6558 p = 1) : d1899 p ≤ (2 : Int) + d7414 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1899, d7414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32949 p hg
    simpa only [d1899, d7414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1899, d7414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1899, d7414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32951 (p : Pattern) (guard : d6558 p = 1) : d3003 p ≤ (2 : Int) + d7415 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3003, d7415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32935 p hg
    simpa only [d3003, d7415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3003, d7415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32950 p hg
    simpa only [d3003, d7415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32952 (p : Pattern) (guard : d5842 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare32953 (p : Pattern) (guard : d6558 p = 1) : d120 p ≤ (2 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32952 p hg
    simpa only [d6558, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32915 p hg
    simpa only [d6558, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32954 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32955 (p : Pattern) (guard : d5842 p = 1) : d119 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32954 p hg
    simpa only [d5842, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32956 (p : Pattern) (guard : d6558 p = 1) : d317 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32955 p hg
    simpa only [d6558, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32957 (p : Pattern) (guard : d6558 p = 1) : d1901 p ≤ (2 : Int) + d7412 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1901, d7412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32953 p hg
    simpa only [d1901, d7412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1901, d7412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32956 p hg
    simpa only [d1901, d7412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32958 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32959 (p : Pattern) (guard : d5842 p = 1) : d1902 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32958 p hg
    simpa only [d5842, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5842, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32960 (p : Pattern) (guard : d6558 p = 1) : d1903 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32959 p hg
    simpa only [d6558, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32961 (p : Pattern) (guard : d6558 p = 1) : d1904 p ≤ (2 : Int) + d7286 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1904, d7286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32960 p hg
    simpa only [d1904, d7286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1904, d7286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32956 p hg
    simpa only [d1904, d7286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32962 (p : Pattern) (guard : d6558 p = 1) : d1905 p ≤ (2 : Int) + d7416 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1905, d7416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32957 p hg
    simpa only [d1905, d7416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1905, d7416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32961 p hg
    simpa only [d1905, d7416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32963 (p : Pattern) (guard : d6558 p = 1) : d1906 p ≤ (2 : Int) + d7417 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1906, d7417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32962 p hg
    simpa only [d1906, d7417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1906, d7417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1906, d7417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32964 (p : Pattern) (guard : d6558 p = 1) : d3004 p ≤ (2 : Int) + d7418 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3004, d7418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32935 p hg
    simpa only [d3004, d7418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3004, d7418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32963 p hg
    simpa only [d3004, d7418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32965 (p : Pattern) (guard : d6558 p = 1) : d3005 p ≤ (2 : Int) + d7419 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3005, d7419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32951 p hg
    simpa only [d3005, d7419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3005, d7419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32964 p hg
    simpa only [d3005, d7419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32966 (p : Pattern) (guard : d6558 p = 1) : d3006 p ≤ (2 : Int) + d7420 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3006, d7420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32935 p hg
    simpa only [d3006, d7420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3006, d7420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3006, d7420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32967 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32968 (p : Pattern) (guard : d5842 p = 1) : d1960 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32967 p hg
    simpa only [d5842, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5842, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32969 (p : Pattern) (guard : d6558 p = 1) : d1961 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32968 p hg
    simpa only [d6558, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32970 (p : Pattern) (guard : d6558 p = 1) : d1962 p ≤ (2 : Int) + d7421 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1962, d7421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d1962, d7421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1962, d7421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32969 p hg
    simpa only [d1962, d7421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32971 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32972 (p : Pattern) (guard : d5842 p = 1) : d106 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32971 p hg
    simpa only [d5842, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32973 (p : Pattern) (guard : d6558 p = 1) : d348 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32972 p hg
    simpa only [d6558, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32974 (p : Pattern) (guard : d6558 p = 1) : d1965 p ≤ (2 : Int) + d7261 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1965, d7261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32909 p hg
    simpa only [d1965, d7261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1965, d7261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32973 p hg
    simpa only [d1965, d7261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32975 (p : Pattern) (guard : d6558 p = 1) : d1966 p ≤ (2 : Int) + d7422 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1966, d7422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32970 p hg
    simpa only [d1966, d7422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1966, d7422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32974 p hg
    simpa only [d1966, d7422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32976 (p : Pattern) (guard : d6558 p = 1) : d3007 p ≤ (2 : Int) + d7423 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3007, d7423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32906 p hg
    simpa only [d3007, d7423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3007, d7423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32975 p hg
    simpa only [d3007, d7423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32977 (p : Pattern) (guard : d6558 p = 1) : d3008 p ≤ (2 : Int) + d7424 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3008, d7424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32976 p hg
    simpa only [d3008, d7424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3008, d7424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3008, d7424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32978 (p : Pattern) (guard : d6558 p = 1) : d3009 p ≤ (2 : Int) + d7425 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3009, d7425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32966 p hg
    simpa only [d3009, d7425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3009, d7425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d3009, d7425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32979 (p : Pattern) (guard : d6558 p = 1) : d3010 p ≤ (2 : Int) + d7426 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3010, d7426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32965 p hg
    simpa only [d3010, d7426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3010, d7426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32978 p hg
    simpa only [d3010, d7426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32980 (p : Pattern) (guard : d6558 p = 1) : d3011 p ≤ (2 : Int) + d7427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3011, d7427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32818 p hg
    simpa only [d3011, d7427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3011, d7427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3011, d7427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32981 (p : Pattern) (guard : d6558 p = 1) : d3012 p ≤ (2 : Int) + d7428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3012, d7428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32978 p hg
    simpa only [d3012, d7428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3012, d7428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32980 p hg
    simpa only [d3012, d7428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32982 (p : Pattern) (guard : d6558 p = 1) : d3013 p ≤ (2 : Int) + d7429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3013, d7429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32979 p hg
    simpa only [d3013, d7429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3013, d7429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32981 p hg
    simpa only [d3013, d7429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32983 (p : Pattern) (guard : d6558 p = 1) : d3014 p ≤ (2 : Int) + d7430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3014, d7430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32925 p hg
    simpa only [d3014, d7430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3014, d7430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32982 p hg
    simpa only [d3014, d7430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32984 (p : Pattern) (guard : d6558 p = 1) : d2124 p ≤ (2 : Int) + d7431 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2124, d7431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d2124, d7431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2124, d7431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d2124, d7431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32985 (p : Pattern) (guard : d6558 p = 1) : d2125 p ≤ (2 : Int) + d7432 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2125, d7432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32984 p hg
    simpa only [d2125, d7432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2125, d7432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32944 p hg
    simpa only [d2125, d7432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32986 (p : Pattern) (guard : d6558 p = 1) : d3015 p ≤ (2 : Int) + d7433 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3015, d7433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d3015, d7433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3015, d7433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32985 p hg
    simpa only [d3015, d7433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32987 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32988 (p : Pattern) (guard : d5842 p = 1) : d1918 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32987 p hg
    simpa only [d5842, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d5842, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32989 (p : Pattern) (guard : d6558 p = 1) : d1919 p ≤ (2 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32988 p hg
    simpa only [d6558, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32892 p hg
    simpa only [d6558, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32990 (p : Pattern) (guard : d6558 p = 1) : d1920 p ≤ (2 : Int) + d7434 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1920, d7434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d1920, d7434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1920, d7434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32989 p hg
    simpa only [d1920, d7434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32991 (p : Pattern) (guard : d6558 p = 1) : d1921 p ≤ (2 : Int) + d7435 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1921, d7435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32990 p hg
    simpa only [d1921, d7435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1921, d7435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32989 p hg
    simpa only [d1921, d7435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32992 (p : Pattern) (guard : d6558 p = 1) : d1922 p ≤ (2 : Int) + d7436 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1922, d7436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32991 p hg
    simpa only [d1922, d7436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1922, d7436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1922, d7436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32993 (p : Pattern) (guard : d6558 p = 1) : d3016 p ≤ (2 : Int) + d7437 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3016, d7437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32986 p hg
    simpa only [d3016, d7437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3016, d7437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32992 p hg
    simpa only [d3016, d7437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32994 (p : Pattern) (guard : d6558 p = 1) : d3017 p ≤ (2 : Int) + d7438 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3017, d7438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32904 p hg
    simpa only [d3017, d7438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3017, d7438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32993 p hg
    simpa only [d3017, d7438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32995 (p : Pattern) (guard : d6558 p = 1) : d3018 p ≤ (2 : Int) + d7439 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3018, d7439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32920 p hg
    simpa only [d3018, d7439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3018, d7439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32806 p hg
    simpa only [d3018, d7439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32996 (p : Pattern) (guard : d6558 p = 1) : d3019 p ≤ (2 : Int) + d7440 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3019, d7440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32994 p hg
    simpa only [d3019, d7440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3019, d7440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32995 p hg
    simpa only [d3019, d7440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32997 (p : Pattern) (guard : d6558 p = 1) : d3020 p ≤ (2 : Int) + d7441 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3020, d7441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32920 p hg
    simpa only [d3020, d7441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3020, d7441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32809 p hg
    simpa only [d3020, d7441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32998 (p : Pattern) (guard : d6558 p = 1) : d3021 p ≤ (2 : Int) + d7442 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3021, d7442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32997 p hg
    simpa only [d3021, d7442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3021, d7442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3021, d7442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32999 (p : Pattern) (guard : d6558 p = 1) : d3022 p ≤ (2 : Int) + d7443 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3022, d7443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32996 p hg
    simpa only [d3022, d7443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3022, d7443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32998 p hg
    simpa only [d3022, d7443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33000 (p : Pattern) (guard : d6558 p = 1) : d3023 p ≤ (2 : Int) + d7444 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3023, d7444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32937 p hg
    simpa only [d3023, d7444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3023, d7444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32949 p hg
    simpa only [d3023, d7444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33001 (p : Pattern) (guard : d6558 p = 1) : d3024 p ≤ (2 : Int) + d7445 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3024, d7445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33000 p hg
    simpa only [d3024, d7445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3024, d7445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3024, d7445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33002 (p : Pattern) (guard : d6558 p = 1) : d3025 p ≤ (2 : Int) + d7446 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3025, d7446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32964 p hg
    simpa only [d3025, d7446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3025, d7446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33001 p hg
    simpa only [d3025, d7446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33003 (p : Pattern) (guard : d6558 p = 1) : d3026 p ≤ (2 : Int) + d7447 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3026, d7447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d3026, d7447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3026, d7447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32818 p hg
    simpa only [d3026, d7447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33004 (p : Pattern) (guard : d6558 p = 1) : d3027 p ≤ (2 : Int) + d7448 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3027, d7448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33002 p hg
    simpa only [d3027, d7448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3027, d7448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33003 p hg
    simpa only [d3027, d7448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33005 (p : Pattern) (guard : d6558 p = 1) : d3028 p ≤ (2 : Int) + d7449 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3028, d7449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32977 p hg
    simpa only [d3028, d7449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3028, d7449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32820 p hg
    simpa only [d3028, d7449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33006 (p : Pattern) (guard : d6558 p = 1) : d3029 p ≤ (2 : Int) + d7450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3029, d7450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33005 p hg
    simpa only [d3029, d7450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3029, d7450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d3029, d7450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33007 (p : Pattern) (guard : d6558 p = 1) : d3030 p ≤ (2 : Int) + d7451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3030, d7451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33004 p hg
    simpa only [d3030, d7451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3030, d7451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33006 p hg
    simpa only [d3030, d7451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33008 (p : Pattern) (guard : d6558 p = 1) : d3031 p ≤ (2 : Int) + d7452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3031, d7452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32999 p hg
    simpa only [d3031, d7452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3031, d7452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33007 p hg
    simpa only [d3031, d7452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33009 (p : Pattern) (guard : d6558 p = 1) : d3032 p ≤ (2 : Int) + d7453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3032, d7453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32983 p hg
    simpa only [d3032, d7453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3032, d7453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33008 p hg
    simpa only [d3032, d7453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33010 (p : Pattern) (guard : d6558 p = 1) : d2107 p ≤ (2 : Int) + d7398 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2107, d7398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d2107, d7398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2107, d7398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32928 p hg
    simpa only [d2107, d7398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33011 (p : Pattern) (guard : d6558 p = 1) : d2108 p ≤ (2 : Int) + d7454 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2108, d7454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d2108, d7454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2108, d7454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33010 p hg
    simpa only [d2108, d7454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33012 (p : Pattern) (guard : d6558 p = 1) : d3033 p ≤ (2 : Int) + d7455 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3033, d7455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d3033, d7455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3033, d7455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33011 p hg
    simpa only [d3033, d7455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33013 (p : Pattern) (guard : d6558 p = 1) : d1943 p ≤ (2 : Int) + d7456 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1943, d7456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32895 p hg
    simpa only [d1943, d7456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1943, d7456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1943, d7456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33014 (p : Pattern) (guard : d6558 p = 1) : d3034 p ≤ (2 : Int) + d7457 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3034, d7457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33012 p hg
    simpa only [d3034, d7457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3034, d7457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33013 p hg
    simpa only [d3034, d7457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33015 (p : Pattern) (guard : d5842 p = 1) : d3035 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32930 p hg
    simpa only [d5842, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d5842, d3035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33016 (p : Pattern) (guard : d6558 p = 1) : d3036 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33015 p hg
    simpa only [d6558, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d3036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33017 (p : Pattern) (guard : d6558 p = 1) : d3037 p ≤ (2 : Int) + d7408 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3037, d7408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d3037, d7408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3037, d7408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33016 p hg
    simpa only [d3037, d7408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33018 (p : Pattern) (guard : d6558 p = 1) : d3038 p ≤ (2 : Int) + d7409 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3038, d7409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d3038, d7409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3038, d7409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33017 p hg
    simpa only [d3038, d7409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33019 (p : Pattern) (guard : d6558 p = 1) : d3039 p ≤ (2 : Int) + d7410 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3039, d7410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32889 p hg
    simpa only [d3039, d7410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3039, d7410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33018 p hg
    simpa only [d3039, d7410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33020 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33021 (p : Pattern) (guard : d5842 p = 1) : d1948 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33020 p hg
    simpa only [d5842, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d5842, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33022 (p : Pattern) (guard : d6558 p = 1) : d1949 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33021 p hg
    simpa only [d6558, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33023 (p : Pattern) (guard : d6558 p = 1) : d1950 p ≤ (2 : Int) + d7395 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1950, d7395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32893 p hg
    simpa only [d1950, d7395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1950, d7395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33022 p hg
    simpa only [d1950, d7395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33024 (p : Pattern) (guard : d6558 p = 1) : d1951 p ≤ (2 : Int) + d7458 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1951, d7458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32929 p hg
    simpa only [d1951, d7458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1951, d7458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33023 p hg
    simpa only [d1951, d7458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33025 (p : Pattern) (guard : d6558 p = 1) : d1952 p ≤ (2 : Int) + d7459 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1952, d7459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33024 p hg
    simpa only [d1952, d7459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1952, d7459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1952, d7459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33026 (p : Pattern) (guard : d6558 p = 1) : d3040 p ≤ (2 : Int) + d7460 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3040, d7460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33019 p hg
    simpa only [d3040, d7460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3040, d7460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33025 p hg
    simpa only [d3040, d7460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33027 (p : Pattern) (guard : d6558 p = 1) : d3041 p ≤ (2 : Int) + d7461 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3041, d7461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33014 p hg
    simpa only [d3041, d7461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3041, d7461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33026 p hg
    simpa only [d3041, d7461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33028 (p : Pattern) (guard : d6558 p = 1) : d1958 p ≤ (2 : Int) + d7462 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1958, d7462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32934 p hg
    simpa only [d1958, d7462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1958, d7462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1958, d7462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33029 (p : Pattern) (guard : d6558 p = 1) : d3042 p ≤ (2 : Int) + d7463 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3042, d7463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32935 p hg
    simpa only [d3042, d7463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3042, d7463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33028 p hg
    simpa only [d3042, d7463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33030 (p : Pattern) (guard : d6558 p = 1) : d1967 p ≤ (2 : Int) + d7464 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1967, d7464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32975 p hg
    simpa only [d1967, d7464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1967, d7464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1967, d7464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33031 (p : Pattern) (guard : d6558 p = 1) : d3043 p ≤ (2 : Int) + d7465 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3043, d7465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32976 p hg
    simpa only [d3043, d7465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3043, d7465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33030 p hg
    simpa only [d3043, d7465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33032 (p : Pattern) (guard : d6558 p = 1) : d3044 p ≤ (2 : Int) + d7466 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3044, d7466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33029 p hg
    simpa only [d3044, d7466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3044, d7466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33031 p hg
    simpa only [d3044, d7466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33033 (p : Pattern) (guard : d6558 p = 1) : d3045 p ≤ (2 : Int) + d7467 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3045, d7467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33027 p hg
    simpa only [d3045, d7467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3045, d7467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33032 p hg
    simpa only [d3045, d7467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33034 (p : Pattern) (guard : d6558 p = 1) : d3046 p ≤ (2 : Int) + d7468 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3046, d7468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33032 p hg
    simpa only [d3046, d7468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3046, d7468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32923 p hg
    simpa only [d3046, d7468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33035 (p : Pattern) (guard : d6558 p = 1) : d3047 p ≤ (2 : Int) + d7469 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3047, d7469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33033 p hg
    simpa only [d3047, d7469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3047, d7469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33034 p hg
    simpa only [d3047, d7469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33036 (p : Pattern) (guard : d6558 p = 1) : d3048 p ≤ (2 : Int) + d7470 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3048, d7470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33000 p hg
    simpa only [d3048, d7470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3048, d7470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32950 p hg
    simpa only [d3048, d7470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33037 (p : Pattern) (guard : d6558 p = 1) : d3049 p ≤ (2 : Int) + d7471 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3049, d7471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32953 p hg
    simpa only [d3049, d7471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3049, d7471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32962 p hg
    simpa only [d3049, d7471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33038 (p : Pattern) (guard : d6558 p = 1) : d3050 p ≤ (2 : Int) + d7472 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3050, d7472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33037 p hg
    simpa only [d3050, d7472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3050, d7472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32963 p hg
    simpa only [d3050, d7472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33039 (p : Pattern) (guard : d6558 p = 1) : d3051 p ≤ (2 : Int) + d7473 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3051, d7473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33036 p hg
    simpa only [d3051, d7473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3051, d7473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33038 p hg
    simpa only [d3051, d7473, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
