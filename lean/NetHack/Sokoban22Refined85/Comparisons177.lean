/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24780 (p : Pattern) (guard : d4985 p = 1) : d3159 p ≤ (2 : Int) + d6000 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3159, d6000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24778 p hg
    simpa only [d3159, d6000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3159, d6000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24779 p hg
    simpa only [d3159, d6000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24781 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d2108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24782 (p : Pattern) (guard : d1 p = 1) : d1948 p ≤ (2 : Int) + d1945 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1948, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1948, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1948, d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d1948, d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24783 (p : Pattern) (guard : d1 p = 1) : d1949 p ≤ (2 : Int) + d1946 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1949, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24782 p hg
    simpa only [d1949, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1949, d1946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1949, d1946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24784 (p : Pattern) (guard : d1 p = 1) : d1950 p ≤ (2 : Int) + d2107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1950, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24568 p hg
    simpa only [d1950, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1950, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24783 p hg
    simpa only [d1950, d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24785 (p : Pattern) (guard : d1 p = 1) : d1951 p ≤ (2 : Int) + d2108 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1951, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24575 p hg
    simpa only [d1951, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1951, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24784 p hg
    simpa only [d1951, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24786 (p : Pattern) (guard : d4473 p = 1) : d3160 p ≤ (2 : Int) + d2108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24781 p hg
    simpa only [d4473, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24785 p hg
    simpa only [d4473, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24787 (p : Pattern) (guard : d0 p = 1) : d2109 p ≤ (2 : Int) + d2108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24788 (p : Pattern) (guard : d4985 p = 1) : d3161 p ≤ (2 : Int) + d2108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24786 p hg
    simpa only [d4985, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24787 p hg
    simpa only [d4985, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24789 (p : Pattern) (guard : d4985 p = 1) : d3162 p ≤ (2 : Int) + d6001 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3162, d6001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24788 p hg
    simpa only [d3162, d6001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3162, d6001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3162, d6001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24790 (p : Pattern) (guard : d4985 p = 1) : d3163 p ≤ (2 : Int) + d6002 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3163, d6002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24573 p hg
    simpa only [d3163, d6002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3163, d6002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24789 p hg
    simpa only [d3163, d6002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24791 (p : Pattern) (guard : d4985 p = 1) : d3164 p ≤ (2 : Int) + d6003 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3164, d6003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24582 p hg
    simpa only [d3164, d6003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3164, d6003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3164, d6003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24792 (p : Pattern) (guard : d4985 p = 1) : d3165 p ≤ (2 : Int) + d6004 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3165, d6004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24791 p hg
    simpa only [d3165, d6004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3165, d6004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24499 p hg
    simpa only [d3165, d6004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24793 (p : Pattern) (guard : d4985 p = 1) : d3166 p ≤ (2 : Int) + d6005 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3166, d6005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24790 p hg
    simpa only [d3166, d6005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3166, d6005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24792 p hg
    simpa only [d3166, d6005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24794 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24795 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d7 p := by
  change (3 : Int) ≤ (2 : Int) + 7
  decide
theorem compare24796 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24797 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24796 p hg
    simpa only [d116, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24798 (p : Pattern) (guard : d1 p = 1) : d1891 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1891, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d1891, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1891, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d1891, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24799 (p : Pattern) (guard : d1 p = 1) : d1892 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1892, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24798 p hg
    simpa only [d1892, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1892, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1892, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24800 (p : Pattern) (guard : d1 p = 1) : d1893 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1893, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24797 p hg
    simpa only [d1893, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1893, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24799 p hg
    simpa only [d1893, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24801 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24795 p hg
    simpa only [d1894, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d1894, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24802 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24801 p hg
    simpa only [d1895, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16300 p hg
    simpa only [d1895, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24803 (p : Pattern) (guard : d1 p = 1) : d1896 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1896, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24796 p hg
    simpa only [d1896, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1896, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d1896, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24804 (p : Pattern) (guard : d1 p = 1) : d1897 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1897, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24802 p hg
    simpa only [d1897, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1897, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24803 p hg
    simpa only [d1897, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24805 (p : Pattern) (guard : d1 p = 1) : d1898 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1898, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24800 p hg
    simpa only [d1898, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1898, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24804 p hg
    simpa only [d1898, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24806 (p : Pattern) (guard : d4473 p = 1) : d3023 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24794 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24805 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24807 (p : Pattern) (guard : d4985 p = 1) : d3167 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24806 p hg
    simpa only [d4985, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24524 p hg
    simpa only [d4985, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24808 (p : Pattern) (guard : d4985 p = 1) : d3168 p ≤ (2 : Int) + d5911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3168, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3168, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3168, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24807 p hg
    simpa only [d3168, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24809 (p : Pattern) (guard : d4985 p = 1) : d3169 p ≤ (2 : Int) + d5912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3169, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24808 p hg
    simpa only [d3169, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3169, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24766 p hg
    simpa only [d3169, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24810 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24811 (p : Pattern) (guard : d4473 p = 1) : d3049 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24810 p hg
    simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16284 p hg
    simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24812 (p : Pattern) (guard : d4985 p = 1) : d3170 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24811 p hg
    simpa only [d4985, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24813 (p : Pattern) (guard : d4985 p = 1) : d3171 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24812 p hg
    simpa only [d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24814 (p : Pattern) (guard : d4985 p = 1) : d3172 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24813 p hg
    simpa only [d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24815 (p : Pattern) (guard : d4985 p = 1) : d3173 p ≤ (2 : Int) + d5913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3173, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24809 p hg
    simpa only [d3173, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3173, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24814 p hg
    simpa only [d3173, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24816 (p : Pattern) (guard : d4985 p = 1) : d3174 p ≤ (2 : Int) + d6006 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3174, d6006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24793 p hg
    simpa only [d3174, d6006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3174, d6006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24815 p hg
    simpa only [d3174, d6006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24817 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d2125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24818 (p : Pattern) (guard : d1 p = 1) : d1891 p ≤ (2 : Int) + d1894 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1891, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d1891, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1891, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d1891, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24819 (p : Pattern) (guard : d1 p = 1) : d1892 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1892, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24818 p hg
    simpa only [d1892, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1892, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1892, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24820 (p : Pattern) (guard : d1 p = 1) : d1893 p ≤ (2 : Int) + d2124 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1893, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d1893, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1893, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24819 p hg
    simpa only [d1893, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24821 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d1895 p := by
  omega
theorem compare24822 (p : Pattern) (guard : d1 p = 1) : d3175 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24821 p hg
    simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24819 p hg
    simpa only [d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24823 (p : Pattern) (guard : d1 p = 1) : d3176 p ≤ (2 : Int) + d2125 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3176, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24820 p hg
    simpa only [d3176, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3176, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24822 p hg
    simpa only [d3176, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24824 (p : Pattern) (guard : d4473 p = 1) : d3177 p ≤ (2 : Int) + d2125 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24817 p hg
    simpa only [d4473, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24823 p hg
    simpa only [d4473, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24825 (p : Pattern) (guard : d0 p = 1) : d2126 p ≤ (2 : Int) + d2125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24826 (p : Pattern) (guard : d4985 p = 1) : d3178 p ≤ (2 : Int) + d2125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24824 p hg
    simpa only [d4985, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24825 p hg
    simpa only [d4985, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24827 (p : Pattern) (guard : d4985 p = 1) : d3179 p ≤ (2 : Int) + d6007 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3179, d6007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24788 p hg
    simpa only [d3179, d6007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3179, d6007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24826 p hg
    simpa only [d3179, d6007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24828 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d2130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24829 (p : Pattern) (guard : d1 p = 1) : d1960 p ≤ (2 : Int) + d1963 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1960, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1960, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1960, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d1960, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24830 (p : Pattern) (guard : d1 p = 1) : d1961 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1961, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24829 p hg
    simpa only [d1961, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1961, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d1961, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24831 (p : Pattern) (guard : d1 p = 1) : d1962 p ≤ (2 : Int) + d2129 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1962, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d1962, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1962, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24830 p hg
    simpa only [d1962, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24832 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d1964 p := by
  omega
theorem compare24833 (p : Pattern) (guard : d1 p = 1) : d2135 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24832 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24830 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24834 (p : Pattern) (guard : d1 p = 1) : d2136 p ≤ (2 : Int) + d2130 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2136, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24831 p hg
    simpa only [d2136, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2136, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24833 p hg
    simpa only [d2136, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24835 (p : Pattern) (guard : d4473 p = 1) : d3180 p ≤ (2 : Int) + d2130 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24828 p hg
    simpa only [d4473, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24834 p hg
    simpa only [d4473, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24836 (p : Pattern) (guard : d0 p = 1) : d2131 p ≤ (2 : Int) + d2130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24837 (p : Pattern) (guard : d4985 p = 1) : d3181 p ≤ (2 : Int) + d2130 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24835 p hg
    simpa only [d4985, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24836 p hg
    simpa only [d4985, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24838 (p : Pattern) (guard : d4985 p = 1) : d3182 p ≤ (2 : Int) + d6008 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3182, d6008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24837 p hg
    simpa only [d3182, d6008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3182, d6008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3182, d6008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24839 (p : Pattern) (guard : d4985 p = 1) : d3183 p ≤ (2 : Int) + d6009 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3183, d6009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24827 p hg
    simpa only [d3183, d6009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3183, d6009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24838 p hg
    simpa only [d3183, d6009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24840 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d2136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24841 (p : Pattern) (guard : d1 p = 1) : d1962 p ≤ (2 : Int) + d1962 p := by
  omega
theorem compare24842 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d1960 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d106, d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24843 (p : Pattern) (guard : d1 p = 1) : d348 p ≤ (2 : Int) + d1961 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24842 p hg
    simpa only [d348, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d348, d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24844 (p : Pattern) (guard : d1 p = 1) : d1965 p ≤ (2 : Int) + d2135 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1965, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24832 p hg
    simpa only [d1965, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1965, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24843 p hg
    simpa only [d1965, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24845 (p : Pattern) (guard : d1 p = 1) : d1966 p ≤ (2 : Int) + d2136 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1966, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24841 p hg
    simpa only [d1966, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1966, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24844 p hg
    simpa only [d1966, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24846 (p : Pattern) (guard : d4473 p = 1) : d3007 p ≤ (2 : Int) + d2136 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24840 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24845 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24847 (p : Pattern) (guard : d0 p = 1) : d2137 p ≤ (2 : Int) + d2136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24848 (p : Pattern) (guard : d4985 p = 1) : d3184 p ≤ (2 : Int) + d2136 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24846 p hg
    simpa only [d4985, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24847 p hg
    simpa only [d4985, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24849 (p : Pattern) (guard : d4985 p = 1) : d3185 p ≤ (2 : Int) + d6010 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3185, d6010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24848 p hg
    simpa only [d3185, d6010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3185, d6010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3185, d6010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24850 (p : Pattern) (guard : d4985 p = 1) : d3186 p ≤ (2 : Int) + d6011 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3186, d6011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24849 p hg
    simpa only [d3186, d6011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3186, d6011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3186, d6011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24851 (p : Pattern) (guard : d4985 p = 1) : d3187 p ≤ (2 : Int) + d6012 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3187, d6012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24839 p hg
    simpa only [d3187, d6012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3187, d6012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24850 p hg
    simpa only [d3187, d6012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24852 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24853 (p : Pattern) (guard : d1 p = 1) : d1960 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1960, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d1960, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1960, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1960, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24854 (p : Pattern) (guard : d1 p = 1) : d1961 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1961, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24853 p hg
    simpa only [d1961, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1961, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1961, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24855 (p : Pattern) (guard : d1 p = 1) : d1962 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1962, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16225 p hg
    simpa only [d1962, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1962, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24854 p hg
    simpa only [d1962, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24856 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d1963, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d1963, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24857 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24856 p hg
    simpa only [d1964, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15786 p hg
    simpa only [d1964, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24858 (p : Pattern) (guard : d1 p = 1) : d348 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d348, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d348, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24859 (p : Pattern) (guard : d1 p = 1) : d1965 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1965, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24857 p hg
    simpa only [d1965, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1965, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24858 p hg
    simpa only [d1965, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24860 (p : Pattern) (guard : d1 p = 1) : d1966 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1966, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24855 p hg
    simpa only [d1966, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1966, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24859 p hg
    simpa only [d1966, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24861 (p : Pattern) (guard : d4473 p = 1) : d3007 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24852 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24860 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24862 (p : Pattern) (guard : d4985 p = 1) : d3188 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24861 p hg
    simpa only [d4985, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24524 p hg
    simpa only [d4985, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24863 (p : Pattern) (guard : d4985 p = 1) : d3189 p ≤ (2 : Int) + d5921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3189, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24862 p hg
    simpa only [d3189, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3189, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d3189, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24864 (p : Pattern) (guard : d4985 p = 1) : d3190 p ≤ (2 : Int) + d5922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3190, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24863 p hg
    simpa only [d3190, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3190, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24813 p hg
    simpa only [d3190, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24865 (p : Pattern) (guard : d4985 p = 1) : d3191 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24358 p hg
    simpa only [d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24866 (p : Pattern) (guard : d4985 p = 1) : d3192 p ≤ (2 : Int) + d5923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3192, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24864 p hg
    simpa only [d3192, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3192, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24865 p hg
    simpa only [d3192, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24867 (p : Pattern) (guard : d4985 p = 1) : d3193 p ≤ (2 : Int) + d6013 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3193, d6013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24851 p hg
    simpa only [d3193, d6013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3193, d6013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24866 p hg
    simpa only [d3193, d6013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24868 (p : Pattern) (guard : d4985 p = 1) : d3194 p ≤ (2 : Int) + d6014 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3194, d6014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24816 p hg
    simpa only [d3194, d6014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3194, d6014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24867 p hg
    simpa only [d3194, d6014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24869 (p : Pattern) (guard : d4985 p = 1) : d3195 p ≤ (2 : Int) + d6015 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3195, d6015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24582 p hg
    simpa only [d3195, d6015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3195, d6015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24588 p hg
    simpa only [d3195, d6015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24870 (p : Pattern) (guard : d4985 p = 1) : d3196 p ≤ (2 : Int) + d6016 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3196, d6016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3196, d6016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3196, d6016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d3196, d6016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24871 (p : Pattern) (guard : d4985 p = 1) : d3197 p ≤ (2 : Int) + d6017 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3197, d6017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24869 p hg
    simpa only [d3197, d6017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3197, d6017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24870 p hg
    simpa only [d3197, d6017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24872 (p : Pattern) (guard : d4985 p = 1) : d3198 p ≤ (2 : Int) + d6018 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3198, d6018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24871 p hg
    simpa only [d3198, d6018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3198, d6018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24614 p hg
    simpa only [d3198, d6018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24873 (p : Pattern) (guard : d4985 p = 1) : d3199 p ≤ (2 : Int) + d6019 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3199, d6019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24872 p hg
    simpa only [d3199, d6019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3199, d6019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24618 p hg
    simpa only [d3199, d6019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24874 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d2157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24875 (p : Pattern) (guard : d1 p = 1) : d1893 p ≤ (2 : Int) + d1893 p := by
  omega
theorem compare24876 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d2154 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24877 (p : Pattern) (guard : d1 p = 1) : d1896 p ≤ (2 : Int) + d2155 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1896, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24876 p hg
    simpa only [d1896, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1896, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d1896, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24878 (p : Pattern) (guard : d1 p = 1) : d1897 p ≤ (2 : Int) + d2156 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1897, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24821 p hg
    simpa only [d1897, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1897, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24877 p hg
    simpa only [d1897, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24879 (p : Pattern) (guard : d1 p = 1) : d1898 p ≤ (2 : Int) + d2157 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1898, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24875 p hg
    simpa only [d1898, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1898, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24878 p hg
    simpa only [d1898, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24880 (p : Pattern) (guard : d4473 p = 1) : d3023 p ≤ (2 : Int) + d2157 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24874 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24879 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24881 (p : Pattern) (guard : d0 p = 1) : d2158 p ≤ (2 : Int) + d2157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24882 (p : Pattern) (guard : d4985 p = 1) : d3200 p ≤ (2 : Int) + d2157 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24880 p hg
    simpa only [d4985, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24881 p hg
    simpa only [d4985, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24883 (p : Pattern) (guard : d4985 p = 1) : d3201 p ≤ (2 : Int) + d6020 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3201, d6020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24882 p hg
    simpa only [d3201, d6020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3201, d6020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3201, d6020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24884 (p : Pattern) (guard : d4985 p = 1) : d3202 p ≤ (2 : Int) + d6021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3202, d6021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24883 p hg
    simpa only [d3202, d6021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3202, d6021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24772 p hg
    simpa only [d3202, d6021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24885 (p : Pattern) (guard : d4985 p = 1) : d3203 p ≤ (2 : Int) + d6022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3203, d6022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24884 p hg
    simpa only [d3203, d6022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3203, d6022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24617 p hg
    simpa only [d3203, d6022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24886 (p : Pattern) (guard : d4985 p = 1) : d3204 p ≤ (2 : Int) + d6023 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3204, d6023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24441 p hg
    simpa only [d3204, d6023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3204, d6023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3204, d6023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24887 (p : Pattern) (guard : d4985 p = 1) : d3205 p ≤ (2 : Int) + d6024 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3205, d6024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24886 p hg
    simpa only [d3205, d6024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3205, d6024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3205, d6024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24888 (p : Pattern) (guard : d4985 p = 1) : d3206 p ≤ (2 : Int) + d6025 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3206, d6025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24885 p hg
    simpa only [d3206, d6025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3206, d6025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24887 p hg
    simpa only [d3206, d6025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24889 (p : Pattern) (guard : d4985 p = 1) : d3207 p ≤ (2 : Int) + d6026 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3207, d6026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24873 p hg
    simpa only [d3207, d6026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3207, d6026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24888 p hg
    simpa only [d3207, d6026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24890 (p : Pattern) (guard : d4985 p = 1) : d3208 p ≤ (2 : Int) + d6027 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3208, d6027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24868 p hg
    simpa only [d3208, d6027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3208, d6027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24889 p hg
    simpa only [d3208, d6027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24891 (p : Pattern) (guard : d4985 p = 1) : d3209 p ≤ (2 : Int) + d6028 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3209, d6028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3209, d6028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3209, d6028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d3209, d6028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24892 (p : Pattern) (guard : d4985 p = 1) : d3210 p ≤ (2 : Int) + d6029 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3210, d6029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24869 p hg
    simpa only [d3210, d6029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3210, d6029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24891 p hg
    simpa only [d3210, d6029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24893 (p : Pattern) (guard : d4985 p = 1) : d3211 p ≤ (2 : Int) + d6030 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3211, d6030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3211, d6030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3211, d6030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d3211, d6030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24894 (p : Pattern) (guard : d4985 p = 1) : d3212 p ≤ (2 : Int) + d6031 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3212, d6031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24893 p hg
    simpa only [d3212, d6031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3212, d6031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3212, d6031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24895 (p : Pattern) (guard : d4985 p = 1) : d3213 p ≤ (2 : Int) + d6032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3213, d6032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24892 p hg
    simpa only [d3213, d6032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3213, d6032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24894 p hg
    simpa only [d3213, d6032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24896 (p : Pattern) (guard : d4985 p = 1) : d3214 p ≤ (2 : Int) + d6033 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3214, d6033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24605 p hg
    simpa only [d3214, d6033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3214, d6033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d3214, d6033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24897 (p : Pattern) (guard : d4985 p = 1) : d3215 p ≤ (2 : Int) + d6034 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3215, d6034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24896 p hg
    simpa only [d3215, d6034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3215, d6034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3215, d6034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24898 (p : Pattern) (guard : d4985 p = 1) : d3216 p ≤ (2 : Int) + d6035 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3216, d6035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24897 p hg
    simpa only [d3216, d6035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3216, d6035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3216, d6035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24899 (p : Pattern) (guard : d4985 p = 1) : d3217 p ≤ (2 : Int) + d6036 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3217, d6036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24895 p hg
    simpa only [d3217, d6036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3217, d6036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24898 p hg
    simpa only [d3217, d6036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24900 (p : Pattern) (guard : d4985 p = 1) : d3218 p ≤ (2 : Int) + d6037 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3218, d6037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24899 p hg
    simpa only [d3218, d6037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3218, d6037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24888 p hg
    simpa only [d3218, d6037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24901 (p : Pattern) (guard : d4985 p = 1) : d3219 p ≤ (2 : Int) + d6038 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3219, d6038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24900 p hg
    simpa only [d3219, d6038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3219, d6038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3219, d6038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24902 (p : Pattern) (guard : d4985 p = 1) : d3220 p ≤ (2 : Int) + d6039 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3220, d6039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24890 p hg
    simpa only [d3220, d6039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3220, d6039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24901 p hg
    simpa only [d3220, d6039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24903 (p : Pattern) (guard : d4985 p = 1) : d3221 p ≤ (2 : Int) + d6040 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3221, d6040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24780 p hg
    simpa only [d3221, d6040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3221, d6040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24902 p hg
    simpa only [d3221, d6040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24904 (p : Pattern) (guard : d4985 p = 1) : d3222 p ≤ (2 : Int) + d6041 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3222, d6041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24480 p hg
    simpa only [d3222, d6041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3222, d6041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24903 p hg
    simpa only [d3222, d6041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24905 (p : Pattern) (guard : d4985 p = 1) : d3223 p ≤ (2 : Int) + d6042 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3223, d6042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24761 p hg
    simpa only [d3223, d6042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3223, d6042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24904 p hg
    simpa only [d3223, d6042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24906 (p : Pattern) (guard : d4985 p = 1) : d3224 p ≤ (2 : Int) + d6043 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3224, d6043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24632 p hg
    simpa only [d3224, d6043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3224, d6043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24905 p hg
    simpa only [d3224, d6043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24907 (p : Pattern) (guard : d1 p = 1) : d3224 p ≤ (0 : Int) + d3224 p := by
  omega
theorem compare24908 (p : Pattern) (guard : d5502 p = 1) : d2895 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17081 p hg
    simpa only [d2895, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d2895, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24909 (p : Pattern) (guard : d5502 p = 1) : d1687 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17088 p hg
    simpa only [d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1687, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24910 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24908 p hg
    simpa only [d2896, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d2896, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24911 (p : Pattern) (guard : d5502 p = 1) : d2895 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17091 p hg
    simpa only [d2895, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d2895, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24912 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24911 p hg
    simpa only [d2896, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d2896, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24913 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24910 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24912 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24914 (p : Pattern) (guard : d5502 p = 1) : d2895 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2895, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2895, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17204 p hg
    simpa only [d2895, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24915 (p : Pattern) (guard : d5502 p = 1) : d2896 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24914 p hg
    simpa only [d2896, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2896, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24909 p hg
    simpa only [d2896, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24916 (p : Pattern) (guard : d5502 p = 1) : d2897 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2897, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14853 p hg
    simpa only [d2897, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2897, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17461 p hg
    simpa only [d2897, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24917 (p : Pattern) (guard : d5502 p = 1) : d1697 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17105 p hg
    simpa only [d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d1697, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24918 (p : Pattern) (guard : d5502 p = 1) : d2898 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2898, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24916 p hg
    simpa only [d2898, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2898, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24917 p hg
    simpa only [d2898, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24919 (p : Pattern) (guard : d5502 p = 1) : d2899 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2899, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24915 p hg
    simpa only [d2899, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2899, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24918 p hg
    simpa only [d2899, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
