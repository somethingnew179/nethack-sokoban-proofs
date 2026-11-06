/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24500 (p : Pattern) (guard : d4985 p = 1) : d3000 p ≤ (2 : Int) + d5909 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3000, d5909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24497 p hg
    simpa only [d3000, d5909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3000, d5909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24499 p hg
    simpa only [d3000, d5909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24501 (p : Pattern) (guard : d4985 p = 1) : d3001 p ≤ (2 : Int) + d5910 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3001, d5910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24498 p hg
    simpa only [d3001, d5910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3001, d5910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24500 p hg
    simpa only [d3001, d5910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24502 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24503 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d1891 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d1945, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16266 p hg
    simpa only [d1945, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24504 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d1892 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24503 p hg
    simpa only [d1946, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16268 p hg
    simpa only [d1946, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24505 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d1893 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d1947, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24504 p hg
    simpa only [d1947, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24506 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d1894 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d1939, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d1939, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24507 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24506 p hg
    simpa only [d1940, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d1940, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24508 (p : Pattern) (guard : d1 p = 1) : d1955 p ≤ (2 : Int) + d1896 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1955, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14091 p hg
    simpa only [d1955, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1955, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1955, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24509 (p : Pattern) (guard : d1 p = 1) : d1956 p ≤ (2 : Int) + d1897 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1956, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24507 p hg
    simpa only [d1956, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1956, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24508 p hg
    simpa only [d1956, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24510 (p : Pattern) (guard : d1 p = 1) : d1957 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1957, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24505 p hg
    simpa only [d1957, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1957, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24509 p hg
    simpa only [d1957, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24511 (p : Pattern) (guard : d4473 p = 1) : d3002 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24502 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24510 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24512 (p : Pattern) (guard : d0 p = 1) : d1899 p ≤ (2 : Int) + d1898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24513 (p : Pattern) (guard : d4985 p = 1) : d3003 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24511 p hg
    simpa only [d4985, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24512 p hg
    simpa only [d4985, d3003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24514 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24515 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1945, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d1945, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24516 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24515 p hg
    simpa only [d1946, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d1946, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24517 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d1901 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15978 p hg
    simpa only [d1947, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24516 p hg
    simpa only [d1947, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24518 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15976 p hg
    simpa only [d1939, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d1939, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24519 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24518 p hg
    simpa only [d1940, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16305 p hg
    simpa only [d1940, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24520 (p : Pattern) (guard : d1 p = 1) : d1955 p ≤ (2 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1955, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15977 p hg
    simpa only [d1955, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1955, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1955, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24521 (p : Pattern) (guard : d1 p = 1) : d1956 p ≤ (2 : Int) + d1904 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1956, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24519 p hg
    simpa only [d1956, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1956, d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24520 p hg
    simpa only [d1956, d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24522 (p : Pattern) (guard : d1 p = 1) : d1957 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1957, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24517 p hg
    simpa only [d1957, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1957, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24521 p hg
    simpa only [d1957, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24523 (p : Pattern) (guard : d4473 p = 1) : d3002 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24514 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24522 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24524 (p : Pattern) (guard : d0 p = 1) : d1906 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24525 (p : Pattern) (guard : d4985 p = 1) : d3004 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24523 p hg
    simpa only [d4985, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24524 p hg
    simpa only [d4985, d3004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24526 (p : Pattern) (guard : d4985 p = 1) : d3005 p ≤ (2 : Int) + d5911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3005, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24513 p hg
    simpa only [d3005, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3005, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24525 p hg
    simpa only [d3005, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24527 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24528 (p : Pattern) (guard : d4473 p = 1) : d3002 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24527 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16007 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24529 (p : Pattern) (guard : d4985 p = 1) : d3006 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24528 p hg
    simpa only [d4985, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d3006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24530 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24531 (p : Pattern) (guard : d4473 p = 1) : d3007 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24530 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16018 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24532 (p : Pattern) (guard : d4985 p = 1) : d3008 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24531 p hg
    simpa only [d4985, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d3008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24533 (p : Pattern) (guard : d4985 p = 1) : d3009 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24529 p hg
    simpa only [d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d3009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24534 (p : Pattern) (guard : d4985 p = 1) : d3010 p ≤ (2 : Int) + d5912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3010, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24526 p hg
    simpa only [d3010, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3010, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24533 p hg
    simpa only [d3010, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24535 (p : Pattern) (guard : d4985 p = 1) : d3011 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24394 p hg
    simpa only [d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24536 (p : Pattern) (guard : d4985 p = 1) : d3012 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24533 p hg
    simpa only [d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24535 p hg
    simpa only [d3012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24537 (p : Pattern) (guard : d4985 p = 1) : d3013 p ≤ (2 : Int) + d5913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3013, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24534 p hg
    simpa only [d3013, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3013, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24536 p hg
    simpa only [d3013, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24538 (p : Pattern) (guard : d4985 p = 1) : d3014 p ≤ (2 : Int) + d5914 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3014, d5914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24501 p hg
    simpa only [d3014, d5914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3014, d5914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24537 p hg
    simpa only [d3014, d5914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24539 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d1921 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24540 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (2 : Int) + d1918 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15951 p hg
    simpa only [d1894, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d1894, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24541 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d1919 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24540 p hg
    simpa only [d1895, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1895, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24542 (p : Pattern) (guard : d1 p = 1) : d2124 p ≤ (2 : Int) + d1920 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2124, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d2124, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2124, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24541 p hg
    simpa only [d2124, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24543 (p : Pattern) (guard : d1 p = 1) : d2125 p ≤ (2 : Int) + d1921 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2125, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24542 p hg
    simpa only [d2125, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2125, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24541 p hg
    simpa only [d2125, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24544 (p : Pattern) (guard : d4473 p = 1) : d3015 p ≤ (2 : Int) + d1921 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24539 p hg
    simpa only [d4473, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24543 p hg
    simpa only [d4473, d3015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24545 (p : Pattern) (guard : d0 p = 1) : d1922 p ≤ (2 : Int) + d1921 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24546 (p : Pattern) (guard : d4985 p = 1) : d3016 p ≤ (2 : Int) + d1921 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24544 p hg
    simpa only [d4985, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24545 p hg
    simpa only [d4985, d3016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24547 (p : Pattern) (guard : d4985 p = 1) : d3017 p ≤ (2 : Int) + d5915 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3017, d5915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24488 p hg
    simpa only [d3017, d5915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3017, d5915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24546 p hg
    simpa only [d3017, d5915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24548 (p : Pattern) (guard : d4985 p = 1) : d3018 p ≤ (2 : Int) + d5916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3018, d5916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24496 p hg
    simpa only [d3018, d5916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3018, d5916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d3018, d5916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24549 (p : Pattern) (guard : d4985 p = 1) : d3019 p ≤ (2 : Int) + d5917 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3019, d5917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24547 p hg
    simpa only [d3019, d5917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3019, d5917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24548 p hg
    simpa only [d3019, d5917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24550 (p : Pattern) (guard : d4985 p = 1) : d3020 p ≤ (2 : Int) + d5918 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3020, d5918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24496 p hg
    simpa only [d3020, d5918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3020, d5918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d3020, d5918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24551 (p : Pattern) (guard : d4985 p = 1) : d3021 p ≤ (2 : Int) + d5919 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3021, d5919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24550 p hg
    simpa only [d3021, d5919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3021, d5919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3021, d5919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24552 (p : Pattern) (guard : d4985 p = 1) : d3022 p ≤ (2 : Int) + d5920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3022, d5920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24549 p hg
    simpa only [d3022, d5920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3022, d5920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24551 p hg
    simpa only [d3022, d5920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24553 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24554 (p : Pattern) (guard : d4473 p = 1) : d3023 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24553 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16036 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24555 (p : Pattern) (guard : d4985 p = 1) : d3024 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24554 p hg
    simpa only [d4985, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d3024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24556 (p : Pattern) (guard : d4985 p = 1) : d3025 p ≤ (2 : Int) + d5921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3025, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24525 p hg
    simpa only [d3025, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3025, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24555 p hg
    simpa only [d3025, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24557 (p : Pattern) (guard : d4985 p = 1) : d3026 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24394 p hg
    simpa only [d3026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24558 (p : Pattern) (guard : d4985 p = 1) : d3027 p ≤ (2 : Int) + d5922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3027, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24556 p hg
    simpa only [d3027, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3027, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24557 p hg
    simpa only [d3027, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24559 (p : Pattern) (guard : d4985 p = 1) : d3028 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24398 p hg
    simpa only [d3028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24560 (p : Pattern) (guard : d4985 p = 1) : d3029 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24559 p hg
    simpa only [d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24561 (p : Pattern) (guard : d4985 p = 1) : d3030 p ≤ (2 : Int) + d5923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3030, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24558 p hg
    simpa only [d3030, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3030, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24560 p hg
    simpa only [d3030, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24562 (p : Pattern) (guard : d4985 p = 1) : d3031 p ≤ (2 : Int) + d5924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3031, d5924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24552 p hg
    simpa only [d3031, d5924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3031, d5924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24561 p hg
    simpa only [d3031, d5924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24563 (p : Pattern) (guard : d4985 p = 1) : d3032 p ≤ (2 : Int) + d5925 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3032, d5925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24538 p hg
    simpa only [d3032, d5925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3032, d5925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24562 p hg
    simpa only [d3032, d5925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24564 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24565 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d1939 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d1945, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d1945, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24566 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24565 p hg
    simpa only [d1946, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1946, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24567 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d1941 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1947, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24566 p hg
    simpa only [d1947, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24568 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d1940 p := by
  omega
theorem compare24569 (p : Pattern) (guard : d1 p = 1) : d2107 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24568 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24566 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24570 (p : Pattern) (guard : d1 p = 1) : d2108 p ≤ (2 : Int) + d1942 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2108, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24567 p hg
    simpa only [d2108, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2108, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24569 p hg
    simpa only [d2108, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24571 (p : Pattern) (guard : d4473 p = 1) : d3033 p ≤ (2 : Int) + d1942 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24564 p hg
    simpa only [d4473, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24570 p hg
    simpa only [d4473, d3033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24572 (p : Pattern) (guard : d0 p = 1) : d1943 p ≤ (2 : Int) + d1942 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24573 (p : Pattern) (guard : d4985 p = 1) : d3034 p ≤ (2 : Int) + d1942 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24571 p hg
    simpa only [d4985, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24572 p hg
    simpa only [d4985, d3034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24574 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24575 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d1947 p := by
  omega
theorem compare24576 (p : Pattern) (guard : d1 p = 1) : d3035 p ≤ (2 : Int) + d1948 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3035, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15921 p hg
    simpa only [d3035, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3035, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d3035, d1948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24577 (p : Pattern) (guard : d1 p = 1) : d3036 p ≤ (2 : Int) + d1949 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3036, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24576 p hg
    simpa only [d3036, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3036, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d3036, d1949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24578 (p : Pattern) (guard : d1 p = 1) : d3037 p ≤ (2 : Int) + d1950 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3037, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24568 p hg
    simpa only [d3037, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3037, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24577 p hg
    simpa only [d3037, d1950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24579 (p : Pattern) (guard : d1 p = 1) : d3038 p ≤ (2 : Int) + d1951 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3038, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24575 p hg
    simpa only [d3038, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3038, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24578 p hg
    simpa only [d3038, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24580 (p : Pattern) (guard : d4473 p = 1) : d3039 p ≤ (2 : Int) + d1951 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24574 p hg
    simpa only [d4473, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24579 p hg
    simpa only [d4473, d3039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24581 (p : Pattern) (guard : d0 p = 1) : d1952 p ≤ (2 : Int) + d1951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24582 (p : Pattern) (guard : d4985 p = 1) : d3040 p ≤ (2 : Int) + d1951 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24580 p hg
    simpa only [d4985, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24581 p hg
    simpa only [d4985, d3040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24583 (p : Pattern) (guard : d4985 p = 1) : d3041 p ≤ (2 : Int) + d5926 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3041, d5926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24573 p hg
    simpa only [d3041, d5926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3041, d5926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24582 p hg
    simpa only [d3041, d5926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24584 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1957 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24585 (p : Pattern) (guard : d1 p = 1) : d1957 p ≤ (2 : Int) + d1957 p := by
  omega
theorem compare24586 (p : Pattern) (guard : d4473 p = 1) : d3002 p ≤ (2 : Int) + d1957 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24584 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24585 p hg
    simpa only [d4473, d3002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24587 (p : Pattern) (guard : d0 p = 1) : d1958 p ≤ (2 : Int) + d1957 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24588 (p : Pattern) (guard : d4985 p = 1) : d3042 p ≤ (2 : Int) + d1957 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24586 p hg
    simpa only [d4985, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24587 p hg
    simpa only [d4985, d3042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24589 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d1966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24590 (p : Pattern) (guard : d1 p = 1) : d1966 p ≤ (2 : Int) + d1966 p := by
  omega
theorem compare24591 (p : Pattern) (guard : d4473 p = 1) : d3007 p ≤ (2 : Int) + d1966 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24589 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24590 p hg
    simpa only [d4473, d3007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24592 (p : Pattern) (guard : d0 p = 1) : d1967 p ≤ (2 : Int) + d1966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24593 (p : Pattern) (guard : d4985 p = 1) : d3043 p ≤ (2 : Int) + d1966 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24591 p hg
    simpa only [d4985, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24592 p hg
    simpa only [d4985, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24594 (p : Pattern) (guard : d4985 p = 1) : d3044 p ≤ (2 : Int) + d5927 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3044, d5927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24588 p hg
    simpa only [d3044, d5927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3044, d5927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3044, d5927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24595 (p : Pattern) (guard : d4985 p = 1) : d3045 p ≤ (2 : Int) + d5928 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3045, d5928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24583 p hg
    simpa only [d3045, d5928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3045, d5928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24594 p hg
    simpa only [d3045, d5928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24596 (p : Pattern) (guard : d4985 p = 1) : d3046 p ≤ (2 : Int) + d5929 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3046, d5929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24594 p hg
    simpa only [d3046, d5929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3046, d5929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24499 p hg
    simpa only [d3046, d5929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24597 (p : Pattern) (guard : d4985 p = 1) : d3047 p ≤ (2 : Int) + d5930 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3047, d5930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24595 p hg
    simpa only [d3047, d5930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3047, d5930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24596 p hg
    simpa only [d3047, d5930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24598 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d1898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24599 (p : Pattern) (guard : d1 p = 1) : d1898 p ≤ (2 : Int) + d1898 p := by
  omega
theorem compare24600 (p : Pattern) (guard : d4473 p = 1) : d3023 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24598 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24599 p hg
    simpa only [d4473, d3023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24601 (p : Pattern) (guard : d4985 p = 1) : d3048 p ≤ (2 : Int) + d1898 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24600 p hg
    simpa only [d4985, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24512 p hg
    simpa only [d4985, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24602 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (2 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24603 (p : Pattern) (guard : d1 p = 1) : d1905 p ≤ (2 : Int) + d1905 p := by
  omega
theorem compare24604 (p : Pattern) (guard : d4473 p = 1) : d3049 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24602 p hg
    simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24603 p hg
    simpa only [d4473, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24605 (p : Pattern) (guard : d4985 p = 1) : d3050 p ≤ (2 : Int) + d1905 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24604 p hg
    simpa only [d4985, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24524 p hg
    simpa only [d4985, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24606 (p : Pattern) (guard : d4985 p = 1) : d3051 p ≤ (2 : Int) + d5911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3051, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3051, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3051, d5911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24605 p hg
    simpa only [d3051, d5911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24607 (p : Pattern) (guard : d4985 p = 1) : d3052 p ≤ (2 : Int) + d5912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3052, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24606 p hg
    simpa only [d3052, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3052, d5912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3052, d5912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24608 (p : Pattern) (guard : d4985 p = 1) : d3053 p ≤ (2 : Int) + d5913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3053, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24607 p hg
    simpa only [d3053, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3053, d5913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3053, d5913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24609 (p : Pattern) (guard : d4985 p = 1) : d3054 p ≤ (2 : Int) + d5931 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3054, d5931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24597 p hg
    simpa only [d3054, d5931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3054, d5931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24608 p hg
    simpa only [d3054, d5931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24610 (p : Pattern) (guard : d4985 p = 1) : d3055 p ≤ (2 : Int) + d5932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3055, d5932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24582 p hg
    simpa only [d3055, d5932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3055, d5932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24601 p hg
    simpa only [d3055, d5932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24611 (p : Pattern) (guard : d4985 p = 1) : d3056 p ≤ (2 : Int) + d5933 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3056, d5933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3056, d5933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3056, d5933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d3056, d5933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24612 (p : Pattern) (guard : d4985 p = 1) : d3057 p ≤ (2 : Int) + d5934 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3057, d5934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24610 p hg
    simpa only [d3057, d5934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3057, d5934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24611 p hg
    simpa only [d3057, d5934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24613 (p : Pattern) (guard : d4985 p = 1) : d3058 p ≤ (2 : Int) + d5935 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3058, d5935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3058, d5935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3058, d5935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d3058, d5935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24614 (p : Pattern) (guard : d4985 p = 1) : d3059 p ≤ (2 : Int) + d5936 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3059, d5936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24613 p hg
    simpa only [d3059, d5936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3059, d5936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3059, d5936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24615 (p : Pattern) (guard : d4985 p = 1) : d3060 p ≤ (2 : Int) + d5937 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3060, d5937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24612 p hg
    simpa only [d3060, d5937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3060, d5937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24614 p hg
    simpa only [d3060, d5937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24616 (p : Pattern) (guard : d4985 p = 1) : d3061 p ≤ (2 : Int) + d5921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3061, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24605 p hg
    simpa only [d3061, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3061, d5921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3061, d5921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24617 (p : Pattern) (guard : d4985 p = 1) : d3062 p ≤ (2 : Int) + d5922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3062, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24616 p hg
    simpa only [d3062, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3062, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3062, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24618 (p : Pattern) (guard : d4985 p = 1) : d3063 p ≤ (2 : Int) + d5923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3063, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24617 p hg
    simpa only [d3063, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3063, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3063, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24619 (p : Pattern) (guard : d4985 p = 1) : d3064 p ≤ (2 : Int) + d5938 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3064, d5938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24615 p hg
    simpa only [d3064, d5938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3064, d5938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24618 p hg
    simpa only [d3064, d5938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24620 (p : Pattern) (guard : d4985 p = 1) : d3065 p ≤ (2 : Int) + d5939 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3065, d5939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24609 p hg
    simpa only [d3065, d5939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3065, d5939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24619 p hg
    simpa only [d3065, d5939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24621 (p : Pattern) (guard : d4985 p = 1) : d3066 p ≤ (2 : Int) + d5940 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3066, d5940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24563 p hg
    simpa only [d3066, d5940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3066, d5940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24620 p hg
    simpa only [d3066, d5940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24622 (p : Pattern) (guard : d4985 p = 1) : d3067 p ≤ (2 : Int) + d5941 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3067, d5941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24499 p hg
    simpa only [d3067, d5941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3067, d5941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3067, d5941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24623 (p : Pattern) (guard : d4985 p = 1) : d3068 p ≤ (2 : Int) + d5942 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3068, d5942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24622 p hg
    simpa only [d3068, d5942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3068, d5942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3068, d5942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24624 (p : Pattern) (guard : d4985 p = 1) : d3069 p ≤ (2 : Int) + d5943 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3069, d5943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24623 p hg
    simpa only [d3069, d5943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3069, d5943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3069, d5943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24625 (p : Pattern) (guard : d4985 p = 1) : d3070 p ≤ (2 : Int) + d5944 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3070, d5944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24624 p hg
    simpa only [d3070, d5944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3070, d5944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3070, d5944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24626 (p : Pattern) (guard : d4985 p = 1) : d3071 p ≤ (2 : Int) + d5945 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3071, d5945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24620 p hg
    simpa only [d3071, d5945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3071, d5945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24625 p hg
    simpa only [d3071, d5945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24627 (p : Pattern) (guard : d4985 p = 1) : d3072 p ≤ (2 : Int) + d5946 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3072, d5946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24621 p hg
    simpa only [d3072, d5946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3072, d5946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24626 p hg
    simpa only [d3072, d5946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24628 (p : Pattern) (guard : d4985 p = 1) : d3073 p ≤ (2 : Int) + d5947 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3073, d5947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24620 p hg
    simpa only [d3073, d5947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3073, d5947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3073, d5947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24629 (p : Pattern) (guard : d4985 p = 1) : d3074 p ≤ (2 : Int) + d5948 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3074, d5948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24621 p hg
    simpa only [d3074, d5948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3074, d5948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24628 p hg
    simpa only [d3074, d5948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24630 (p : Pattern) (guard : d4985 p = 1) : d3075 p ≤ (2 : Int) + d5949 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3075, d5949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24627 p hg
    simpa only [d3075, d5949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3075, d5949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24629 p hg
    simpa only [d3075, d5949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24631 (p : Pattern) (guard : d4985 p = 1) : d3076 p ≤ (2 : Int) + d5950 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3076, d5950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24480 p hg
    simpa only [d3076, d5950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3076, d5950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24630 p hg
    simpa only [d3076, d5950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24632 (p : Pattern) (guard : d4985 p = 1) : d3077 p ≤ (2 : Int) + d5951 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3077, d5951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24480 p hg
    simpa only [d3077, d5951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3077, d5951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24631 p hg
    simpa only [d3077, d5951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24633 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d2012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24634 (p : Pattern) (guard : d1 p = 1) : d1791 p ≤ (2 : Int) + d1794 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1791, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1791, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1791, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d1791, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24635 (p : Pattern) (guard : d1 p = 1) : d1792 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1792, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24634 p hg
    simpa only [d1792, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1792, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16162 p hg
    simpa only [d1792, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24636 (p : Pattern) (guard : d1 p = 1) : d1793 p ≤ (2 : Int) + d2011 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1793, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1793, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1793, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d1793, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24637 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (2 : Int) + d1795 p := by
  omega
theorem compare24638 (p : Pattern) (guard : d1 p = 1) : d3078 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24637 p hg
    simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24635 p hg
    simpa only [d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24639 (p : Pattern) (guard : d1 p = 1) : d3079 p ≤ (2 : Int) + d2012 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3079, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24636 p hg
    simpa only [d3079, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3079, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24638 p hg
    simpa only [d3079, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
