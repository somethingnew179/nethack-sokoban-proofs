/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons081
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c11480 (pattern : Twelve) (guard : d1901 pattern = 1) : d103 pattern ≤ (0 : Int) + d1948 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d103, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11472 pattern childGuard
    simpa only [d103, d1948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d103, d1948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11479 pattern childGuard
    simpa only [d103, d1948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11481 (pattern : Twelve) (guard : d1901 pattern = 1) : d110 pattern ≤ (0 : Int) + d1949 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d110, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11470 pattern childGuard
    simpa only [d110, d1949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d110, d1949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11480 pattern childGuard
    simpa only [d110, d1949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11482 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11483 (pattern : Twelve) (guard : d1848 pattern = 1) : d30 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11482 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11484 (pattern : Twelve) (guard : d1901 pattern = 1) : d30 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11485 (pattern : Twelve) (guard : d1848 pattern = 1) : d37 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10968 pattern childGuard
    simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7759 pattern childGuard
    simpa only [d1848, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11486 (pattern : Twelve) (guard : d1901 pattern = 1) : d58 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11485 pattern childGuard
    simpa only [d1901, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11487 (pattern : Twelve) (guard : d1901 pattern = 1) : d79 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11484 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11486 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11488 (pattern : Twelve) (guard : d1901 pattern = 1) : d80 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d80, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11484 pattern childGuard
    simpa only [d80, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d80, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11467 pattern childGuard
    simpa only [d80, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11489 (pattern : Twelve) (guard : d1901 pattern = 1) : d95 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d95, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11487 pattern childGuard
    simpa only [d95, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d95, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11488 pattern childGuard
    simpa only [d95, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11490 (pattern : Twelve) (guard : d0 pattern = 1) : d38 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11491 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11492 (pattern : Twelve) (guard : d1901 pattern = 1) : d59 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11490 pattern childGuard
    simpa only [d1901, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11491 pattern childGuard
    simpa only [d1901, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11493 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d4 pattern := by
  change (3 : Int) ≤ (0 : Int) + 4
  decide
theorem c11494 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11493 pattern childGuard
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11495 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11494 pattern childGuard
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11496 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11495 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11497 (pattern : Twelve) (guard : d1901 pattern = 1) : d60 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11490 pattern childGuard
    simpa only [d1901, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11496 pattern childGuard
    simpa only [d1901, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11498 (pattern : Twelve) (guard : d1901 pattern = 1) : d81 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11492 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11497 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11499 (pattern : Twelve) (guard : d0 pattern = 1) : d41 pattern ≤ (0 : Int) + d24 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11500 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11501 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11493 pattern childGuard
    simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d12, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11502 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11500 pattern childGuard
    simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11501 pattern childGuard
    simpa only [d25, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11503 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11502 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11504 (pattern : Twelve) (guard : d1901 pattern = 1) : d61 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11503 pattern childGuard
    simpa only [d1901, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11505 (pattern : Twelve) (guard : d1901 pattern = 1) : d82 pattern ≤ (0 : Int) + d1950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d82, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11492 pattern childGuard
    simpa only [d82, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d82, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11504 pattern childGuard
    simpa only [d82, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11506 (pattern : Twelve) (guard : d1901 pattern = 1) : d96 pattern ≤ (0 : Int) + d1951 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d96, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11498 pattern childGuard
    simpa only [d96, d1951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d96, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11505 pattern childGuard
    simpa only [d96, d1951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11507 (pattern : Twelve) (guard : d1901 pattern = 1) : d104 pattern ≤ (0 : Int) + d1952 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d104, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11489 pattern childGuard
    simpa only [d104, d1952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d104, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11506 pattern childGuard
    simpa only [d104, d1952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11508 (pattern : Twelve) (guard : d1901 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c11509 (pattern : Twelve) (guard : d1901 pattern = 1) : d105 pattern ≤ (0 : Int) + d1953 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11479 pattern childGuard
    simpa only [d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d105, d1953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11510 (pattern : Twelve) (guard : d1901 pattern = 1) : d111 pattern ≤ (0 : Int) + d1954 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d111, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11507 pattern childGuard
    simpa only [d111, d1954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d111, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11509 pattern childGuard
    simpa only [d111, d1954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11511 (pattern : Twelve) (guard : d1901 pattern = 1) : d114 pattern ≤ (0 : Int) + d1955 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d114, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11481 pattern childGuard
    simpa only [d114, d1955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d114, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11510 pattern childGuard
    simpa only [d114, d1955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11512 (pattern : Twelve) (guard : d1901 pattern = 1) : d97 pattern ≤ (0 : Int) + d1956 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d97, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11447 pattern childGuard
    simpa only [d97, d1956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d97, d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11488 pattern childGuard
    simpa only [d97, d1956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11513 (pattern : Twelve) (guard : d1848 pattern = 1) : d43 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11459 pattern childGuard
    simpa only [d1848, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11514 (pattern : Twelve) (guard : d1901 pattern = 1) : d62 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11513 pattern childGuard
    simpa only [d1901, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11515 (pattern : Twelve) (guard : d1901 pattern = 1) : d83 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11458 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11514 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11516 (pattern : Twelve) (guard : d1848 pattern = 1) : d44 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5002 pattern childGuard
    simpa only [d1848, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11517 (pattern : Twelve) (guard : d1901 pattern = 1) : d63 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11516 pattern childGuard
    simpa only [d1901, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11518 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11519 (pattern : Twelve) (guard : d1901 pattern = 1) : d64 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11518 pattern childGuard
    simpa only [d1901, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11520 (pattern : Twelve) (guard : d1901 pattern = 1) : d84 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d84, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11517 pattern childGuard
    simpa only [d84, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d84, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11519 pattern childGuard
    simpa only [d84, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11521 (pattern : Twelve) (guard : d1901 pattern = 1) : d98 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d98, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11515 pattern childGuard
    simpa only [d98, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d98, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11520 pattern childGuard
    simpa only [d98, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11522 (pattern : Twelve) (guard : d1901 pattern = 1) : d106 pattern ≤ (0 : Int) + d1957 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d106, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11512 pattern childGuard
    simpa only [d106, d1957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d106, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11521 pattern childGuard
    simpa only [d106, d1957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11523 (pattern : Twelve) (guard : d1848 pattern = 1) : d45 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11524 (pattern : Twelve) (guard : d1901 pattern = 1) : d65 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11523 pattern childGuard
    simpa only [d1901, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11525 (pattern : Twelve) (guard : d1901 pattern = 1) : d85 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11474 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11524 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11526 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11527 (pattern : Twelve) (guard : d1901 pattern = 1) : d66 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11526 pattern childGuard
    simpa only [d1901, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11528 (pattern : Twelve) (guard : d1901 pattern = 1) : d86 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d86, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11527 pattern childGuard
    simpa only [d86, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d86, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11519 pattern childGuard
    simpa only [d86, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11529 (pattern : Twelve) (guard : d1901 pattern = 1) : d99 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d99, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11525 pattern childGuard
    simpa only [d99, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d99, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11528 pattern childGuard
    simpa only [d99, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11530 (pattern : Twelve) (guard : d1901 pattern = 1) : d107 pattern ≤ (0 : Int) + d1957 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d107, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11512 pattern childGuard
    simpa only [d107, d1957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d107, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11529 pattern childGuard
    simpa only [d107, d1957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11531 (pattern : Twelve) (guard : d1901 pattern = 1) : d112 pattern ≤ (0 : Int) + d1957 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11522 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11530 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11532 (pattern : Twelve) (guard : d1848 pattern = 1) : d46 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7759 pattern childGuard
    simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11533 (pattern : Twelve) (guard : d1901 pattern = 1) : d67 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11532 pattern childGuard
    simpa only [d1901, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11534 (pattern : Twelve) (guard : d1901 pattern = 1) : d87 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11484 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11533 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11535 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7809 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11536 (pattern : Twelve) (guard : d1901 pattern = 1) : d68 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11455 pattern childGuard
    simpa only [d1901, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11535 pattern childGuard
    simpa only [d1901, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11537 (pattern : Twelve) (guard : d1901 pattern = 1) : d88 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d88, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11536 pattern childGuard
    simpa only [d88, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d88, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11519 pattern childGuard
    simpa only [d88, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11538 (pattern : Twelve) (guard : d1901 pattern = 1) : d100 pattern ≤ (0 : Int) + d1944 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d100, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11534 pattern childGuard
    simpa only [d100, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d100, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11537 pattern childGuard
    simpa only [d100, d1944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11539 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11493 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11540 (pattern : Twelve) (guard : d1901 pattern = 1) : d69 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11490 pattern childGuard
    simpa only [d1901, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11539 pattern childGuard
    simpa only [d1901, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11541 (pattern : Twelve) (guard : d1901 pattern = 1) : d89 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11492 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11540 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11542 (pattern : Twelve) (guard : d1848 pattern = 1) : d48 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d1848, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11543 (pattern : Twelve) (guard : d1901 pattern = 1) : d70 pattern ≤ (0 : Int) + d4 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11490 pattern childGuard
    simpa only [d1901, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11542 pattern childGuard
    simpa only [d1901, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11544 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (0 : Int) + d24 pattern := by
  omega
theorem c11545 (pattern : Twelve) (guard : d1848 pattern = 1) : d49 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11544 pattern childGuard
    simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11546 (pattern : Twelve) (guard : d1901 pattern = 1) : d71 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11545 pattern childGuard
    simpa only [d1901, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11547 (pattern : Twelve) (guard : d1901 pattern = 1) : d90 pattern ≤ (0 : Int) + d1950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d90, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11543 pattern childGuard
    simpa only [d90, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d90, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11546 pattern childGuard
    simpa only [d90, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11548 (pattern : Twelve) (guard : d1901 pattern = 1) : d101 pattern ≤ (0 : Int) + d1951 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d101, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11541 pattern childGuard
    simpa only [d101, d1951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d101, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11547 pattern childGuard
    simpa only [d101, d1951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11549 (pattern : Twelve) (guard : d1901 pattern = 1) : d108 pattern ≤ (0 : Int) + d1952 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d108, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11538 pattern childGuard
    simpa only [d108, d1952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d108, d1952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11548 pattern childGuard
    simpa only [d108, d1952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11550 (pattern : Twelve) (guard : d1901 pattern = 1) : d109 pattern ≤ (0 : Int) + d1953 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d109, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11529 pattern childGuard
    simpa only [d109, d1953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d109, d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d109, d1953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11551 (pattern : Twelve) (guard : d1901 pattern = 1) : d113 pattern ≤ (0 : Int) + d1954 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d113, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11549 pattern childGuard
    simpa only [d113, d1954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d113, d1954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11550 pattern childGuard
    simpa only [d113, d1954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11552 (pattern : Twelve) (guard : d1901 pattern = 1) : d115 pattern ≤ (0 : Int) + d1958 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d115, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11531 pattern childGuard
    simpa only [d115, d1958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d115, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11551 pattern childGuard
    simpa only [d115, d1958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11553 (pattern : Twelve) (guard : d1901 pattern = 1) : d116 pattern ≤ (0 : Int) + d1959 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d116, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11511 pattern childGuard
    simpa only [d116, d1959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d116, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11552 pattern childGuard
    simpa only [d116, d1959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11554 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11555 (pattern : Twelve) (guard : d1848 pattern = 1) : d816 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10959 pattern childGuard
    simpa only [d1848, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11444 pattern childGuard
    simpa only [d1848, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11556 (pattern : Twelve) (guard : d1901 pattern = 1) : d824 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11554 pattern childGuard
    simpa only [d1901, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11555 pattern childGuard
    simpa only [d1901, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11557 (pattern : Twelve) (guard : d1901 pattern = 1) : d838 pattern ≤ (0 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11442 pattern childGuard
    simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11556 pattern childGuard
    simpa only [d838, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11558 (pattern : Twelve) (guard : d1901 pattern = 1) : d17 pattern ≤ (0 : Int) + d17 pattern := by
  omega
theorem c11559 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (0 : Int) + d25 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11560 (pattern : Twelve) (guard : d1901 pattern = 1) : d825 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11559 pattern childGuard
    simpa only [d1901, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d1901, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11561 (pattern : Twelve) (guard : d1901 pattern = 1) : d839 pattern ≤ (0 : Int) + d1960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11558 pattern childGuard
    simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d839, d1960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11562 (pattern : Twelve) (guard : d1901 pattern = 1) : d853 pattern ≤ (0 : Int) + d1961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d853, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11557 pattern childGuard
    simpa only [d853, d1961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d853, d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11561 pattern childGuard
    simpa only [d853, d1961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11563 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10967 pattern childGuard
    simpa only [d814, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10929 pattern childGuard
    simpa only [d814, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11564 (pattern : Twelve) (guard : d1848 pattern = 1) : d818 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11563 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11565 (pattern : Twelve) (guard : d1901 pattern = 1) : d826 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11564 pattern childGuard
    simpa only [d1901, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11566 (pattern : Twelve) (guard : d1901 pattern = 1) : d840 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d840, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11474 pattern childGuard
    simpa only [d840, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d840, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11565 pattern childGuard
    simpa only [d840, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11567 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10880 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11568 (pattern : Twelve) (guard : d1901 pattern = 1) : d827 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11567 pattern childGuard
    simpa only [d1901, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11569 (pattern : Twelve) (guard : d1901 pattern = 1) : d841 pattern ≤ (0 : Int) + d1962 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d841, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11568 pattern childGuard
    simpa only [d841, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d841, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d841, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11570 (pattern : Twelve) (guard : d1901 pattern = 1) : d854 pattern ≤ (0 : Int) + d1963 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d854, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11566 pattern childGuard
    simpa only [d854, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d854, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11569 pattern childGuard
    simpa only [d854, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11571 (pattern : Twelve) (guard : d1901 pattern = 1) : d861 pattern ≤ (0 : Int) + d1964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d861, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11562 pattern childGuard
    simpa only [d861, d1964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d861, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11570 pattern childGuard
    simpa only [d861, d1964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11572 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11573 (pattern : Twelve) (guard : d1848 pattern = 1) : d819 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11563 pattern childGuard
    simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11572 pattern childGuard
    simpa only [d1848, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11574 (pattern : Twelve) (guard : d1901 pattern = 1) : d828 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11573 pattern childGuard
    simpa only [d1901, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11575 (pattern : Twelve) (guard : d1901 pattern = 1) : d842 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d842, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11484 pattern childGuard
    simpa only [d842, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d842, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11574 pattern childGuard
    simpa only [d842, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11576 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11577 (pattern : Twelve) (guard : d1848 pattern = 1) : d34 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10880 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11576 pattern childGuard
    simpa only [d1848, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11578 (pattern : Twelve) (guard : d1901 pattern = 1) : d34 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11579 (pattern : Twelve) (guard : d1901 pattern = 1) : d843 pattern ≤ (0 : Int) + d1962 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d843, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11578 pattern childGuard
    simpa only [d843, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d843, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d843, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11580 (pattern : Twelve) (guard : d1901 pattern = 1) : d855 pattern ≤ (0 : Int) + d1963 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d855, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11575 pattern childGuard
    simpa only [d855, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d855, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11579 pattern childGuard
    simpa only [d855, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11581 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11493 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10884 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11582 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11494 pattern childGuard
    simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11581 pattern childGuard
    simpa only [d815, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11583 (pattern : Twelve) (guard : d1848 pattern = 1) : d820 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11582 pattern childGuard
    simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11584 (pattern : Twelve) (guard : d1901 pattern = 1) : d829 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11583 pattern childGuard
    simpa only [d1901, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11585 (pattern : Twelve) (guard : d1901 pattern = 1) : d844 pattern ≤ (0 : Int) + d1950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d844, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11492 pattern childGuard
    simpa only [d844, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d844, d1950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11584 pattern childGuard
    simpa only [d844, d1950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11586 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10886 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d1848, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11587 (pattern : Twelve) (guard : d1901 pattern = 1) : d830 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11499 pattern childGuard
    simpa only [d1901, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11586 pattern childGuard
    simpa only [d1901, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11588 (pattern : Twelve) (guard : d0 pattern = 1) : d821 pattern ≤ (0 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11589 (pattern : Twelve) (guard : d1 pattern = 1) : d21 pattern ≤ (0 : Int) + d21 pattern := by
  omega
theorem c11590 (pattern : Twelve) (guard : d1848 pattern = 1) : d822 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11589 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5122 pattern childGuard
    simpa only [d1848, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11591 (pattern : Twelve) (guard : d1901 pattern = 1) : d831 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11588 pattern childGuard
    simpa only [d1901, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11590 pattern childGuard
    simpa only [d1901, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11592 (pattern : Twelve) (guard : d1901 pattern = 1) : d845 pattern ≤ (0 : Int) + d1965 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d845, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11587 pattern childGuard
    simpa only [d845, d1965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d845, d1965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11591 pattern childGuard
    simpa only [d845, d1965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11593 (pattern : Twelve) (guard : d1901 pattern = 1) : d856 pattern ≤ (0 : Int) + d1966 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d856, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11585 pattern childGuard
    simpa only [d856, d1966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d856, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11592 pattern childGuard
    simpa only [d856, d1966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11594 (pattern : Twelve) (guard : d1901 pattern = 1) : d862 pattern ≤ (0 : Int) + d1967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d862, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11580 pattern childGuard
    simpa only [d862, d1967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d862, d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11593 pattern childGuard
    simpa only [d862, d1967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11595 (pattern : Twelve) (guard : d1901 pattern = 1) : d863 pattern ≤ (0 : Int) + d1968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d863, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11570 pattern childGuard
    simpa only [d863, d1968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d863, d1968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11508 pattern childGuard
    simpa only [d863, d1968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11596 (pattern : Twelve) (guard : d1901 pattern = 1) : d867 pattern ≤ (0 : Int) + d1969 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d867, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11594 pattern childGuard
    simpa only [d867, d1969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d867, d1969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11595 pattern childGuard
    simpa only [d867, d1969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11597 (pattern : Twelve) (guard : d1901 pattern = 1) : d869 pattern ≤ (0 : Int) + d1970 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d869, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11571 pattern childGuard
    simpa only [d869, d1970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d869, d1970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11596 pattern childGuard
    simpa only [d869, d1970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11598 (pattern : Twelve) (guard : d0 pattern = 1) : d823 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11599 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10968 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11482 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11600 (pattern : Twelve) (guard : d1901 pattern = 1) : d823 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11598 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11599 pattern childGuard
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11601 (pattern : Twelve) (guard : d1901 pattern = 1) : d846 pattern ≤ (0 : Int) + d1971 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d846, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11600 pattern childGuard
    simpa only [d846, d1971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d846, d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d846, d1971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11602 (pattern : Twelve) (guard : d1901 pattern = 1) : d857 pattern ≤ (0 : Int) + d1972 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d857, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11557 pattern childGuard
    simpa only [d857, d1972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d857, d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11601 pattern childGuard
    simpa only [d857, d1972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11603 (pattern : Twelve) (guard : d1848 pattern = 1) : d45 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10930 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11604 (pattern : Twelve) (guard : d1901 pattern = 1) : d832 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11603 pattern childGuard
    simpa only [d1901, d832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11605 (pattern : Twelve) (guard : d1901 pattern = 1) : d847 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d847, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11474 pattern childGuard
    simpa only [d847, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d847, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11604 pattern childGuard
    simpa only [d847, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11606 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10965 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d1848, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11607 (pattern : Twelve) (guard : d1901 pattern = 1) : d833 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11606 pattern childGuard
    simpa only [d1901, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11608 (pattern : Twelve) (guard : d1901 pattern = 1) : d848 pattern ≤ (0 : Int) + d1962 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d848, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11607 pattern childGuard
    simpa only [d848, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d848, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d848, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11609 (pattern : Twelve) (guard : d1901 pattern = 1) : d858 pattern ≤ (0 : Int) + d1963 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d858, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11605 pattern childGuard
    simpa only [d858, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d858, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11608 pattern childGuard
    simpa only [d858, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11610 (pattern : Twelve) (guard : d1901 pattern = 1) : d864 pattern ≤ (0 : Int) + d1973 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d864, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11602 pattern childGuard
    simpa only [d864, d1973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d864, d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11609 pattern childGuard
    simpa only [d864, d1973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11611 (pattern : Twelve) (guard : d1848 pattern = 1) : d46 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10930 pattern childGuard
    simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11572 pattern childGuard
    simpa only [d1848, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11612 (pattern : Twelve) (guard : d1901 pattern = 1) : d834 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11611 pattern childGuard
    simpa only [d1901, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11613 (pattern : Twelve) (guard : d1901 pattern = 1) : d849 pattern ≤ (0 : Int) + d1943 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d849, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11484 pattern childGuard
    simpa only [d849, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d849, d1943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11612 pattern childGuard
    simpa only [d849, d1943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11614 (pattern : Twelve) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c11615 (pattern : Twelve) (guard : d1848 pattern = 1) : d38 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10965 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11614 pattern childGuard
    simpa only [d1848, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11616 (pattern : Twelve) (guard : d1901 pattern = 1) : d835 pattern ≤ (0 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1901, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11465 pattern childGuard
    simpa only [d1901, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1901, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11615 pattern childGuard
    simpa only [d1901, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11617 (pattern : Twelve) (guard : d1901 pattern = 1) : d850 pattern ≤ (0 : Int) + d1962 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d850, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11616 pattern childGuard
    simpa only [d850, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d850, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11560 pattern childGuard
    simpa only [d850, d1962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11618 (pattern : Twelve) (guard : d1901 pattern = 1) : d859 pattern ≤ (0 : Int) + d1963 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1901 pattern = 1 := by simpa only [d859, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11613 pattern childGuard
    simpa only [d859, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1901 pattern = 1 := by simpa only [d859, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11617 pattern childGuard
    simpa only [d859, d1963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c11619 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11493 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11581 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
