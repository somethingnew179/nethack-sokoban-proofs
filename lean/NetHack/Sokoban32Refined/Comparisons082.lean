/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11480 (p : Pattern) (guard : d1966 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11481 (p : Pattern) (guard : d1967 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d1967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11482 (p : Pattern) (guard : d1968 p = 1) : d761 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11479 p hg
    simpa only [d1968, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11481 p hg
    simpa only [d1968, d761, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11483 (p : Pattern) (guard : d1969 p = 1) : d762 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d1969, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d1969, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11484 (p : Pattern) (guard : d1957 p = 1) : d763 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d1957, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11485 (p : Pattern) (guard : d1958 p = 1) : d764 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d1958, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11484 p hg
    simpa only [d1958, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11486 (p : Pattern) (guard : d0 p = 1) : d744 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11487 (p : Pattern) (guard : d1956 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11422 p hg
    simpa only [d1956, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11486 p hg
    simpa only [d1956, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11488 (p : Pattern) (guard : d1961 p = 1) : d763 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d1961, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11489 (p : Pattern) (guard : d1962 p = 1) : d764 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1962, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d1962, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11490 (p : Pattern) (guard : d1963 p = 1) : d764 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11485 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11489 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11491 (p : Pattern) (guard : d0 p = 1) : d765 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11492 (p : Pattern) (guard : d1966 p = 1) : d766 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11426 p hg
    simpa only [d1966, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11491 p hg
    simpa only [d1966, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11493 (p : Pattern) (guard : d1967 p = 1) : d767 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11489 p hg
    simpa only [d1967, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11492 p hg
    simpa only [d1967, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11494 (p : Pattern) (guard : d1968 p = 1) : d768 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d1968, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11493 p hg
    simpa only [d1968, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11495 (p : Pattern) (guard : d1293 p = 1) : d9 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11496 (p : Pattern) (guard : d1951 p = 1) : d746 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d1951, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d1951, d746, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11497 (p : Pattern) (guard : d1956 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d1956, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11434 p hg
    simpa only [d1956, d748, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11498 (p : Pattern) (guard : d1957 p = 1) : d749 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d1957, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11499 (p : Pattern) (guard : d1962 p = 1) : d764 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d1962, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d1962, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11500 (p : Pattern) (guard : d1967 p = 1) : d767 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11499 p hg
    simpa only [d1967, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11492 p hg
    simpa only [d1967, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11501 (p : Pattern) (guard : d1971 p = 1) : d766 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11492 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11502 (p : Pattern) (guard : d1972 p = 1) : d769 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11500 p hg
    simpa only [d1972, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11501 p hg
    simpa only [d1972, d769, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11503 (p : Pattern) (guard : d1973 p = 1) : d770 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11494 p hg
    simpa only [d1973, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d1973, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11504 (p : Pattern) (guard : d1974 p = 1) : d771 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11483 p hg
    simpa only [d1974, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11503 p hg
    simpa only [d1974, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11505 (p : Pattern) (guard : d1975 p = 1) : d772 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1970 p = 1 := by simpa only [d1975, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11463 p hg
    simpa only [d1975, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1974 p = 1 := by simpa only [d1975, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11504 p hg
    simpa only [d1975, d772, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11506 (p : Pattern) (guard : d1951 p = 1) : d23 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11385 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1951, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11507 (p : Pattern) (guard : d1952 p = 1) : d752 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1947 p = 1 := by simpa only [d1952, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11475 p hg
    simpa only [d1952, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1951 p = 1 := by simpa only [d1952, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11506 p hg
    simpa only [d1952, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11508 (p : Pattern) (guard : d1956 p = 1) : d752 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d1956, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d1956, d752, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11509 (p : Pattern) (guard : d1957 p = 1) : d752 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11510 (p : Pattern) (guard : d1961 p = 1) : d773 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11404 p hg
    simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11511 (p : Pattern) (guard : d1962 p = 1) : d774 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d774, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d1962, d774, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d774, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d1962, d774, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11512 (p : Pattern) (guard : d1961 p = 1) : d752 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11404 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11425 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11513 (p : Pattern) (guard : d1966 p = 1) : d774 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11512 p hg
    simpa only [d1966, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1966, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11514 (p : Pattern) (guard : d1967 p = 1) : d774 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11511 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11515 (p : Pattern) (guard : d1968 p = 1) : d775 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d775, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d1968, d775, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d775, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11514 p hg
    simpa only [d1968, d775, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11516 (p : Pattern) (guard : d1969 p = 1) : d776 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1964 p = 1 := by simpa only [d1969, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11443 p hg
    simpa only [d1969, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1968 p = 1 := by simpa only [d1969, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11515 p hg
    simpa only [d1969, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11517 (p : Pattern) (guard : d1957 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11432 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11518 (p : Pattern) (guard : d0 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11519 (p : Pattern) (guard : d1961 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11518 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11520 (p : Pattern) (guard : d1962 p = 1) : d750 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d1962, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1962, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11521 (p : Pattern) (guard : d1963 p = 1) : d750 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11451 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11520 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11522 (p : Pattern) (guard : d1956 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11453 p hg
    simpa only [d1956, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11486 p hg
    simpa only [d1956, d745, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11523 (p : Pattern) (guard : d1957 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11439 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11524 (p : Pattern) (guard : d1962 p = 1) : d750 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11523 p hg
    simpa only [d1962, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1962, d750, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11525 (p : Pattern) (guard : d1967 p = 1) : d755 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11524 p hg
    simpa only [d1967, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d1967, d755, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11526 (p : Pattern) (guard : d1968 p = 1) : d756 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11521 p hg
    simpa only [d1968, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11525 p hg
    simpa only [d1968, d756, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11527 (p : Pattern) (guard : d1293 p = 1) : d3 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11528 (p : Pattern) (guard : d1951 p = 1) : d743 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d1951, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11527 p hg
    simpa only [d1951, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1951, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1951, d743, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11529 (p : Pattern) (guard : d0 p = 1) : d744 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11530 (p : Pattern) (guard : d1956 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1951 p = 1 := by simpa only [d1956, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11528 p hg
    simpa only [d1956, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1956, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11529 p hg
    simpa only [d1956, d745, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11531 (p : Pattern) (guard : d1957 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11449 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11530 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11532 (p : Pattern) (guard : d1962 p = 1) : d750 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11531 p hg
    simpa only [d1962, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1962, d750, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11533 (p : Pattern) (guard : d1967 p = 1) : d755 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11532 p hg
    simpa only [d1967, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d1967, d755, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11534 (p : Pattern) (guard : d1961 p = 1) : d773 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1961, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11535 (p : Pattern) (guard : d1966 p = 1) : d773 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11534 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1966, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11536 (p : Pattern) (guard : d1971 p = 1) : d773 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11535 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11537 (p : Pattern) (guard : d1972 p = 1) : d777 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d1972, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11536 p hg
    simpa only [d1972, d777, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11538 (p : Pattern) (guard : d1973 p = 1) : d778 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d1973, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d1973, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11539 (p : Pattern) (guard : d1974 p = 1) : d779 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11516 p hg
    simpa only [d1974, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d1974, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11540 (p : Pattern) (guard : d1962 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11436 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11541 (p : Pattern) (guard : d1963 p = 1) : d749 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11478 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11540 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11542 (p : Pattern) (guard : d1967 p = 1) : d759 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11540 p hg
    simpa only [d1967, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d1967, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11543 (p : Pattern) (guard : d1968 p = 1) : d760 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d1968, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d1968, d760, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11544 (p : Pattern) (guard : d1962 p = 1) : d749 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1962, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11545 (p : Pattern) (guard : d1967 p = 1) : d759 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11544 p hg
    simpa only [d1967, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d1967, d759, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11546 (p : Pattern) (guard : d1966 p = 1) : d773 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11547 (p : Pattern) (guard : d1971 p = 1) : d773 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11546 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11548 (p : Pattern) (guard : d1972 p = 1) : d780 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11545 p hg
    simpa only [d1972, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11547 p hg
    simpa only [d1972, d780, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11549 (p : Pattern) (guard : d1973 p = 1) : d781 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d1973, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11548 p hg
    simpa only [d1973, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11550 (p : Pattern) (guard : d0 p = 1) : d763 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11551 (p : Pattern) (guard : d1966 p = 1) : d764 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d1966, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11552 (p : Pattern) (guard : d1967 p = 1) : d764 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11499 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11551 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11553 (p : Pattern) (guard : d1971 p = 1) : d767 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11551 p hg
    simpa only [d1971, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1971, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11554 (p : Pattern) (guard : d1972 p = 1) : d768 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11552 p hg
    simpa only [d1972, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11553 p hg
    simpa only [d1972, d768, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11555 (p : Pattern) (guard : d0 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11556 (p : Pattern) (guard : d1961 p = 1) : d749 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11555 p hg
    simpa only [d1961, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11557 (p : Pattern) (guard : d1966 p = 1) : d764 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11556 p hg
    simpa only [d1966, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d764, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11558 (p : Pattern) (guard : d1971 p = 1) : d767 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11557 p hg
    simpa only [d1971, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1971, d767, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11559 (p : Pattern) (guard : d1976 p = 1) : d782 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d782, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11558 p hg
    simpa only [d1976, d782, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d782, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1976, d782, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11560 (p : Pattern) (guard : d1977 p = 1) : d783 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11554 p hg
    simpa only [d1977, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d1977, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11561 (p : Pattern) (guard : d1978 p = 1) : d784 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11549 p hg
    simpa only [d1978, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11560 p hg
    simpa only [d1978, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11562 (p : Pattern) (guard : d1979 p = 1) : d785 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d785, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11539 p hg
    simpa only [d1979, d785, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d785, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11561 p hg
    simpa only [d1979, d785, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11563 (p : Pattern) (guard : d1980 p = 1) : d786 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1975 p = 1 := by simpa only [d1980, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d1980, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11562 p hg
    simpa only [d1980, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11564 (p : Pattern) (guard : d1958 p = 1) : d787 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11450 p hg
    simpa only [d1958, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11484 p hg
    simpa only [d1958, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11565 (p : Pattern) (guard : d1962 p = 1) : d787 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d1962, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d1962, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11566 (p : Pattern) (guard : d1963 p = 1) : d787 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11564 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11565 p hg
    simpa only [d1963, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11567 (p : Pattern) (guard : d1962 p = 1) : d787 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11523 p hg
    simpa only [d1962, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d1962, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11568 (p : Pattern) (guard : d1966 p = 1) : d788 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d1966, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11491 p hg
    simpa only [d1966, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11569 (p : Pattern) (guard : d1967 p = 1) : d789 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11567 p hg
    simpa only [d1967, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11568 p hg
    simpa only [d1967, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11570 (p : Pattern) (guard : d1968 p = 1) : d790 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11566 p hg
    simpa only [d1968, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11569 p hg
    simpa only [d1968, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11571 (p : Pattern) (guard : d1962 p = 1) : d787 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11531 p hg
    simpa only [d1962, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d1962, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11572 (p : Pattern) (guard : d1967 p = 1) : d789 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11571 p hg
    simpa only [d1967, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11568 p hg
    simpa only [d1967, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11573 (p : Pattern) (guard : d0 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11574 (p : Pattern) (guard : d1961 p = 1) : d751 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11454 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11573 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11575 (p : Pattern) (guard : d1966 p = 1) : d788 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d788, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11574 p hg
    simpa only [d1966, d788, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d788, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11491 p hg
    simpa only [d1966, d788, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11576 (p : Pattern) (guard : d1971 p = 1) : d788 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11575 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1971, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11577 (p : Pattern) (guard : d1972 p = 1) : d791 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11572 p hg
    simpa only [d1972, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11576 p hg
    simpa only [d1972, d791, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11578 (p : Pattern) (guard : d1973 p = 1) : d792 p ≤ (0 : Int) + d141 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11570 p hg
    simpa only [d1973, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11577 p hg
    simpa only [d1973, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11579 (p : Pattern) (guard : d1974 p = 1) : d793 p ≤ (0 : Int) + d141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1969 p = 1 := by simpa only [d1974, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d1974, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1973 p = 1 := by simpa only [d1974, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11578 p hg
    simpa only [d1974, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11580 (p : Pattern) (guard : d1953 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1948 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11466 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1952 p = 1 := by simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11476 p hg
    simpa only [d1953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11581 (p : Pattern) (guard : d1957 p = 1) : d794 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11389 p hg
    simpa only [d1957, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9596 p hg
    simpa only [d1957, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11582 (p : Pattern) (guard : d1958 p = 1) : d795 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1953 p = 1 := by simpa only [d1958, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11580 p hg
    simpa only [d1958, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1957 p = 1 := by simpa only [d1958, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11581 p hg
    simpa only [d1958, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11583 (p : Pattern) (guard : d1957 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11389 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11584 (p : Pattern) (guard : d1961 p = 1) : d794 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1961, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11585 (p : Pattern) (guard : d1962 p = 1) : d795 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d1962, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11584 p hg
    simpa only [d1962, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11586 (p : Pattern) (guard : d1963 p = 1) : d795 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1958 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11582 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1962 p = 1 := by simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11585 p hg
    simpa only [d1963, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11587 (p : Pattern) (guard : d1967 p = 1) : d796 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11585 p hg
    simpa only [d1967, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d1967, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11588 (p : Pattern) (guard : d1968 p = 1) : d797 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1963 p = 1 := by simpa only [d1968, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11586 p hg
    simpa only [d1968, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1967 p = 1 := by simpa only [d1968, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11587 p hg
    simpa only [d1968, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11589 (p : Pattern) (guard : d1957 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1952 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11476 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1956 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11590 (p : Pattern) (guard : d1962 p = 1) : d795 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1957 p = 1 := by simpa only [d1962, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11589 p hg
    simpa only [d1962, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1961 p = 1 := by simpa only [d1962, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11584 p hg
    simpa only [d1962, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11591 (p : Pattern) (guard : d1967 p = 1) : d796 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11590 p hg
    simpa only [d1967, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d1967, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11592 (p : Pattern) (guard : d1971 p = 1) : d774 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11593 (p : Pattern) (guard : d1972 p = 1) : d798 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11591 p hg
    simpa only [d1972, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11592 p hg
    simpa only [d1972, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11594 (p : Pattern) (guard : d1973 p = 1) : d799 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1968 p = 1 := by simpa only [d1973, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11588 p hg
    simpa only [d1973, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1972 p = 1 := by simpa only [d1973, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11593 p hg
    simpa only [d1973, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11595 (p : Pattern) (guard : d1961 p = 1) : d748 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11435 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11518 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11596 (p : Pattern) (guard : d1966 p = 1) : d795 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11595 p hg
    simpa only [d1966, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1966, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11597 (p : Pattern) (guard : d1967 p = 1) : d795 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11590 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11596 p hg
    simpa only [d1967, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11598 (p : Pattern) (guard : d1971 p = 1) : d796 p ≤ (0 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11596 p hg
    simpa only [d1971, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1971, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11599 (p : Pattern) (guard : d1972 p = 1) : d797 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11597 p hg
    simpa only [d1972, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11598 p hg
    simpa only [d1972, d797, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11600 (p : Pattern) (guard : d1961 p = 1) : d748 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11555 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11601 (p : Pattern) (guard : d1966 p = 1) : d795 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11600 p hg
    simpa only [d1966, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1966, d795, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11602 (p : Pattern) (guard : d1971 p = 1) : d796 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11601 p hg
    simpa only [d1971, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1971, d796, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11603 (p : Pattern) (guard : d1976 p = 1) : d798 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1976, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11602 p hg
    simpa only [d1976, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1976, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1976, d798, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11604 (p : Pattern) (guard : d1977 p = 1) : d799 p ≤ (0 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1977, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11599 p hg
    simpa only [d1977, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1976 p = 1 := by simpa only [d1977, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11603 p hg
    simpa only [d1977, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11605 (p : Pattern) (guard : d1978 p = 1) : d799 p ≤ (0 : Int) + d152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11594 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11604 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11606 (p : Pattern) (guard : d1979 p = 1) : d800 p ≤ (0 : Int) + d1991 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1979, d800, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11579 p hg
    simpa only [d1979, d800, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, d800, d1991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11605 p hg
    simpa only [d1979, d800, d1991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11607 (p : Pattern) (guard : d0 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11608 (p : Pattern) (guard : d1961 p = 1) : d745 p ≤ (0 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11607 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11609 (p : Pattern) (guard : d1966 p = 1) : d787 p ≤ (0 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d1966, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11610 (p : Pattern) (guard : d1967 p = 1) : d787 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1962 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11571 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1966 p = 1 := by simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11609 p hg
    simpa only [d1967, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11611 (p : Pattern) (guard : d0 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11612 (p : Pattern) (guard : d1961 p = 1) : d745 p ≤ (0 : Int) + d138 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11613 (p : Pattern) (guard : d1966 p = 1) : d787 p ≤ (0 : Int) + d139 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d1966, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d787, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11614 (p : Pattern) (guard : d1971 p = 1) : d789 p ≤ (0 : Int) + d140 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11613 p hg
    simpa only [d1971, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1971, d789, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11615 (p : Pattern) (guard : d1972 p = 1) : d790 p ≤ (0 : Int) + d141 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1967 p = 1 := by simpa only [d1972, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d1972, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1971 p = 1 := by simpa only [d1972, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d1972, d790, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11616 (p : Pattern) (guard : d0 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11617 (p : Pattern) (guard : d1961 p = 1) : d745 p ≤ (0 : Int) + d135 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1956 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11530 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11616 p hg
    simpa only [d1961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11618 (p : Pattern) (guard : d1966 p = 1) : d787 p ≤ (0 : Int) + d136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1961 p = 1 := by simpa only [d1966, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d1966, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1966, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d1966, d787, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11619 (p : Pattern) (guard : d1971 p = 1) : d789 p ≤ (0 : Int) + d137 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1966 p = 1 := by simpa only [d1971, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11618 p hg
    simpa only [d1971, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1971, d789, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
