/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15540 (p : Pattern) (guard : d4967 p = 1) : d2037 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2037, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15539 p hg
    simpa only [d2037, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2037, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15311 p hg
    simpa only [d2037, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15541 (p : Pattern) (guard : d4967 p = 1) : d2038 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2038, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15538 p hg
    simpa only [d2038, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2038, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15540 p hg
    simpa only [d2038, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15542 (p : Pattern) (guard : d4967 p = 1) : d2039 p ≤ (0 : Int) + d1615 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2039, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15524 p hg
    simpa only [d2039, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2039, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d2039, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15543 (p : Pattern) (guard : d4967 p = 1) : d2040 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2040, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d2040, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2040, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15320 p hg
    simpa only [d2040, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15544 (p : Pattern) (guard : d4967 p = 1) : d2041 p ≤ (0 : Int) + d1616 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2041, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15542 p hg
    simpa only [d2041, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2041, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15543 p hg
    simpa only [d2041, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15545 (p : Pattern) (guard : d4967 p = 1) : d2042 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2042, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15527 p hg
    simpa only [d2042, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2042, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2042, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15546 (p : Pattern) (guard : d4967 p = 1) : d2043 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2043, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15545 p hg
    simpa only [d2043, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2043, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2043, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15547 (p : Pattern) (guard : d4967 p = 1) : d2044 p ≤ (0 : Int) + d1617 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2044, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15544 p hg
    simpa only [d2044, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2044, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15546 p hg
    simpa only [d2044, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15548 (p : Pattern) (guard : d4967 p = 1) : d2045 p ≤ (0 : Int) + d1618 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2045, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15541 p hg
    simpa only [d2045, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2045, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15547 p hg
    simpa only [d2045, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15549 (p : Pattern) (guard : d4967 p = 1) : d2046 p ≤ (0 : Int) + d1619 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2046, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15533 p hg
    simpa only [d2046, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2046, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15548 p hg
    simpa only [d2046, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15550 (p : Pattern) (guard : d0 p = 1) : d2049 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15551 (p : Pattern) (guard : d4967 p = 1) : d2050 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2050, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d2050, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2050, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15550 p hg
    simpa only [d4967, d2050, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15552 (p : Pattern) (guard : d0 p = 1) : d2055 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15553 (p : Pattern) (guard : d4967 p = 1) : d2056 p ≤ (0 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2056, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d2056, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2056, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d4967, d2056, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15554 (p : Pattern) (guard : d4967 p = 1) : d2057 p ≤ (0 : Int) + d46 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15551 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15553 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15555 (p : Pattern) (guard : d4967 p = 1) : d2058 p ≤ (0 : Int) + d1620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2058, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15554 p hg
    simpa only [d2058, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2058, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15344 p hg
    simpa only [d2058, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15556 (p : Pattern) (guard : d4967 p = 1) : d2059 p ≤ (0 : Int) + d1621 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2059, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15555 p hg
    simpa only [d2059, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2059, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15345 p hg
    simpa only [d2059, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15557 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15558 (p : Pattern) (guard : d4474 p = 1) : d192 p ≤ (0 : Int) + d191 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15557 p hg
    simpa only [d4474, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15559 (p : Pattern) (guard : d0 p = 1) : d2062 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15560 (p : Pattern) (guard : d4967 p = 1) : d2063 p ≤ (0 : Int) + d1622 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2063, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15558 p hg
    simpa only [d4967, d2063, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2063, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15559 p hg
    simpa only [d4967, d2063, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15561 (p : Pattern) (guard : d4967 p = 1) : d2064 p ≤ (0 : Int) + d1623 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2064, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d2064, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2064, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15560 p hg
    simpa only [d2064, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15562 (p : Pattern) (guard : d4967 p = 1) : d2065 p ≤ (0 : Int) + d1624 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2065, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15561 p hg
    simpa only [d2065, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2065, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2065, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15563 (p : Pattern) (guard : d4967 p = 1) : d2066 p ≤ (0 : Int) + d1625 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2066, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15562 p hg
    simpa only [d2066, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2066, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2066, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15564 (p : Pattern) (guard : d4967 p = 1) : d2067 p ≤ (0 : Int) + d1626 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2067, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15556 p hg
    simpa only [d2067, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2067, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15563 p hg
    simpa only [d2067, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15565 (p : Pattern) (guard : d0 p = 1) : d2072 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15566 (p : Pattern) (guard : d4967 p = 1) : d2073 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2073, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d2073, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2073, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d4967, d2073, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15567 (p : Pattern) (guard : d4967 p = 1) : d2074 p ≤ (0 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15566 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15342 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15568 (p : Pattern) (guard : d4967 p = 1) : d2075 p ≤ (0 : Int) + d1627 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2075, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15334 p hg
    simpa only [d2075, d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2075, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d2075, d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15569 (p : Pattern) (guard : d4967 p = 1) : d2076 p ≤ (0 : Int) + d1628 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2076, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15567 p hg
    simpa only [d2076, d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2076, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15568 p hg
    simpa only [d2076, d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15570 (p : Pattern) (guard : d4967 p = 1) : d2077 p ≤ (0 : Int) + d1629 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2077, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15569 p hg
    simpa only [d2077, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2077, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15355 p hg
    simpa only [d2077, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15571 (p : Pattern) (guard : d4967 p = 1) : d2078 p ≤ (0 : Int) + d1630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2078, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15560 p hg
    simpa only [d2078, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2078, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2078, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15572 (p : Pattern) (guard : d4967 p = 1) : d2079 p ≤ (0 : Int) + d1631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2079, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15571 p hg
    simpa only [d2079, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2079, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2079, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15573 (p : Pattern) (guard : d4967 p = 1) : d2080 p ≤ (0 : Int) + d1632 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2080, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15572 p hg
    simpa only [d2080, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2080, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2080, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15574 (p : Pattern) (guard : d4967 p = 1) : d2081 p ≤ (0 : Int) + d1633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2081, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15570 p hg
    simpa only [d2081, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2081, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15573 p hg
    simpa only [d2081, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15575 (p : Pattern) (guard : d4967 p = 1) : d2082 p ≤ (0 : Int) + d1634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2082, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15564 p hg
    simpa only [d2082, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2082, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15574 p hg
    simpa only [d2082, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15576 (p : Pattern) (guard : d4967 p = 1) : d2083 p ≤ (0 : Int) + d1635 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2083, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15549 p hg
    simpa only [d2083, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2083, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15575 p hg
    simpa only [d2083, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15577 (p : Pattern) (guard : d4967 p = 1) : d2084 p ≤ (0 : Int) + d1636 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2084, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15575 p hg
    simpa only [d2084, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2084, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2084, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15578 (p : Pattern) (guard : d4967 p = 1) : d2085 p ≤ (0 : Int) + d1637 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2085, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15576 p hg
    simpa only [d2085, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2085, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15577 p hg
    simpa only [d2085, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15579 (p : Pattern) (guard : d4967 p = 1) : d2086 p ≤ (0 : Int) + d1638 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2086, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15405 p hg
    simpa only [d2086, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2086, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15578 p hg
    simpa only [d2086, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15580 (p : Pattern) (guard : d4967 p = 1) : d2087 p ≤ (0 : Int) + d1639 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2087, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15389 p hg
    simpa only [d2087, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2087, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15579 p hg
    simpa only [d2087, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15581 (p : Pattern) (guard : d4967 p = 1) : d2088 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2088, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15425 p hg
    simpa only [d2088, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2088, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2088, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15582 (p : Pattern) (guard : d4967 p = 1) : d2089 p ≤ (0 : Int) + d1640 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2089, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15450 p hg
    simpa only [d2089, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2089, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15581 p hg
    simpa only [d2089, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15583 (p : Pattern) (guard : d4967 p = 1) : d2090 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2090, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15581 p hg
    simpa only [d2090, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2090, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2090, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15584 (p : Pattern) (guard : d4967 p = 1) : d2091 p ≤ (0 : Int) + d1641 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2091, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15582 p hg
    simpa only [d2091, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2091, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15583 p hg
    simpa only [d2091, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15585 (p : Pattern) (guard : d4967 p = 1) : d2092 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2092, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d2092, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2092, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2092, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15586 (p : Pattern) (guard : d4967 p = 1) : d2093 p ≤ (0 : Int) + d1642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2093, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15457 p hg
    simpa only [d2093, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2093, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d2093, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15587 (p : Pattern) (guard : d4967 p = 1) : d2094 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2094, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d2094, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2094, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2094, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15588 (p : Pattern) (guard : d4967 p = 1) : d2095 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2095, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15586 p hg
    simpa only [d2095, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2095, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15587 p hg
    simpa only [d2095, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15589 (p : Pattern) (guard : d4967 p = 1) : d2096 p ≤ (0 : Int) + d1644 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2096, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15584 p hg
    simpa only [d2096, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2096, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15588 p hg
    simpa only [d2096, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15590 (p : Pattern) (guard : d4967 p = 1) : d2097 p ≤ (0 : Int) + d1645 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2097, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15443 p hg
    simpa only [d2097, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2097, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15589 p hg
    simpa only [d2097, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15591 (p : Pattern) (guard : d4967 p = 1) : d2098 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2098, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d2098, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2098, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2098, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15592 (p : Pattern) (guard : d4967 p = 1) : d2099 p ≤ (0 : Int) + d1642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2099, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15484 p hg
    simpa only [d2099, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2099, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15591 p hg
    simpa only [d2099, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15593 (p : Pattern) (guard : d4967 p = 1) : d2100 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2100, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15591 p hg
    simpa only [d2100, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2100, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2100, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15594 (p : Pattern) (guard : d4967 p = 1) : d2101 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2101, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15592 p hg
    simpa only [d2101, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2101, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15593 p hg
    simpa only [d2101, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15595 (p : Pattern) (guard : d4967 p = 1) : d2102 p ≤ (0 : Int) + d1646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2102, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15594 p hg
    simpa only [d2102, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2102, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15492 p hg
    simpa only [d2102, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15596 (p : Pattern) (guard : d4967 p = 1) : d2103 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2103, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15483 p hg
    simpa only [d2103, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2103, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15595 p hg
    simpa only [d2103, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15597 (p : Pattern) (guard : d4967 p = 1) : d2104 p ≤ (0 : Int) + d1648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2104, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15590 p hg
    simpa only [d2104, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2104, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15596 p hg
    simpa only [d2104, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15598 (p : Pattern) (guard : d4967 p = 1) : d2105 p ≤ (0 : Int) + d1649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2105, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15596 p hg
    simpa only [d2105, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2105, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15499 p hg
    simpa only [d2105, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15599 (p : Pattern) (guard : d4967 p = 1) : d2106 p ≤ (0 : Int) + d1650 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2106, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15597 p hg
    simpa only [d2106, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2106, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15598 p hg
    simpa only [d2106, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15600 (p : Pattern) (guard : d0 p = 1) : d1943 p ≤ (0 : Int) + d343 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15601 (p : Pattern) (guard : d4967 p = 1) : d1944 p ≤ (0 : Int) + d1573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1944, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d1944, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1944, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15600 p hg
    simpa only [d4967, d1944, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15602 (p : Pattern) (guard : d4967 p = 1) : d1944 p ≤ (0 : Int) + d1601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15601 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15466 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15603 (p : Pattern) (guard : d0 p = 1) : d2109 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15604 (p : Pattern) (guard : d4967 p = 1) : d2110 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2110, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4967, d2110, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2110, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d4967, d2110, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15605 (p : Pattern) (guard : d4967 p = 1) : d2111 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2111, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15604 p hg
    simpa only [d2111, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2111, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d2111, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15606 (p : Pattern) (guard : d4967 p = 1) : d2112 p ≤ (0 : Int) + d1602 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2112, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15602 p hg
    simpa only [d2112, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2112, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15605 p hg
    simpa only [d2112, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15607 (p : Pattern) (guard : d4967 p = 1) : d2113 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2113, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15468 p hg
    simpa only [d2113, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2113, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d2113, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15608 (p : Pattern) (guard : d4967 p = 1) : d2114 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2114, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15607 p hg
    simpa only [d2114, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2114, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15428 p hg
    simpa only [d2114, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15609 (p : Pattern) (guard : d4967 p = 1) : d2115 p ≤ (0 : Int) + d1603 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2115, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15606 p hg
    simpa only [d2115, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2115, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15608 p hg
    simpa only [d2115, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15610 (p : Pattern) (guard : d4967 p = 1) : d2116 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2116, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2116, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2116, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d4967, d2116, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15611 (p : Pattern) (guard : d4967 p = 1) : d2117 p ≤ (0 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15610 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15612 (p : Pattern) (guard : d4967 p = 1) : d2118 p ≤ (0 : Int) + d1651 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2118, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15611 p hg
    simpa only [d2118, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2118, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15585 p hg
    simpa only [d2118, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15613 (p : Pattern) (guard : d4967 p = 1) : d2119 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2119, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d4967, d2119, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2119, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d2119, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15614 (p : Pattern) (guard : d4967 p = 1) : d2120 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2120, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15613 p hg
    simpa only [d2120, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2120, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2120, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15615 (p : Pattern) (guard : d4967 p = 1) : d2121 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2121, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15614 p hg
    simpa only [d2121, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2121, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2121, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15616 (p : Pattern) (guard : d4967 p = 1) : d2122 p ≤ (0 : Int) + d1652 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2122, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15612 p hg
    simpa only [d2122, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2122, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15615 p hg
    simpa only [d2122, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15617 (p : Pattern) (guard : d4967 p = 1) : d2123 p ≤ (0 : Int) + d1653 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2123, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15609 p hg
    simpa only [d2123, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2123, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15616 p hg
    simpa only [d2123, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15618 (p : Pattern) (guard : d0 p = 1) : d2126 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15619 (p : Pattern) (guard : d4967 p = 1) : d2127 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2127, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2127, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2127, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15618 p hg
    simpa only [d4967, d2127, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15620 (p : Pattern) (guard : d4967 p = 1) : d2128 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2128, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15604 p hg
    simpa only [d2128, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2128, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15619 p hg
    simpa only [d2128, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15621 (p : Pattern) (guard : d0 p = 1) : d2131 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15622 (p : Pattern) (guard : d4967 p = 1) : d2132 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2132, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2132, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2132, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15621 p hg
    simpa only [d4967, d2132, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15623 (p : Pattern) (guard : d4967 p = 1) : d2133 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2133, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15622 p hg
    simpa only [d2133, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2133, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2133, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15624 (p : Pattern) (guard : d4967 p = 1) : d2134 p ≤ (0 : Int) + d1642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2134, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15620 p hg
    simpa only [d2134, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2134, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15623 p hg
    simpa only [d2134, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15625 (p : Pattern) (guard : d0 p = 1) : d2137 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15626 (p : Pattern) (guard : d4967 p = 1) : d2138 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2138, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2138, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2138, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15625 p hg
    simpa only [d4967, d2138, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15627 (p : Pattern) (guard : d4967 p = 1) : d2139 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2139, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15626 p hg
    simpa only [d2139, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2139, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2139, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15628 (p : Pattern) (guard : d4967 p = 1) : d2140 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2140, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15627 p hg
    simpa only [d2140, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2140, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2140, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15629 (p : Pattern) (guard : d4967 p = 1) : d2141 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2141, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15624 p hg
    simpa only [d2141, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2141, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15628 p hg
    simpa only [d2141, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15630 (p : Pattern) (guard : d4967 p = 1) : d2142 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2142, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4967, d2142, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2142, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d4967, d2142, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15631 (p : Pattern) (guard : d4967 p = 1) : d2143 p ≤ (0 : Int) + d125 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15630 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15437 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15632 (p : Pattern) (guard : d4967 p = 1) : d2144 p ≤ (0 : Int) + d1654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2144, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15631 p hg
    simpa only [d2144, d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2144, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15614 p hg
    simpa only [d2144, d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15633 (p : Pattern) (guard : d4967 p = 1) : d2145 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2145, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15294 p hg
    simpa only [d2145, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2145, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2145, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15634 (p : Pattern) (guard : d4967 p = 1) : d2146 p ≤ (0 : Int) + d1655 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2146, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15632 p hg
    simpa only [d2146, d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2146, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15633 p hg
    simpa only [d2146, d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15635 (p : Pattern) (guard : d4967 p = 1) : d2147 p ≤ (0 : Int) + d1656 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2147, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15629 p hg
    simpa only [d2147, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2147, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15634 p hg
    simpa only [d2147, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15636 (p : Pattern) (guard : d4967 p = 1) : d2148 p ≤ (0 : Int) + d1657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2148, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15617 p hg
    simpa only [d2148, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2148, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15635 p hg
    simpa only [d2148, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15637 (p : Pattern) (guard : d4967 p = 1) : d2149 p ≤ (0 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15468 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15471 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15638 (p : Pattern) (guard : d4967 p = 1) : d2150 p ≤ (0 : Int) + d1658 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2150, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d2150, d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2150, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d2150, d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15639 (p : Pattern) (guard : d4967 p = 1) : d2151 p ≤ (0 : Int) + d1659 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2151, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15637 p hg
    simpa only [d2151, d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2151, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15638 p hg
    simpa only [d2151, d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15640 (p : Pattern) (guard : d4967 p = 1) : d2152 p ≤ (0 : Int) + d1660 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2152, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15639 p hg
    simpa only [d2152, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2152, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15488 p hg
    simpa only [d2152, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15641 (p : Pattern) (guard : d4967 p = 1) : d2153 p ≤ (0 : Int) + d1661 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2153, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15640 p hg
    simpa only [d2153, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2153, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15492 p hg
    simpa only [d2153, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15642 (p : Pattern) (guard : d0 p = 1) : d2158 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15643 (p : Pattern) (guard : d4967 p = 1) : d2159 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d2159, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4967, d2159, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d2159, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15642 p hg
    simpa only [d4967, d2159, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15644 (p : Pattern) (guard : d4967 p = 1) : d2160 p ≤ (0 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15643 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15645 (p : Pattern) (guard : d4967 p = 1) : d2161 p ≤ (0 : Int) + d1651 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2161, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15644 p hg
    simpa only [d2161, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2161, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15591 p hg
    simpa only [d2161, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15646 (p : Pattern) (guard : d4967 p = 1) : d2162 p ≤ (0 : Int) + d1652 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2162, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15645 p hg
    simpa only [d2162, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2162, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15491 p hg
    simpa only [d2162, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15647 (p : Pattern) (guard : d4967 p = 1) : d2163 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2163, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15339 p hg
    simpa only [d2163, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2163, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2163, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15648 (p : Pattern) (guard : d4967 p = 1) : d2164 p ≤ (0 : Int) + d1662 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2164, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15647 p hg
    simpa only [d2164, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2164, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2164, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15649 (p : Pattern) (guard : d4967 p = 1) : d2165 p ≤ (0 : Int) + d1663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2165, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15646 p hg
    simpa only [d2165, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2165, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15648 p hg
    simpa only [d2165, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15650 (p : Pattern) (guard : d4967 p = 1) : d2166 p ≤ (0 : Int) + d1664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2166, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15641 p hg
    simpa only [d2166, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2166, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15649 p hg
    simpa only [d2166, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15651 (p : Pattern) (guard : d4967 p = 1) : d2167 p ≤ (0 : Int) + d1665 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2167, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15636 p hg
    simpa only [d2167, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2167, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15650 p hg
    simpa only [d2167, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15652 (p : Pattern) (guard : d4967 p = 1) : d2168 p ≤ (0 : Int) + d1666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2168, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15478 p hg
    simpa only [d2168, d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2168, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d2168, d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15653 (p : Pattern) (guard : d4967 p = 1) : d2169 p ≤ (0 : Int) + d1667 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2169, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15637 p hg
    simpa only [d2169, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2169, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15652 p hg
    simpa only [d2169, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15654 (p : Pattern) (guard : d4967 p = 1) : d2170 p ≤ (0 : Int) + d1668 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2170, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15473 p hg
    simpa only [d2170, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2170, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15338 p hg
    simpa only [d2170, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15655 (p : Pattern) (guard : d4967 p = 1) : d2171 p ≤ (0 : Int) + d1669 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2171, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15654 p hg
    simpa only [d2171, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2171, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2171, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15656 (p : Pattern) (guard : d4967 p = 1) : d2172 p ≤ (0 : Int) + d1670 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2172, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15653 p hg
    simpa only [d2172, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2172, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15655 p hg
    simpa only [d2172, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15657 (p : Pattern) (guard : d4967 p = 1) : d2173 p ≤ (0 : Int) + d1671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2173, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15479 p hg
    simpa only [d2173, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2173, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15310 p hg
    simpa only [d2173, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15658 (p : Pattern) (guard : d4967 p = 1) : d2174 p ≤ (0 : Int) + d1672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2174, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15657 p hg
    simpa only [d2174, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2174, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2174, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15659 (p : Pattern) (guard : d4967 p = 1) : d2175 p ≤ (0 : Int) + d1673 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2175, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15658 p hg
    simpa only [d2175, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2175, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2175, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15660 (p : Pattern) (guard : d4967 p = 1) : d2176 p ≤ (0 : Int) + d1674 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2176, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15656 p hg
    simpa only [d2176, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2176, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15659 p hg
    simpa only [d2176, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15661 (p : Pattern) (guard : d4967 p = 1) : d2177 p ≤ (0 : Int) + d1675 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2177, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15660 p hg
    simpa only [d2177, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2177, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15649 p hg
    simpa only [d2177, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15662 (p : Pattern) (guard : d4967 p = 1) : d2178 p ≤ (0 : Int) + d1676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2178, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15661 p hg
    simpa only [d2178, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2178, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d2178, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15663 (p : Pattern) (guard : d4967 p = 1) : d2179 p ≤ (0 : Int) + d1677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2179, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15651 p hg
    simpa only [d2179, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2179, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15662 p hg
    simpa only [d2179, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15664 (p : Pattern) (guard : d4967 p = 1) : d2180 p ≤ (0 : Int) + d1678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2180, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15599 p hg
    simpa only [d2180, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2180, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15663 p hg
    simpa only [d2180, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15665 (p : Pattern) (guard : d4967 p = 1) : d2181 p ≤ (0 : Int) + d1679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2181, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15389 p hg
    simpa only [d2181, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2181, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15664 p hg
    simpa only [d2181, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15666 (p : Pattern) (guard : d4967 p = 1) : d2182 p ≤ (0 : Int) + d1680 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2182, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15580 p hg
    simpa only [d2182, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2182, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15665 p hg
    simpa only [d2182, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15667 (p : Pattern) (guard : d4967 p = 1) : d2183 p ≤ (0 : Int) + d1681 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2183, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15516 p hg
    simpa only [d2183, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2183, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15666 p hg
    simpa only [d2183, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15668 (p : Pattern) (guard : d0 p = 1) : d1682 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15669 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare15670 (p : Pattern) (guard : d1 p = 1) : d1683 p ≤ (2 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15671 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (2 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15670 p hg
    simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4690 p hg
    simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15672 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (2 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15671 p hg
    simpa only [d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15673 (p : Pattern) (guard : d1 p = 1) : d1686 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15672 p hg
    simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15671 p hg
    simpa only [d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15674 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15675 (p : Pattern) (guard : d4474 p = 1) : d1687 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15673 p hg
    simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15674 p hg
    simpa only [d4474, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15676 (p : Pattern) (guard : d4475 p = 1) : d1688 p ≤ (2 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15668 p hg
    simpa only [d4475, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d4475, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15677 (p : Pattern) (guard : d0 p = 1) : d1689 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15678 (p : Pattern) (guard : d4475 p = 1) : d1690 p ≤ (2 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15677 p hg
    simpa only [d4475, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d4475, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15679 (p : Pattern) (guard : d4475 p = 1) : d1691 p ≤ (2 : Int) + d14 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15676 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15678 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
