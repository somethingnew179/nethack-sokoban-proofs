/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12600 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d2050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12599 p hg
    simpa only [d4967, d46, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12601 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2055 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12602 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d2056 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12601 p hg
    simpa only [d4967, d46, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12603 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d2057 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12600 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12602 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12604 (p : Pattern) (guard : d4967 p = 1) : d1620 p ≤ (0 : Int) + d2058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1620, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12603 p hg
    simpa only [d1620, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1620, d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12414 p hg
    simpa only [d1620, d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12605 (p : Pattern) (guard : d4967 p = 1) : d1621 p ≤ (0 : Int) + d2059 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1621, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12604 p hg
    simpa only [d1621, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1621, d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12415 p hg
    simpa only [d1621, d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12606 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2062 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12607 (p : Pattern) (guard : d4967 p = 1) : d1622 p ≤ (0 : Int) + d2063 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1622, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11751 p hg
    simpa only [d4967, d1622, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1622, d2063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12606 p hg
    simpa only [d4967, d1622, d2063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12608 (p : Pattern) (guard : d4967 p = 1) : d1623 p ≤ (0 : Int) + d2064 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1623, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d1623, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1623, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12607 p hg
    simpa only [d1623, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12609 (p : Pattern) (guard : d4967 p = 1) : d1624 p ≤ (0 : Int) + d2065 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1624, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12608 p hg
    simpa only [d1624, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1624, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1624, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12610 (p : Pattern) (guard : d4967 p = 1) : d1625 p ≤ (0 : Int) + d2066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1625, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12609 p hg
    simpa only [d1625, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1625, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1625, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12611 (p : Pattern) (guard : d4967 p = 1) : d1626 p ≤ (0 : Int) + d2067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1626, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12605 p hg
    simpa only [d1626, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1626, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12610 p hg
    simpa only [d1626, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12612 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2072 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12613 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2073 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12612 p hg
    simpa only [d4967, d66, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12614 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d2074 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12613 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12615 (p : Pattern) (guard : d4967 p = 1) : d1627 p ≤ (0 : Int) + d2075 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1627, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d1627, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1627, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d1627, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12616 (p : Pattern) (guard : d4967 p = 1) : d1628 p ≤ (0 : Int) + d2076 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1628, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12614 p hg
    simpa only [d1628, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1628, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12615 p hg
    simpa only [d1628, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12617 (p : Pattern) (guard : d4967 p = 1) : d1629 p ≤ (0 : Int) + d2077 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1629, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12616 p hg
    simpa only [d1629, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1629, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12425 p hg
    simpa only [d1629, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12618 (p : Pattern) (guard : d4967 p = 1) : d1630 p ≤ (0 : Int) + d2078 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1630, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12607 p hg
    simpa only [d1630, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1630, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1630, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12619 (p : Pattern) (guard : d4967 p = 1) : d1631 p ≤ (0 : Int) + d2079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1631, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12618 p hg
    simpa only [d1631, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1631, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1631, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12620 (p : Pattern) (guard : d4967 p = 1) : d1632 p ≤ (0 : Int) + d2080 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1632, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12619 p hg
    simpa only [d1632, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1632, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1632, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12621 (p : Pattern) (guard : d4967 p = 1) : d1633 p ≤ (0 : Int) + d2081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1633, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12617 p hg
    simpa only [d1633, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1633, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12620 p hg
    simpa only [d1633, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12622 (p : Pattern) (guard : d4967 p = 1) : d1634 p ≤ (0 : Int) + d2082 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1634, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12611 p hg
    simpa only [d1634, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1634, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12621 p hg
    simpa only [d1634, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12623 (p : Pattern) (guard : d4967 p = 1) : d1635 p ≤ (0 : Int) + d2083 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1635, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12598 p hg
    simpa only [d1635, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1635, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12622 p hg
    simpa only [d1635, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12624 (p : Pattern) (guard : d4967 p = 1) : d1636 p ≤ (0 : Int) + d2084 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1636, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12622 p hg
    simpa only [d1636, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1636, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1636, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12625 (p : Pattern) (guard : d4967 p = 1) : d1637 p ≤ (0 : Int) + d2085 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1637, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12623 p hg
    simpa only [d1637, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1637, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12624 p hg
    simpa only [d1637, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12626 (p : Pattern) (guard : d4967 p = 1) : d1638 p ≤ (0 : Int) + d2086 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1638, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12473 p hg
    simpa only [d1638, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1638, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12625 p hg
    simpa only [d1638, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12627 (p : Pattern) (guard : d4967 p = 1) : d1639 p ≤ (0 : Int) + d2087 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1639, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d1639, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1639, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12626 p hg
    simpa only [d1639, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12628 (p : Pattern) (guard : d4967 p = 1) : d215 p ≤ (0 : Int) + d2088 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d215, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12491 p hg
    simpa only [d215, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d215, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d215, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12629 (p : Pattern) (guard : d4967 p = 1) : d1640 p ≤ (0 : Int) + d2089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1640, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12509 p hg
    simpa only [d1640, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1640, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12628 p hg
    simpa only [d1640, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12630 (p : Pattern) (guard : d4967 p = 1) : d217 p ≤ (0 : Int) + d2090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d217, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12628 p hg
    simpa only [d217, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d217, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d217, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12631 (p : Pattern) (guard : d4967 p = 1) : d1641 p ≤ (0 : Int) + d2091 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1641, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12629 p hg
    simpa only [d1641, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1641, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12630 p hg
    simpa only [d1641, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12632 (p : Pattern) (guard : d4967 p = 1) : d1642 p ≤ (0 : Int) + d2093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12515 p hg
    simpa only [d1642, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d1642, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12633 (p : Pattern) (guard : d4967 p = 1) : d1643 p ≤ (0 : Int) + d2095 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12632 p hg
    simpa only [d1643, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11780 p hg
    simpa only [d1643, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12634 (p : Pattern) (guard : d4967 p = 1) : d1644 p ≤ (0 : Int) + d2096 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1644, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12631 p hg
    simpa only [d1644, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1644, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12633 p hg
    simpa only [d1644, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12635 (p : Pattern) (guard : d4967 p = 1) : d1645 p ≤ (0 : Int) + d2097 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1645, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12504 p hg
    simpa only [d1645, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1645, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12634 p hg
    simpa only [d1645, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12636 (p : Pattern) (guard : d4967 p = 1) : d215 p ≤ (0 : Int) + d2098 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d215, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d215, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d215, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d215, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12637 (p : Pattern) (guard : d4967 p = 1) : d1642 p ≤ (0 : Int) + d2099 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12539 p hg
    simpa only [d1642, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12636 p hg
    simpa only [d1642, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12638 (p : Pattern) (guard : d4967 p = 1) : d217 p ≤ (0 : Int) + d2100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d217, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12636 p hg
    simpa only [d217, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d217, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d217, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12639 (p : Pattern) (guard : d4967 p = 1) : d1643 p ≤ (0 : Int) + d2101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12637 p hg
    simpa only [d1643, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12638 p hg
    simpa only [d1643, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12640 (p : Pattern) (guard : d4967 p = 1) : d1646 p ≤ (0 : Int) + d2102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1646, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12639 p hg
    simpa only [d1646, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1646, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12547 p hg
    simpa only [d1646, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12641 (p : Pattern) (guard : d4967 p = 1) : d1647 p ≤ (0 : Int) + d2103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1647, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12538 p hg
    simpa only [d1647, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1647, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12640 p hg
    simpa only [d1647, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12642 (p : Pattern) (guard : d4967 p = 1) : d1648 p ≤ (0 : Int) + d2104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1648, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12635 p hg
    simpa only [d1648, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1648, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12641 p hg
    simpa only [d1648, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12643 (p : Pattern) (guard : d4967 p = 1) : d1649 p ≤ (0 : Int) + d2105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1649, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12641 p hg
    simpa only [d1649, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1649, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12554 p hg
    simpa only [d1649, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12644 (p : Pattern) (guard : d4967 p = 1) : d1650 p ≤ (0 : Int) + d2106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1650, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12642 p hg
    simpa only [d1650, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1650, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12643 p hg
    simpa only [d1650, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12645 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1943 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12646 (p : Pattern) (guard : d4967 p = 1) : d1573 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1573, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d1573, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1573, d1944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12645 p hg
    simpa only [d4967, d1573, d1944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12647 (p : Pattern) (guard : d4967 p = 1) : d1601 p ≤ (0 : Int) + d1944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12646 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12521 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12648 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12649 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d2110 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d124, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d124, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d124, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12648 p hg
    simpa only [d4967, d124, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12650 (p : Pattern) (guard : d4967 p = 1) : d126 p ≤ (0 : Int) + d2111 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d126, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12649 p hg
    simpa only [d126, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d126, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d126, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12651 (p : Pattern) (guard : d4967 p = 1) : d1602 p ≤ (0 : Int) + d2112 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1602, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12647 p hg
    simpa only [d1602, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1602, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12650 p hg
    simpa only [d1602, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12652 (p : Pattern) (guard : d4967 p = 1) : d126 p ≤ (0 : Int) + d2113 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d126, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12523 p hg
    simpa only [d126, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d126, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d126, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12653 (p : Pattern) (guard : d4967 p = 1) : d129 p ≤ (0 : Int) + d2114 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d129, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12652 p hg
    simpa only [d129, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d129, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d129, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12654 (p : Pattern) (guard : d4967 p = 1) : d1603 p ≤ (0 : Int) + d2115 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1603, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12651 p hg
    simpa only [d1603, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1603, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12653 p hg
    simpa only [d1603, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12655 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d2116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12499 p hg
    simpa only [d4967, d139, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12656 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d2117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12655 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12657 (p : Pattern) (guard : d4967 p = 1) : d1651 p ≤ (0 : Int) + d2118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1651, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12656 p hg
    simpa only [d1651, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1651, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d1651, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12658 (p : Pattern) (guard : d4967 p = 1) : d1652 p ≤ (0 : Int) + d2122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1652, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12657 p hg
    simpa only [d1652, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1652, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11805 p hg
    simpa only [d1652, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12659 (p : Pattern) (guard : d4967 p = 1) : d1653 p ≤ (0 : Int) + d2123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1653, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12654 p hg
    simpa only [d1653, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1653, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12658 p hg
    simpa only [d1653, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12660 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12661 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d2127 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12660 p hg
    simpa only [d4967, d139, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12662 (p : Pattern) (guard : d4967 p = 1) : d1584 p ≤ (0 : Int) + d2128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1584, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12649 p hg
    simpa only [d1584, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1584, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12661 p hg
    simpa only [d1584, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12663 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12664 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d2132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12663 p hg
    simpa only [d4967, d125, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12665 (p : Pattern) (guard : d4967 p = 1) : d215 p ≤ (0 : Int) + d2133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d215, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12664 p hg
    simpa only [d215, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d215, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d215, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12666 (p : Pattern) (guard : d4967 p = 1) : d1642 p ≤ (0 : Int) + d2134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12662 p hg
    simpa only [d1642, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1642, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12665 p hg
    simpa only [d1642, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12667 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12668 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d2138 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12667 p hg
    simpa only [d4967, d125, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12669 (p : Pattern) (guard : d4967 p = 1) : d215 p ≤ (0 : Int) + d2139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d215, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12668 p hg
    simpa only [d215, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d215, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d215, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12670 (p : Pattern) (guard : d4967 p = 1) : d217 p ≤ (0 : Int) + d2140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d217, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12669 p hg
    simpa only [d217, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d217, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d217, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12671 (p : Pattern) (guard : d4967 p = 1) : d1643 p ≤ (0 : Int) + d2141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12666 p hg
    simpa only [d1643, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1643, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12670 p hg
    simpa only [d1643, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12672 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d2142 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d125, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d125, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d125, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12499 p hg
    simpa only [d4967, d125, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12673 (p : Pattern) (guard : d4967 p = 1) : d125 p ≤ (0 : Int) + d2143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12672 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12674 (p : Pattern) (guard : d4967 p = 1) : d1654 p ≤ (0 : Int) + d2144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1654, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12673 p hg
    simpa only [d1654, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1654, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11804 p hg
    simpa only [d1654, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12675 (p : Pattern) (guard : d4967 p = 1) : d1655 p ≤ (0 : Int) + d2146 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1655, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12674 p hg
    simpa only [d1655, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1655, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11823 p hg
    simpa only [d1655, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12676 (p : Pattern) (guard : d4967 p = 1) : d1656 p ≤ (0 : Int) + d2147 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1656, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12671 p hg
    simpa only [d1656, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1656, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12675 p hg
    simpa only [d1656, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12677 (p : Pattern) (guard : d4967 p = 1) : d1657 p ≤ (0 : Int) + d2148 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1657, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12659 p hg
    simpa only [d1657, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1657, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12676 p hg
    simpa only [d1657, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12678 (p : Pattern) (guard : d4967 p = 1) : d124 p ≤ (0 : Int) + d2149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12523 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12526 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12679 (p : Pattern) (guard : d4967 p = 1) : d1658 p ≤ (0 : Int) + d2150 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1658, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d1658, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1658, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d1658, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12680 (p : Pattern) (guard : d4967 p = 1) : d1659 p ≤ (0 : Int) + d2151 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1659, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12678 p hg
    simpa only [d1659, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1659, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12679 p hg
    simpa only [d1659, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12681 (p : Pattern) (guard : d4967 p = 1) : d1660 p ≤ (0 : Int) + d2152 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1660, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12680 p hg
    simpa only [d1660, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1660, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12543 p hg
    simpa only [d1660, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12682 (p : Pattern) (guard : d4967 p = 1) : d1661 p ≤ (0 : Int) + d2153 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1661, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12681 p hg
    simpa only [d1661, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1661, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12547 p hg
    simpa only [d1661, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12683 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12684 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d2159 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d139, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d139, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d139, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12683 p hg
    simpa only [d4967, d139, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12685 (p : Pattern) (guard : d4967 p = 1) : d139 p ≤ (0 : Int) + d2160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12684 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12686 (p : Pattern) (guard : d4967 p = 1) : d1651 p ≤ (0 : Int) + d2161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1651, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12685 p hg
    simpa only [d1651, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1651, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12636 p hg
    simpa only [d1651, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12687 (p : Pattern) (guard : d4967 p = 1) : d1652 p ≤ (0 : Int) + d2162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1652, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12686 p hg
    simpa only [d1652, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1652, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12546 p hg
    simpa only [d1652, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12688 (p : Pattern) (guard : d4967 p = 1) : d237 p ≤ (0 : Int) + d2163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d237, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12409 p hg
    simpa only [d237, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d237, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d237, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12689 (p : Pattern) (guard : d4967 p = 1) : d1662 p ≤ (0 : Int) + d2164 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1662, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12688 p hg
    simpa only [d1662, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1662, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1662, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12690 (p : Pattern) (guard : d4967 p = 1) : d1663 p ≤ (0 : Int) + d2165 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1663, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12687 p hg
    simpa only [d1663, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1663, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12689 p hg
    simpa only [d1663, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12691 (p : Pattern) (guard : d4967 p = 1) : d1664 p ≤ (0 : Int) + d2166 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1664, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12682 p hg
    simpa only [d1664, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1664, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12690 p hg
    simpa only [d1664, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12692 (p : Pattern) (guard : d4967 p = 1) : d1665 p ≤ (0 : Int) + d2167 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1665, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12677 p hg
    simpa only [d1665, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1665, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12691 p hg
    simpa only [d1665, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12693 (p : Pattern) (guard : d4967 p = 1) : d1666 p ≤ (0 : Int) + d2168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1666, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12533 p hg
    simpa only [d1666, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1666, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d1666, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12694 (p : Pattern) (guard : d4967 p = 1) : d1667 p ≤ (0 : Int) + d2169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1667, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12678 p hg
    simpa only [d1667, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1667, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12693 p hg
    simpa only [d1667, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12695 (p : Pattern) (guard : d4967 p = 1) : d1668 p ≤ (0 : Int) + d2170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1668, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12528 p hg
    simpa only [d1668, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1668, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d1668, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12696 (p : Pattern) (guard : d4967 p = 1) : d1669 p ≤ (0 : Int) + d2171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1669, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12695 p hg
    simpa only [d1669, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1669, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1669, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12697 (p : Pattern) (guard : d4967 p = 1) : d1670 p ≤ (0 : Int) + d2172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1670, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12694 p hg
    simpa only [d1670, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1670, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12696 p hg
    simpa only [d1670, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12698 (p : Pattern) (guard : d4967 p = 1) : d1671 p ≤ (0 : Int) + d2173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1671, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12534 p hg
    simpa only [d1671, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1671, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d1671, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12699 (p : Pattern) (guard : d4967 p = 1) : d1672 p ≤ (0 : Int) + d2174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1672, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12698 p hg
    simpa only [d1672, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1672, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1672, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12700 (p : Pattern) (guard : d4967 p = 1) : d1673 p ≤ (0 : Int) + d2175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1673, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12699 p hg
    simpa only [d1673, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1673, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1673, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12701 (p : Pattern) (guard : d4967 p = 1) : d1674 p ≤ (0 : Int) + d2176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1674, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12697 p hg
    simpa only [d1674, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1674, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12700 p hg
    simpa only [d1674, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12702 (p : Pattern) (guard : d4967 p = 1) : d1675 p ≤ (0 : Int) + d2177 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1675, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12701 p hg
    simpa only [d1675, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1675, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12690 p hg
    simpa only [d1675, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12703 (p : Pattern) (guard : d4967 p = 1) : d1676 p ≤ (0 : Int) + d2178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1676, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12702 p hg
    simpa only [d1676, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1676, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1676, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12704 (p : Pattern) (guard : d4967 p = 1) : d1677 p ≤ (0 : Int) + d2179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1677, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12692 p hg
    simpa only [d1677, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1677, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12703 p hg
    simpa only [d1677, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12705 (p : Pattern) (guard : d4967 p = 1) : d1678 p ≤ (0 : Int) + d2180 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1678, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12644 p hg
    simpa only [d1678, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1678, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12704 p hg
    simpa only [d1678, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12706 (p : Pattern) (guard : d4967 p = 1) : d1679 p ≤ (0 : Int) + d2181 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1679, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d1679, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1679, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12705 p hg
    simpa only [d1679, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12707 (p : Pattern) (guard : d4967 p = 1) : d1680 p ≤ (0 : Int) + d2182 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1680, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12627 p hg
    simpa only [d1680, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1680, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12706 p hg
    simpa only [d1680, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12708 (p : Pattern) (guard : d4967 p = 1) : d1681 p ≤ (0 : Int) + d2183 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1681, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12571 p hg
    simpa only [d1681, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1681, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12707 p hg
    simpa only [d1681, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12709 (p : Pattern) (guard : d4473 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  omega
theorem compare12710 (p : Pattern) (guard : d0 p = 1) : d324 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12711 (p : Pattern) (guard : d4985 p = 1) : d1504 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1504, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1504, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1504, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12710 p hg
    simpa only [d4985, d1504, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12712 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12713 (p : Pattern) (guard : d4985 p = 1) : d1505 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1505, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1505, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1505, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12712 p hg
    simpa only [d4985, d1505, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12714 (p : Pattern) (guard : d4985 p = 1) : d1506 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12711 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12713 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12715 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12716 (p : Pattern) (guard : d4985 p = 1) : d1507 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1507, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1507, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1507, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12715 p hg
    simpa only [d4985, d1507, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12717 (p : Pattern) (guard : d4473 p = 1) : d18 p ≤ (0 : Int) + d18 p := by
  omega
theorem compare12718 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12719 (p : Pattern) (guard : d4985 p = 1) : d43 p ≤ (0 : Int) + d4987 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d43, d4987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12717 p hg
    simpa only [d4985, d43, d4987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d43, d4987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12718 p hg
    simpa only [d4985, d43, d4987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12720 (p : Pattern) (guard : d4985 p = 1) : d1508 p ≤ (0 : Int) + d4988 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1508, d4988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12716 p hg
    simpa only [d1508, d4988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1508, d4988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12719 p hg
    simpa only [d1508, d4988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12721 (p : Pattern) (guard : d4985 p = 1) : d1509 p ≤ (0 : Int) + d4989 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1509, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12714 p hg
    simpa only [d1509, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1509, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12720 p hg
    simpa only [d1509, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12722 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12723 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12722 p hg
    simpa only [d4985, d46, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12724 (p : Pattern) (guard : d4985 p = 1) : d47 p ≤ (0 : Int) + d4988 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d47, d4988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12723 p hg
    simpa only [d47, d4988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d47, d4988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12719 p hg
    simpa only [d47, d4988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12725 (p : Pattern) (guard : d4473 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  omega
theorem compare12726 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12727 (p : Pattern) (guard : d4985 p = 1) : d48 p ≤ (0 : Int) + d4990 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d48, d4990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12725 p hg
    simpa only [d4985, d48, d4990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d48, d4990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12726 p hg
    simpa only [d4985, d48, d4990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12728 (p : Pattern) (guard : d4985 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare12729 (p : Pattern) (guard : d4985 p = 1) : d49 p ≤ (0 : Int) + d4991 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d49, d4991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12727 p hg
    simpa only [d49, d4991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d49, d4991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d49, d4991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12730 (p : Pattern) (guard : d4985 p = 1) : d50 p ≤ (0 : Int) + d4992 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d50, d4992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12724 p hg
    simpa only [d50, d4992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d50, d4992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12729 p hg
    simpa only [d50, d4992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12731 (p : Pattern) (guard : d4985 p = 1) : d1510 p ≤ (0 : Int) + d4993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1510, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12721 p hg
    simpa only [d1510, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1510, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12730 p hg
    simpa only [d1510, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12732 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12733 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d4994 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d4994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d4994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d4994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12732 p hg
    simpa only [d4985, d46, d4994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12734 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12735 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d4995 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d4995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d4995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d4995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12734 p hg
    simpa only [d4985, d46, d4995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12736 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d4996 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d4996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12733 p hg
    simpa only [d4996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d4996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12735 p hg
    simpa only [d4996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12737 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12738 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d4997 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d4997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d4997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d4997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12737 p hg
    simpa only [d4985, d46, d4997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12739 (p : Pattern) (guard : d4985 p = 1) : d43 p ≤ (0 : Int) + d43 p := by
  omega
end NetHack.Sokoban22Refined85
