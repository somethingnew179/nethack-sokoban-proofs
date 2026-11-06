/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11760 (p : Pattern) (guard : d4967 p = 1) : d53 p ≤ (0 : Int) + d2074 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11759 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d2074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11761 (p : Pattern) (guard : d4967 p = 1) : d198 p ≤ (0 : Int) + d2075 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d198, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d198, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d198, d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d198, d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11762 (p : Pattern) (guard : d4967 p = 1) : d199 p ≤ (0 : Int) + d2076 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d199, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11760 p hg
    simpa only [d199, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d199, d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11761 p hg
    simpa only [d199, d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11763 (p : Pattern) (guard : d4967 p = 1) : d200 p ≤ (0 : Int) + d2077 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d200, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11762 p hg
    simpa only [d200, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d200, d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11556 p hg
    simpa only [d200, d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11764 (p : Pattern) (guard : d4967 p = 1) : d201 p ≤ (0 : Int) + d2078 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d201, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11753 p hg
    simpa only [d201, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d201, d2078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d201, d2078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11765 (p : Pattern) (guard : d4967 p = 1) : d202 p ≤ (0 : Int) + d2079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d202, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11764 p hg
    simpa only [d202, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d202, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d202, d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11766 (p : Pattern) (guard : d4967 p = 1) : d203 p ≤ (0 : Int) + d2080 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d203, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11765 p hg
    simpa only [d203, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d203, d2080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d203, d2080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11767 (p : Pattern) (guard : d4967 p = 1) : d204 p ≤ (0 : Int) + d2081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d204, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11763 p hg
    simpa only [d204, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d204, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11766 p hg
    simpa only [d204, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11768 (p : Pattern) (guard : d4967 p = 1) : d205 p ≤ (0 : Int) + d2082 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d205, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11757 p hg
    simpa only [d205, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d205, d2082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11767 p hg
    simpa only [d205, d2082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11769 (p : Pattern) (guard : d4967 p = 1) : d206 p ≤ (0 : Int) + d2083 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d206, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11742 p hg
    simpa only [d206, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d206, d2083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11768 p hg
    simpa only [d206, d2083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11770 (p : Pattern) (guard : d4967 p = 1) : d207 p ≤ (0 : Int) + d2084 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d207, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11768 p hg
    simpa only [d207, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d207, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d207, d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11771 (p : Pattern) (guard : d4967 p = 1) : d208 p ≤ (0 : Int) + d2085 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d208, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11769 p hg
    simpa only [d208, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d208, d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11770 p hg
    simpa only [d208, d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11772 (p : Pattern) (guard : d4967 p = 1) : d209 p ≤ (0 : Int) + d2086 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d209, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11597 p hg
    simpa only [d209, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d209, d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11771 p hg
    simpa only [d209, d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11773 (p : Pattern) (guard : d4967 p = 1) : d210 p ≤ (0 : Int) + d2087 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d210, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d210, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d210, d2087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11772 p hg
    simpa only [d210, d2087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11774 (p : Pattern) (guard : d4967 p = 1) : d211 p ≤ (0 : Int) + d2088 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d211, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d211, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d211, d2088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d211, d2088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11775 (p : Pattern) (guard : d4967 p = 1) : d212 p ≤ (0 : Int) + d2089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d212, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11643 p hg
    simpa only [d212, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d212, d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11774 p hg
    simpa only [d212, d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11776 (p : Pattern) (guard : d4967 p = 1) : d213 p ≤ (0 : Int) + d2090 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d213, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11774 p hg
    simpa only [d213, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d213, d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d213, d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11777 (p : Pattern) (guard : d4967 p = 1) : d214 p ≤ (0 : Int) + d2091 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d214, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11775 p hg
    simpa only [d214, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d214, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11776 p hg
    simpa only [d214, d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11778 (p : Pattern) (guard : d4967 p = 1) : d215 p ≤ (0 : Int) + d2092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d215, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d215, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d215, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d215, d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11779 (p : Pattern) (guard : d4967 p = 1) : d216 p ≤ (0 : Int) + d2093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d216, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11650 p hg
    simpa only [d216, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d216, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d216, d2093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11780 (p : Pattern) (guard : d4967 p = 1) : d217 p ≤ (0 : Int) + d2094 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d217, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d217, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d217, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d217, d2094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11781 (p : Pattern) (guard : d4967 p = 1) : d218 p ≤ (0 : Int) + d2095 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d218, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11779 p hg
    simpa only [d218, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d218, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11780 p hg
    simpa only [d218, d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11782 (p : Pattern) (guard : d4967 p = 1) : d219 p ≤ (0 : Int) + d2096 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d219, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11777 p hg
    simpa only [d219, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d219, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11781 p hg
    simpa only [d219, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11783 (p : Pattern) (guard : d4967 p = 1) : d220 p ≤ (0 : Int) + d2097 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d220, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11635 p hg
    simpa only [d220, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d220, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11782 p hg
    simpa only [d220, d2097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11784 (p : Pattern) (guard : d4967 p = 1) : d211 p ≤ (0 : Int) + d2098 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d211, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d211, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d211, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d211, d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11785 (p : Pattern) (guard : d4967 p = 1) : d212 p ≤ (0 : Int) + d2099 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d212, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11679 p hg
    simpa only [d212, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d212, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11784 p hg
    simpa only [d212, d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11786 (p : Pattern) (guard : d4967 p = 1) : d213 p ≤ (0 : Int) + d2100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d213, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11784 p hg
    simpa only [d213, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d213, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d213, d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11787 (p : Pattern) (guard : d4967 p = 1) : d214 p ≤ (0 : Int) + d2101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d214, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11785 p hg
    simpa only [d214, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d214, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11786 p hg
    simpa only [d214, d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11788 (p : Pattern) (guard : d4967 p = 1) : d221 p ≤ (0 : Int) + d2102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d221, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11787 p hg
    simpa only [d221, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d221, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11687 p hg
    simpa only [d221, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11789 (p : Pattern) (guard : d4967 p = 1) : d222 p ≤ (0 : Int) + d2103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d222, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11678 p hg
    simpa only [d222, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d222, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11788 p hg
    simpa only [d222, d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11790 (p : Pattern) (guard : d4967 p = 1) : d223 p ≤ (0 : Int) + d2104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d223, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11783 p hg
    simpa only [d223, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d223, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11789 p hg
    simpa only [d223, d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11791 (p : Pattern) (guard : d4967 p = 1) : d224 p ≤ (0 : Int) + d2105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d224, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11789 p hg
    simpa only [d224, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d224, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11694 p hg
    simpa only [d224, d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11792 (p : Pattern) (guard : d4967 p = 1) : d225 p ≤ (0 : Int) + d2106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d225, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11790 p hg
    simpa only [d225, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d225, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11791 p hg
    simpa only [d225, d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11793 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d2109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11794 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d2110 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d105, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11793 p hg
    simpa only [d4967, d105, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11795 (p : Pattern) (guard : d4967 p = 1) : d110 p ≤ (0 : Int) + d2111 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d110, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11794 p hg
    simpa only [d110, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d110, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d110, d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11796 (p : Pattern) (guard : d4967 p = 1) : d111 p ≤ (0 : Int) + d2112 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d111, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11659 p hg
    simpa only [d111, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d111, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11795 p hg
    simpa only [d111, d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11797 (p : Pattern) (guard : d4967 p = 1) : d110 p ≤ (0 : Int) + d2113 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d110, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d110, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d110, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d110, d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11798 (p : Pattern) (guard : d4967 p = 1) : d113 p ≤ (0 : Int) + d2114 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d113, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11797 p hg
    simpa only [d113, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d113, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11620 p hg
    simpa only [d113, d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11799 (p : Pattern) (guard : d4967 p = 1) : d114 p ≤ (0 : Int) + d2115 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d114, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11796 p hg
    simpa only [d114, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d114, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11798 p hg
    simpa only [d114, d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11800 (p : Pattern) (guard : d4967 p = 1) : d226 p ≤ (0 : Int) + d2116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d226, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d226, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d226, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d4967, d226, d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11801 (p : Pattern) (guard : d4967 p = 1) : d227 p ≤ (0 : Int) + d2117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d227, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d227, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d227, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11800 p hg
    simpa only [d227, d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11802 (p : Pattern) (guard : d4967 p = 1) : d228 p ≤ (0 : Int) + d2118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d228, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11801 p hg
    simpa only [d228, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d228, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d228, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11803 (p : Pattern) (guard : d4967 p = 1) : d229 p ≤ (0 : Int) + d2119 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d229, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11673 p hg
    simpa only [d4967, d229, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d229, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d229, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11804 (p : Pattern) (guard : d4967 p = 1) : d230 p ≤ (0 : Int) + d2120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d230, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11803 p hg
    simpa only [d230, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d230, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d230, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11805 (p : Pattern) (guard : d4967 p = 1) : d231 p ≤ (0 : Int) + d2121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d231, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11804 p hg
    simpa only [d231, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d231, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d231, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11806 (p : Pattern) (guard : d4967 p = 1) : d232 p ≤ (0 : Int) + d2122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d232, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11802 p hg
    simpa only [d232, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d232, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11805 p hg
    simpa only [d232, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11807 (p : Pattern) (guard : d4967 p = 1) : d233 p ≤ (0 : Int) + d2123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d233, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11799 p hg
    simpa only [d233, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d233, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11806 p hg
    simpa only [d233, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11808 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d2126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11809 (p : Pattern) (guard : d4967 p = 1) : d132 p ≤ (0 : Int) + d2127 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d132, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d132, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d132, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11808 p hg
    simpa only [d4967, d132, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11810 (p : Pattern) (guard : d4967 p = 1) : d133 p ≤ (0 : Int) + d2128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d133, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11794 p hg
    simpa only [d133, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d133, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11809 p hg
    simpa only [d133, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11811 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d2131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11812 (p : Pattern) (guard : d4967 p = 1) : d109 p ≤ (0 : Int) + d2132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d109, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d109, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d109, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11811 p hg
    simpa only [d4967, d109, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11813 (p : Pattern) (guard : d4967 p = 1) : d211 p ≤ (0 : Int) + d2133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d211, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11812 p hg
    simpa only [d211, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d211, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d211, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11814 (p : Pattern) (guard : d4967 p = 1) : d212 p ≤ (0 : Int) + d2134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d212, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11810 p hg
    simpa only [d212, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d212, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11813 p hg
    simpa only [d212, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11815 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d2137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11816 (p : Pattern) (guard : d4967 p = 1) : d109 p ≤ (0 : Int) + d2138 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d109, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d109, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d109, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11815 p hg
    simpa only [d4967, d109, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11817 (p : Pattern) (guard : d4967 p = 1) : d211 p ≤ (0 : Int) + d2139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d211, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11816 p hg
    simpa only [d211, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d211, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d211, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11818 (p : Pattern) (guard : d4967 p = 1) : d213 p ≤ (0 : Int) + d2140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d213, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11817 p hg
    simpa only [d213, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d213, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d213, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11819 (p : Pattern) (guard : d4967 p = 1) : d214 p ≤ (0 : Int) + d2141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d214, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11814 p hg
    simpa only [d214, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d214, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11818 p hg
    simpa only [d214, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11820 (p : Pattern) (guard : d4967 p = 1) : d234 p ≤ (0 : Int) + d2142 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d234, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d234, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d234, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11625 p hg
    simpa only [d4967, d234, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11821 (p : Pattern) (guard : d4967 p = 1) : d235 p ≤ (0 : Int) + d2143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d235, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11820 p hg
    simpa only [d235, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d235, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11629 p hg
    simpa only [d235, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11822 (p : Pattern) (guard : d4967 p = 1) : d236 p ≤ (0 : Int) + d2144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d236, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11821 p hg
    simpa only [d236, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d236, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11804 p hg
    simpa only [d236, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11823 (p : Pattern) (guard : d4967 p = 1) : d237 p ≤ (0 : Int) + d2145 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d237, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d237, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d237, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d237, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11824 (p : Pattern) (guard : d4967 p = 1) : d238 p ≤ (0 : Int) + d2146 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d238, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11822 p hg
    simpa only [d238, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d238, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11823 p hg
    simpa only [d238, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11825 (p : Pattern) (guard : d4967 p = 1) : d239 p ≤ (0 : Int) + d2147 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d239, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11819 p hg
    simpa only [d239, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d239, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11824 p hg
    simpa only [d239, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11826 (p : Pattern) (guard : d4967 p = 1) : d240 p ≤ (0 : Int) + d2148 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d240, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11807 p hg
    simpa only [d240, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d240, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11825 p hg
    simpa only [d240, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11827 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d2149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11661 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11664 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11828 (p : Pattern) (guard : d4967 p = 1) : d241 p ≤ (0 : Int) + d2150 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d241, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d241, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d241, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d241, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11829 (p : Pattern) (guard : d4967 p = 1) : d242 p ≤ (0 : Int) + d2151 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d242, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11827 p hg
    simpa only [d242, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d242, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11828 p hg
    simpa only [d242, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11830 (p : Pattern) (guard : d4967 p = 1) : d243 p ≤ (0 : Int) + d2152 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d243, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11829 p hg
    simpa only [d243, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d243, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11683 p hg
    simpa only [d243, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11831 (p : Pattern) (guard : d4967 p = 1) : d244 p ≤ (0 : Int) + d2153 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d244, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11830 p hg
    simpa only [d244, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d244, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11687 p hg
    simpa only [d244, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11832 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d2158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11833 (p : Pattern) (guard : d4967 p = 1) : d132 p ≤ (0 : Int) + d2159 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d132, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11640 p hg
    simpa only [d4967, d132, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d132, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11832 p hg
    simpa only [d4967, d132, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11834 (p : Pattern) (guard : d4967 p = 1) : d132 p ≤ (0 : Int) + d2160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11833 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11835 (p : Pattern) (guard : d4967 p = 1) : d245 p ≤ (0 : Int) + d2161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d245, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11834 p hg
    simpa only [d245, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d245, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11784 p hg
    simpa only [d245, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11836 (p : Pattern) (guard : d4967 p = 1) : d246 p ≤ (0 : Int) + d2162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d246, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11835 p hg
    simpa only [d246, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d246, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11686 p hg
    simpa only [d246, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11837 (p : Pattern) (guard : d4967 p = 1) : d247 p ≤ (0 : Int) + d2163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d247, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d247, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d247, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d247, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11838 (p : Pattern) (guard : d4967 p = 1) : d248 p ≤ (0 : Int) + d2164 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d248, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11837 p hg
    simpa only [d248, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d248, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d248, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11839 (p : Pattern) (guard : d4967 p = 1) : d249 p ≤ (0 : Int) + d2165 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d249, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11836 p hg
    simpa only [d249, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d249, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11838 p hg
    simpa only [d249, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11840 (p : Pattern) (guard : d4967 p = 1) : d250 p ≤ (0 : Int) + d2166 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d250, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11831 p hg
    simpa only [d250, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d250, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11839 p hg
    simpa only [d250, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11841 (p : Pattern) (guard : d4967 p = 1) : d251 p ≤ (0 : Int) + d2167 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d251, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11826 p hg
    simpa only [d251, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d251, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11840 p hg
    simpa only [d251, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11842 (p : Pattern) (guard : d4967 p = 1) : d252 p ≤ (0 : Int) + d2168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d252, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11671 p hg
    simpa only [d252, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d252, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d252, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11843 (p : Pattern) (guard : d4967 p = 1) : d253 p ≤ (0 : Int) + d2169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d253, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11827 p hg
    simpa only [d253, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d253, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11842 p hg
    simpa only [d253, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11844 (p : Pattern) (guard : d4967 p = 1) : d254 p ≤ (0 : Int) + d2170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d254, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11666 p hg
    simpa only [d254, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d254, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d254, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11845 (p : Pattern) (guard : d4967 p = 1) : d255 p ≤ (0 : Int) + d2171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d255, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11844 p hg
    simpa only [d255, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d255, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d255, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11846 (p : Pattern) (guard : d4967 p = 1) : d256 p ≤ (0 : Int) + d2172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d256, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11843 p hg
    simpa only [d256, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d256, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11845 p hg
    simpa only [d256, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11847 (p : Pattern) (guard : d4967 p = 1) : d257 p ≤ (0 : Int) + d2173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d257, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11674 p hg
    simpa only [d257, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d257, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d257, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11848 (p : Pattern) (guard : d4967 p = 1) : d258 p ≤ (0 : Int) + d2174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d258, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11847 p hg
    simpa only [d258, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d258, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d258, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11849 (p : Pattern) (guard : d4967 p = 1) : d259 p ≤ (0 : Int) + d2175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d259, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11848 p hg
    simpa only [d259, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d259, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d259, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11850 (p : Pattern) (guard : d4967 p = 1) : d260 p ≤ (0 : Int) + d2176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d260, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11846 p hg
    simpa only [d260, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d260, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11849 p hg
    simpa only [d260, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11851 (p : Pattern) (guard : d4967 p = 1) : d261 p ≤ (0 : Int) + d2177 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d261, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11850 p hg
    simpa only [d261, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d261, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11839 p hg
    simpa only [d261, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11852 (p : Pattern) (guard : d4967 p = 1) : d262 p ≤ (0 : Int) + d2178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d262, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11851 p hg
    simpa only [d262, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d262, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d262, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11853 (p : Pattern) (guard : d4967 p = 1) : d263 p ≤ (0 : Int) + d2179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d263, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11841 p hg
    simpa only [d263, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d263, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11852 p hg
    simpa only [d263, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11854 (p : Pattern) (guard : d4967 p = 1) : d264 p ≤ (0 : Int) + d2180 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d264, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11792 p hg
    simpa only [d264, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d264, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11853 p hg
    simpa only [d264, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11855 (p : Pattern) (guard : d4967 p = 1) : d265 p ≤ (0 : Int) + d2181 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d265, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d265, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d265, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11854 p hg
    simpa only [d265, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11856 (p : Pattern) (guard : d4967 p = 1) : d266 p ≤ (0 : Int) + d2182 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d266, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11773 p hg
    simpa only [d266, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d266, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11855 p hg
    simpa only [d266, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11857 (p : Pattern) (guard : d4967 p = 1) : d267 p ≤ (0 : Int) + d2183 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d267, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11710 p hg
    simpa only [d267, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d267, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11856 p hg
    simpa only [d267, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11858 (p : Pattern) (guard : d0 p = 1) : d324 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11859 (p : Pattern) (guard : d4206 p = 1) : d1504 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11858 p hg
    simpa only [d4206, d1504, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11860 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11861 (p : Pattern) (guard : d4206 p = 1) : d1505 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11860 p hg
    simpa only [d4206, d1505, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11862 (p : Pattern) (guard : d4206 p = 1) : d1506 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11859 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11861 p hg
    simpa only [d1506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11863 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11864 (p : Pattern) (guard : d4206 p = 1) : d1507 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11863 p hg
    simpa only [d4206, d1507, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11865 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d4206, d43, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11866 (p : Pattern) (guard : d4206 p = 1) : d1508 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11864 p hg
    simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d1508, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11867 (p : Pattern) (guard : d4206 p = 1) : d1509 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11862 p hg
    simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11866 p hg
    simpa only [d1509, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11868 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d4206, d46, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11869 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d47, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11870 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d4206, d48, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11871 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d49, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11872 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11871 p hg
    simpa only [d50, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11873 (p : Pattern) (guard : d4206 p = 1) : d1510 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11867 p hg
    simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1510, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11874 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d376 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11875 (p : Pattern) (guard : d4471 p = 1) : d1513 p ≤ (0 : Int) + d710 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1513, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11873 p hg
    simpa only [d4471, d1513, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1513, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11874 p hg
    simpa only [d4471, d1513, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11876 (p : Pattern) (guard : d0 p = 1) : d359 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11877 (p : Pattern) (guard : d4206 p = 1) : d1514 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11876 p hg
    simpa only [d4206, d1514, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11878 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d4206, d66, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11879 (p : Pattern) (guard : d4206 p = 1) : d1515 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11877 p hg
    simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d1515, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11880 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d68, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11881 (p : Pattern) (guard : d4206 p = 1) : d1516 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11879 p hg
    simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11880 p hg
    simpa only [d1516, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11882 (p : Pattern) (guard : d4206 p = 1) : d70 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d4206, d70, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11883 (p : Pattern) (guard : d4206 p = 1) : d71 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11882 p hg
    simpa only [d71, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11884 (p : Pattern) (guard : d4206 p = 1) : d72 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d4206, d72, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11885 (p : Pattern) (guard : d4206 p = 1) : d73 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d73, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11886 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11883 p hg
    simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11885 p hg
    simpa only [d74, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11887 (p : Pattern) (guard : d4206 p = 1) : d1517 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11881 p hg
    simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11886 p hg
    simpa only [d1517, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11888 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (0 : Int) + d391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11889 (p : Pattern) (guard : d4471 p = 1) : d1521 p ≤ (0 : Int) + d711 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1521, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11887 p hg
    simpa only [d4471, d1521, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1521, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11888 p hg
    simpa only [d4471, d1521, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11890 (p : Pattern) (guard : d4471 p = 1) : d1522 p ≤ (0 : Int) + d712 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1522, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11875 p hg
    simpa only [d1522, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1522, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11889 p hg
    simpa only [d1522, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11891 (p : Pattern) (guard : d4206 p = 1) : d1511 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d1511, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11892 (p : Pattern) (guard : d4206 p = 1) : d1512 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1512, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11893 (p : Pattern) (guard : d0 p = 1) : d1523 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11894 (p : Pattern) (guard : d4471 p = 1) : d1524 p ≤ (0 : Int) + d713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1524, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11892 p hg
    simpa only [d4471, d1524, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1524, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11893 p hg
    simpa only [d4471, d1524, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11895 (p : Pattern) (guard : d4206 p = 1) : d1518 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d1518, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11896 (p : Pattern) (guard : d4206 p = 1) : d1519 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11895 p hg
    simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11880 p hg
    simpa only [d1519, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11897 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11896 p hg
    simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11886 p hg
    simpa only [d1520, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11898 (p : Pattern) (guard : d0 p = 1) : d1525 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11899 (p : Pattern) (guard : d4471 p = 1) : d1526 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1526, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d4471, d1526, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1526, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11898 p hg
    simpa only [d4471, d1526, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
