/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons120
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16940 (pattern : Twelve) (guard : d1848 pattern = 1) : d1645 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16939 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16941 (pattern : Twelve) (guard : d1848 pattern = 1) : d1647 pattern ≤ (0 : Int) + d3143 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11707 pattern childGuard
    simpa only [d1647, d3143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1647, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16940 pattern childGuard
    simpa only [d1647, d3143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16942 (pattern : Twelve) (guard : d1848 pattern = 1) : d1651 pattern ≤ (0 : Int) + d3144 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16873 pattern childGuard
    simpa only [d1651, d3144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1651, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16941 pattern childGuard
    simpa only [d1651, d3144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16943 (pattern : Twelve) (guard : d1848 pattern = 1) : d1657 pattern ≤ (0 : Int) + d3145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16942 pattern childGuard
    simpa only [d1657, d3145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1657, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16887 pattern childGuard
    simpa only [d1657, d3145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16944 (pattern : Twelve) (guard : d1848 pattern = 1) : d1660 pattern ≤ (0 : Int) + d3146 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4852 pattern childGuard
    simpa only [d1660, d3146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1660, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16943 pattern childGuard
    simpa only [d1660, d3146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16945 (pattern : Twelve) (guard : d1848 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11707 pattern childGuard
    simpa only [d1652, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16946 (pattern : Twelve) (guard : d1848 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11711 pattern childGuard
    simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1653, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16947 (pattern : Twelve) (guard : d1848 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16945 pattern childGuard
    simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16946 pattern childGuard
    simpa only [d1658, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16948 (pattern : Twelve) (guard : d1848 pattern = 1) : d1646 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11033 pattern childGuard
    simpa only [d1848, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16676 pattern childGuard
    simpa only [d1848, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16949 (pattern : Twelve) (guard : d1848 pattern = 1) : d1648 pattern ≤ (0 : Int) + d3074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16948 pattern childGuard
    simpa only [d1648, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1648, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16768 pattern childGuard
    simpa only [d1648, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16950 (pattern : Twelve) (guard : d1848 pattern = 1) : d1654 pattern ≤ (0 : Int) + d3147 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1654, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16886 pattern childGuard
    simpa only [d1654, d3147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1654, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16949 pattern childGuard
    simpa only [d1654, d3147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16951 (pattern : Twelve) (guard : d1848 pattern = 1) : d1655 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11719 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16952 (pattern : Twelve) (guard : d1848 pattern = 1) : d1659 pattern ≤ (0 : Int) + d3148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1659, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16950 pattern childGuard
    simpa only [d1659, d3148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1659, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16951 pattern childGuard
    simpa only [d1659, d3148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16953 (pattern : Twelve) (guard : d1848 pattern = 1) : d1661 pattern ≤ (0 : Int) + d3149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1661, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16947 pattern childGuard
    simpa only [d1661, d3149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1661, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16952 pattern childGuard
    simpa only [d1661, d3149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16954 (pattern : Twelve) (guard : d1848 pattern = 1) : d1662 pattern ≤ (0 : Int) + d3150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1662, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16943 pattern childGuard
    simpa only [d1662, d3150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1662, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1662, d3150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16955 (pattern : Twelve) (guard : d1848 pattern = 1) : d1663 pattern ≤ (0 : Int) + d3151 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1663, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16953 pattern childGuard
    simpa only [d1663, d3151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1663, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16954 pattern childGuard
    simpa only [d1663, d3151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16956 (pattern : Twelve) (guard : d1848 pattern = 1) : d1664 pattern ≤ (0 : Int) + d3152 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1664, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16944 pattern childGuard
    simpa only [d1664, d3152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1664, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16955 pattern childGuard
    simpa only [d1664, d3152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16957 (pattern : Twelve) (guard : d1848 pattern = 1) : d1668 pattern ≤ (0 : Int) + d3153 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d1668, d3153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1668, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11707 pattern childGuard
    simpa only [d1668, d3153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16958 (pattern : Twelve) (guard : d1848 pattern = 1) : d1671 pattern ≤ (0 : Int) + d3154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16957 pattern childGuard
    simpa only [d1671, d3154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1671, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4868 pattern childGuard
    simpa only [d1671, d3154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16959 (pattern : Twelve) (guard : d1848 pattern = 1) : d1674 pattern ≤ (0 : Int) + d3155 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16958 pattern childGuard
    simpa only [d1674, d3155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1674, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16943 pattern childGuard
    simpa only [d1674, d3155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16960 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16818 pattern childGuard
    simpa only [d1324, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15095 pattern childGuard
    simpa only [d1324, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16961 (pattern : Twelve) (guard : d1848 pattern = 1) : d1665 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16960 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16676 pattern childGuard
    simpa only [d1848, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16962 (pattern : Twelve) (guard : d1848 pattern = 1) : d1666 pattern ≤ (0 : Int) + d2410 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11707 pattern childGuard
    simpa only [d1666, d2410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1666, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16961 pattern childGuard
    simpa only [d1666, d2410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16963 (pattern : Twelve) (guard : d1848 pattern = 1) : d1669 pattern ≤ (0 : Int) + d2468 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1669, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1669, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16962 pattern childGuard
    simpa only [d1669, d2468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16964 (pattern : Twelve) (guard : d1848 pattern = 1) : d1672 pattern ≤ (0 : Int) + d2471 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16963 pattern childGuard
    simpa only [d1672, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1672, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16887 pattern childGuard
    simpa only [d1672, d2471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16965 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11038 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10876 pattern childGuard
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16966 (pattern : Twelve) (guard : d1848 pattern = 1) : d183 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16965 pattern childGuard
    simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16967 (pattern : Twelve) (guard : d1848 pattern = 1) : d1667 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16768 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16966 pattern childGuard
    simpa only [d1667, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16968 (pattern : Twelve) (guard : d1848 pattern = 1) : d1670 pattern ≤ (0 : Int) + d2470 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1670, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16886 pattern childGuard
    simpa only [d1670, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1670, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16967 pattern childGuard
    simpa only [d1670, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16969 (pattern : Twelve) (guard : d1848 pattern = 1) : d1252 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11719 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16970 (pattern : Twelve) (guard : d1848 pattern = 1) : d1626 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16969 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16971 (pattern : Twelve) (guard : d1848 pattern = 1) : d1673 pattern ≤ (0 : Int) + d3156 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1673, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16968 pattern childGuard
    simpa only [d1673, d3156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1673, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16970 pattern childGuard
    simpa only [d1673, d3156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16972 (pattern : Twelve) (guard : d1848 pattern = 1) : d1675 pattern ≤ (0 : Int) + d3157 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1675, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16964 pattern childGuard
    simpa only [d1675, d3157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1675, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16971 pattern childGuard
    simpa only [d1675, d3157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16973 (pattern : Twelve) (guard : d1848 pattern = 1) : d1676 pattern ≤ (0 : Int) + d3158 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1676, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16972 pattern childGuard
    simpa only [d1676, d3158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1676, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16954 pattern childGuard
    simpa only [d1676, d3158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16974 (pattern : Twelve) (guard : d1848 pattern = 1) : d1677 pattern ≤ (0 : Int) + d3159 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1677, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16959 pattern childGuard
    simpa only [d1677, d3159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1677, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16973 pattern childGuard
    simpa only [d1677, d3159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16975 (pattern : Twelve) (guard : d1848 pattern = 1) : d1678 pattern ≤ (0 : Int) + d3160 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1678, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16956 pattern childGuard
    simpa only [d1678, d3160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1678, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16974 pattern childGuard
    simpa only [d1678, d3160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16976 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12209 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16977 (pattern : Twelve) (guard : d1848 pattern = 1) : d184 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16976 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11051 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16978 (pattern : Twelve) (guard : d0 pattern = 1) : d161 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16979 (pattern : Twelve) (guard : d1848 pattern = 1) : d171 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16978 pattern childGuard
    simpa only [d1848, d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16980 (pattern : Twelve) (guard : d1848 pattern = 1) : d372 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16979 pattern childGuard
    simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11056 pattern childGuard
    simpa only [d372, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16981 (pattern : Twelve) (guard : d1848 pattern = 1) : d389 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16977 pattern childGuard
    simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16980 pattern childGuard
    simpa only [d389, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16982 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16983 (pattern : Twelve) (guard : d1848 pattern = 1) : d367 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16982 pattern childGuard
    simpa only [d1848, d367, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16984 (pattern : Twelve) (guard : d1848 pattern = 1) : d373 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11051 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16983 pattern childGuard
    simpa only [d373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16985 (pattern : Twelve) (guard : d0 pattern = 1) : d163 pattern ≤ (1 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16986 (pattern : Twelve) (guard : d1848 pattern = 1) : d366 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16985 pattern childGuard
    simpa only [d1848, d366, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16987 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (1 : Int) + d29 pattern := by
  omega
theorem c16988 (pattern : Twelve) (guard : d1848 pattern = 1) : d374 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16986 pattern childGuard
    simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16987 pattern childGuard
    simpa only [d374, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16989 (pattern : Twelve) (guard : d1848 pattern = 1) : d390 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16984 pattern childGuard
    simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16988 pattern childGuard
    simpa only [d390, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16990 (pattern : Twelve) (guard : d1848 pattern = 1) : d402 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16981 pattern childGuard
    simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16989 pattern childGuard
    simpa only [d402, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16991 (pattern : Twelve) (guard : d0 pattern = 1) : d165 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16992 (pattern : Twelve) (guard : d1848 pattern = 1) : d368 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16991 pattern childGuard
    simpa only [d1848, d368, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16993 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (1 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16994 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16993 pattern childGuard
    simpa only [d1848, d369, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16995 (pattern : Twelve) (guard : d1848 pattern = 1) : d375 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16992 pattern childGuard
    simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16994 pattern childGuard
    simpa only [d375, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16996 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11144 pattern childGuard
    simpa only [d1848, d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16997 (pattern : Twelve) (guard : d1848 pattern = 1) : d376 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11075 pattern childGuard
    simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16996 pattern childGuard
    simpa only [d376, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16998 (pattern : Twelve) (guard : d1848 pattern = 1) : d391 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16995 pattern childGuard
    simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16997 pattern childGuard
    simpa only [d391, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16999 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11366 pattern childGuard
    simpa only [d1848, d35, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17000 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11075 pattern childGuard
    simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16999 pattern childGuard
    simpa only [d377, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17001 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11079 pattern childGuard
    simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16987 pattern childGuard
    simpa only [d378, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17002 (pattern : Twelve) (guard : d1848 pattern = 1) : d392 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17000 pattern childGuard
    simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d392, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17003 (pattern : Twelve) (guard : d1848 pattern = 1) : d403 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16998 pattern childGuard
    simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17002 pattern childGuard
    simpa only [d403, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17004 (pattern : Twelve) (guard : d1848 pattern = 1) : d409 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16990 pattern childGuard
    simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17003 pattern childGuard
    simpa only [d409, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17005 (pattern : Twelve) (guard : d0 pattern = 1) : d165 pattern ≤ (1 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17006 (pattern : Twelve) (guard : d1848 pattern = 1) : d368 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17005 pattern childGuard
    simpa only [d1848, d368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17007 (pattern : Twelve) (guard : d1848 pattern = 1) : d375 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17006 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11091 pattern childGuard
    simpa only [d375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17008 (pattern : Twelve) (guard : d0 pattern = 1) : d167 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17009 (pattern : Twelve) (guard : d1848 pattern = 1) : d369 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17008 pattern childGuard
    simpa only [d1848, d369, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17010 (pattern : Twelve) (guard : d1848 pattern = 1) : d376 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17009 pattern childGuard
    simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11095 pattern childGuard
    simpa only [d376, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17011 (pattern : Twelve) (guard : d1848 pattern = 1) : d391 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17007 pattern childGuard
    simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17010 pattern childGuard
    simpa only [d391, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17012 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11091 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17013 (pattern : Twelve) (guard : d1848 pattern = 1) : d392 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17012 pattern childGuard
    simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d392, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17014 (pattern : Twelve) (guard : d1848 pattern = 1) : d403 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17011 pattern childGuard
    simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17013 pattern childGuard
    simpa only [d403, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17015 (pattern : Twelve) (guard : d0 pattern = 1) : d22 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17016 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17015 pattern childGuard
    simpa only [d1848, d33, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17017 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d35 pattern := by
  omega
theorem c17018 (pattern : Twelve) (guard : d1848 pattern = 1) : d379 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17016 pattern childGuard
    simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17017 pattern childGuard
    simpa only [d379, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17019 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d36 pattern := by
  omega
theorem c17020 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17019 pattern childGuard
    simpa only [d380, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17021 (pattern : Twelve) (guard : d1848 pattern = 1) : d393 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17018 pattern childGuard
    simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17020 pattern childGuard
    simpa only [d393, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17022 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17017 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17023 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d394, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17024 (pattern : Twelve) (guard : d1848 pattern = 1) : d404 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17021 pattern childGuard
    simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17023 pattern childGuard
    simpa only [d404, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17025 (pattern : Twelve) (guard : d1848 pattern = 1) : d410 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17014 pattern childGuard
    simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17024 pattern childGuard
    simpa only [d410, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17026 (pattern : Twelve) (guard : d1848 pattern = 1) : d415 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17004 pattern childGuard
    simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17025 pattern childGuard
    simpa only [d415, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17027 (pattern : Twelve) (guard : d0 pattern = 1) : d169 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17028 (pattern : Twelve) (guard : d1848 pattern = 1) : d370 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17027 pattern childGuard
    simpa only [d1848, d370, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17029 (pattern : Twelve) (guard : d1848 pattern = 1) : d381 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17028 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11118 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17030 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1848, d36, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17031 (pattern : Twelve) (guard : d1848 pattern = 1) : d382 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11118 pattern childGuard
    simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17030 pattern childGuard
    simpa only [d382, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17032 (pattern : Twelve) (guard : d1848 pattern = 1) : d395 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17029 pattern childGuard
    simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17031 pattern childGuard
    simpa only [d395, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17033 (pattern : Twelve) (guard : d1848 pattern = 1) : d383 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11118 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17034 (pattern : Twelve) (guard : d1848 pattern = 1) : d396 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17033 pattern childGuard
    simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d396, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17035 (pattern : Twelve) (guard : d1848 pattern = 1) : d405 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17032 pattern childGuard
    simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17034 pattern childGuard
    simpa only [d405, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17036 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d39 pattern := by
  omega
theorem c17037 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11129 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17036 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17038 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (1 : Int) + d40 pattern := by
  omega
theorem c17039 (pattern : Twelve) (guard : d1848 pattern = 1) : d384 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11129 pattern childGuard
    simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17038 pattern childGuard
    simpa only [d384, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17040 (pattern : Twelve) (guard : d1848 pattern = 1) : d397 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17037 pattern childGuard
    simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17039 pattern childGuard
    simpa only [d397, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17041 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (1 : Int) + d42 pattern := by
  omega
theorem c17042 (pattern : Twelve) (guard : d1848 pattern = 1) : d385 pattern ≤ (1 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11134 pattern childGuard
    simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17041 pattern childGuard
    simpa only [d385, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17043 (pattern : Twelve) (guard : d1848 pattern = 1) : d398 pattern ≤ (1 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17037 pattern childGuard
    simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17042 pattern childGuard
    simpa only [d398, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17044 (pattern : Twelve) (guard : d1848 pattern = 1) : d406 pattern ≤ (1 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17040 pattern childGuard
    simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17043 pattern childGuard
    simpa only [d406, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17045 (pattern : Twelve) (guard : d1848 pattern = 1) : d411 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17035 pattern childGuard
    simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17044 pattern childGuard
    simpa only [d411, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17046 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17022 pattern childGuard
    simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17020 pattern childGuard
    simpa only [d399, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17047 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17046 pattern childGuard
    simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17023 pattern childGuard
    simpa only [d407, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17048 (pattern : Twelve) (guard : d1848 pattern = 1) : d412 pattern ≤ (1 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17047 pattern childGuard
    simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11321 pattern childGuard
    simpa only [d412, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17049 (pattern : Twelve) (guard : d1848 pattern = 1) : d416 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17045 pattern childGuard
    simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17048 pattern childGuard
    simpa only [d416, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17050 (pattern : Twelve) (guard : d1848 pattern = 1) : d419 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17026 pattern childGuard
    simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17049 pattern childGuard
    simpa only [d419, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17051 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1848, d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17052 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17051 pattern childGuard
    simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11095 pattern childGuard
    simpa only [d380, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17053 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17052 pattern childGuard
    simpa only [d399, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17054 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17055 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17054 pattern childGuard
    simpa only [d1848, d36, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17056 (pattern : Twelve) (guard : d1848 pattern = 1) : d378 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17055 pattern childGuard
    simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16987 pattern childGuard
    simpa only [d378, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17057 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17056 pattern childGuard
    simpa only [d394, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17058 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17053 pattern childGuard
    simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17057 pattern childGuard
    simpa only [d407, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17059 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11348 pattern childGuard
    simpa only [d1848, d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17060 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17059 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17061 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16996 pattern childGuard
    simpa only [d380, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17062 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17060 pattern childGuard
    simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17061 pattern childGuard
    simpa only [d399, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17063 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16999 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17064 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17063 pattern childGuard
    simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d394, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17065 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17062 pattern childGuard
    simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17064 pattern childGuard
    simpa only [d407, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17066 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17058 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17065 pattern childGuard
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17067 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11160 pattern childGuard
    simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d394, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17068 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17053 pattern childGuard
    simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17067 pattern childGuard
    simpa only [d407, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17069 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17068 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17047 pattern childGuard
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17070 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17066 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17069 pattern childGuard
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17071 (pattern : Twelve) (guard : d1848 pattern = 1) : d380 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17030 pattern childGuard
    simpa only [d380, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17072 (pattern : Twelve) (guard : d1848 pattern = 1) : d399 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17071 pattern childGuard
    simpa only [d399, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17073 (pattern : Twelve) (guard : d1848 pattern = 1) : d394 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11106 pattern childGuard
    simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17001 pattern childGuard
    simpa only [d394, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17074 (pattern : Twelve) (guard : d1848 pattern = 1) : d407 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17072 pattern childGuard
    simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17073 pattern childGuard
    simpa only [d407, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17075 (pattern : Twelve) (guard : d1848 pattern = 1) : d413 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17074 pattern childGuard
    simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17044 pattern childGuard
    simpa only [d413, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17076 (pattern : Twelve) (guard : d1848 pattern = 1) : d417 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17075 pattern childGuard
    simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17048 pattern childGuard
    simpa only [d417, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17077 (pattern : Twelve) (guard : d1848 pattern = 1) : d420 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17070 pattern childGuard
    simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17076 pattern childGuard
    simpa only [d420, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17078 (pattern : Twelve) (guard : d1848 pattern = 1) : d422 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17050 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17077 pattern childGuard
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17079 (pattern : Twelve) (guard : d1848 pattern = 1) : d423 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17078 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17077 pattern childGuard
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
