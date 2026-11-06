/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons011
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c1680 (pattern : Twelve) (guard : d1855 pattern = 1) : d956 pattern ≤ (0 : Int) + d1079 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d956, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1675 pattern childGuard
    simpa only [d1855, d956, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d956, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1679 pattern childGuard
    simpa only [d1855, d956, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1681 (pattern : Twelve) (guard : d1855 pattern = 1) : d963 pattern ≤ (0 : Int) + d1088 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d963, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1674 pattern childGuard
    simpa only [d963, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d963, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1680 pattern childGuard
    simpa only [d963, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1682 (pattern : Twelve) (guard : d0 pattern = 1) : d943 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1683 (pattern : Twelve) (guard : d1853 pattern = 1) : d950 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d950, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c839 pattern childGuard
    simpa only [d1853, d950, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d950, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1682 pattern childGuard
    simpa only [d1853, d950, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1684 (pattern : Twelve) (guard : d1849 pattern = 1) : d944 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1685 (pattern : Twelve) (guard : d1854 pattern = 1) : d951 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d951, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1684 pattern childGuard
    simpa only [d1854, d951, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d951, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1678 pattern childGuard
    simpa only [d1854, d951, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1686 (pattern : Twelve) (guard : d1855 pattern = 1) : d957 pattern ≤ (0 : Int) + d1080 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d957, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1683 pattern childGuard
    simpa only [d1855, d957, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d957, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1685 pattern childGuard
    simpa only [d1855, d957, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1687 (pattern : Twelve) (guard : d1853 pattern = 1) : d263 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d1853, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1853, d263, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1688 (pattern : Twelve) (guard : d1855 pattern = 1) : d958 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d958, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1687 pattern childGuard
    simpa only [d1855, d958, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d958, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1679 pattern childGuard
    simpa only [d1855, d958, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1689 (pattern : Twelve) (guard : d1855 pattern = 1) : d964 pattern ≤ (0 : Int) + d1089 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d964, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1686 pattern childGuard
    simpa only [d964, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d964, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1688 pattern childGuard
    simpa only [d964, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1690 (pattern : Twelve) (guard : d1855 pattern = 1) : d970 pattern ≤ (0 : Int) + d1095 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d970, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1681 pattern childGuard
    simpa only [d970, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d970, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1689 pattern childGuard
    simpa only [d970, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1691 (pattern : Twelve) (guard : d1853 pattern = 1) : d265 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c859 pattern childGuard
    simpa only [d1853, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1589 pattern childGuard
    simpa only [d1853, d265, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1692 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c991 pattern childGuard
    simpa only [d1849, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1693 (pattern : Twelve) (guard : d1854 pattern = 1) : d949 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d949, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1692 pattern childGuard
    simpa only [d1854, d949, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d949, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1678 pattern childGuard
    simpa only [d1854, d949, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1694 (pattern : Twelve) (guard : d1855 pattern = 1) : d959 pattern ≤ (0 : Int) + d1082 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d959, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1691 pattern childGuard
    simpa only [d1855, d959, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d959, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1693 pattern childGuard
    simpa only [d1855, d959, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1695 (pattern : Twelve) (guard : d1853 pattern = 1) : d267 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d1853, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1596 pattern childGuard
    simpa only [d1853, d267, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1696 (pattern : Twelve) (guard : d1848 pattern = 1) : d41 pattern ≤ (0 : Int) + d41 pattern := by
  omega
theorem c1697 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1696 pattern childGuard
    simpa only [d1849, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1849, d251, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1698 (pattern : Twelve) (guard : d0 pattern = 1) : d945 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1699 (pattern : Twelve) (guard : d1854 pattern = 1) : d952 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d952, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1697 pattern childGuard
    simpa only [d1854, d952, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d952, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1698 pattern childGuard
    simpa only [d1854, d952, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1700 (pattern : Twelve) (guard : d1855 pattern = 1) : d960 pattern ≤ (0 : Int) + d1083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d960, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1695 pattern childGuard
    simpa only [d1855, d960, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d960, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1699 pattern childGuard
    simpa only [d1855, d960, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1701 (pattern : Twelve) (guard : d1855 pattern = 1) : d965 pattern ≤ (0 : Int) + d1090 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d965, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1694 pattern childGuard
    simpa only [d965, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d965, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1700 pattern childGuard
    simpa only [d965, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1702 (pattern : Twelve) (guard : d1855 pattern = 1) : d966 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d966, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1688 pattern childGuard
    simpa only [d966, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d966, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d966, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1703 (pattern : Twelve) (guard : d1855 pattern = 1) : d971 pattern ≤ (0 : Int) + d1096 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d971, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1701 pattern childGuard
    simpa only [d971, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d971, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1702 pattern childGuard
    simpa only [d971, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1704 (pattern : Twelve) (guard : d1855 pattern = 1) : d973 pattern ≤ (0 : Int) + d1099 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d973, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1690 pattern childGuard
    simpa only [d973, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d973, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1703 pattern childGuard
    simpa only [d973, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1705 (pattern : Twelve) (guard : d0 pattern = 1) : d943 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1706 (pattern : Twelve) (guard : d1853 pattern = 1) : d953 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d953, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d1853, d953, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d953, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1705 pattern childGuard
    simpa only [d1853, d953, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1707 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1708 (pattern : Twelve) (guard : d1848 pattern = 1) : d823 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1707 pattern childGuard
    simpa only [d1848, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1709 (pattern : Twelve) (guard : d1849 pattern = 1) : d946 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1708 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c980 pattern childGuard
    simpa only [d1849, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1710 (pattern : Twelve) (guard : d1854 pattern = 1) : d954 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d954, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1709 pattern childGuard
    simpa only [d1854, d954, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d954, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1678 pattern childGuard
    simpa only [d1854, d954, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1711 (pattern : Twelve) (guard : d1855 pattern = 1) : d961 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d961, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1706 pattern childGuard
    simpa only [d1855, d961, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d961, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1710 pattern childGuard
    simpa only [d1855, d961, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1712 (pattern : Twelve) (guard : d1855 pattern = 1) : d967 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d967, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1711 pattern childGuard
    simpa only [d967, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d967, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1688 pattern childGuard
    simpa only [d967, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1713 (pattern : Twelve) (guard : d1853 pattern = 1) : d263 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d1853, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1581 pattern childGuard
    simpa only [d1853, d263, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1714 (pattern : Twelve) (guard : d1855 pattern = 1) : d958 pattern ≤ (0 : Int) + d1085 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d958, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1713 pattern childGuard
    simpa only [d1855, d958, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d958, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1693 pattern childGuard
    simpa only [d1855, d958, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1715 (pattern : Twelve) (guard : d1855 pattern = 1) : d968 pattern ≤ (0 : Int) + d1093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d968, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1714 pattern childGuard
    simpa only [d968, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d968, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1700 pattern childGuard
    simpa only [d968, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1716 (pattern : Twelve) (guard : d1855 pattern = 1) : d972 pattern ≤ (0 : Int) + d1097 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d972, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1715 pattern childGuard
    simpa only [d972, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d972, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1702 pattern childGuard
    simpa only [d972, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1717 (pattern : Twelve) (guard : d1855 pattern = 1) : d974 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d974, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1712 pattern childGuard
    simpa only [d974, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d974, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1716 pattern childGuard
    simpa only [d974, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1718 (pattern : Twelve) (guard : d1855 pattern = 1) : d976 pattern ≤ (0 : Int) + d1102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d976, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1704 pattern childGuard
    simpa only [d976, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d976, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1717 pattern childGuard
    simpa only [d976, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1719 (pattern : Twelve) (guard : d1855 pattern = 1) : d962 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d962, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1706 pattern childGuard
    simpa only [d1855, d962, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d962, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1685 pattern childGuard
    simpa only [d1855, d962, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1720 (pattern : Twelve) (guard : d1855 pattern = 1) : d969 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d969, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1719 pattern childGuard
    simpa only [d969, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d969, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1688 pattern childGuard
    simpa only [d969, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1721 (pattern : Twelve) (guard : d1855 pattern = 1) : d975 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d975, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1720 pattern childGuard
    simpa only [d975, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d975, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1716 pattern childGuard
    simpa only [d975, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1722 (pattern : Twelve) (guard : d1855 pattern = 1) : d977 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1721 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1717 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1723 (pattern : Twelve) (guard : d1855 pattern = 1) : d978 pattern ≤ (0 : Int) + d1103 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d978, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1718 pattern childGuard
    simpa only [d978, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d978, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1722 pattern childGuard
    simpa only [d978, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1724 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d879 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1725 (pattern : Twelve) (guard : d1849 pattern = 1) : d241 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d241, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d241, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d241, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1724 pattern childGuard
    simpa only [d1849, d241, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1726 (pattern : Twelve) (guard : d1854 pattern = 1) : d949 pattern ≤ (0 : Int) + d1076 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d949, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1725 pattern childGuard
    simpa only [d1854, d949, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d949, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1678 pattern childGuard
    simpa only [d1854, d949, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1727 (pattern : Twelve) (guard : d1855 pattern = 1) : d958 pattern ≤ (0 : Int) + d1086 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d958, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1713 pattern childGuard
    simpa only [d1855, d958, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d958, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1726 pattern childGuard
    simpa only [d1855, d958, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1728 (pattern : Twelve) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d118 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1729 (pattern : Twelve) (guard : d1848 pattern = 1) : d41 pattern ≤ (0 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1728 pattern childGuard
    simpa only [d1848, d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1730 (pattern : Twelve) (guard : d1849 pattern = 1) : d251 pattern ≤ (0 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d251, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1729 pattern childGuard
    simpa only [d1849, d251, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d251, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1068 pattern childGuard
    simpa only [d1849, d251, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1731 (pattern : Twelve) (guard : d1854 pattern = 1) : d952 pattern ≤ (0 : Int) + d1077 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d952, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1730 pattern childGuard
    simpa only [d1854, d952, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d952, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1698 pattern childGuard
    simpa only [d1854, d952, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1732 (pattern : Twelve) (guard : d1855 pattern = 1) : d960 pattern ≤ (0 : Int) + d1087 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d960, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1695 pattern childGuard
    simpa only [d1855, d960, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d960, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1731 pattern childGuard
    simpa only [d1855, d960, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1733 (pattern : Twelve) (guard : d1855 pattern = 1) : d968 pattern ≤ (0 : Int) + d1094 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d968, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1727 pattern childGuard
    simpa only [d968, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d968, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1732 pattern childGuard
    simpa only [d968, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1734 (pattern : Twelve) (guard : d1855 pattern = 1) : d972 pattern ≤ (0 : Int) + d1098 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d972, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1733 pattern childGuard
    simpa only [d972, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d972, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1702 pattern childGuard
    simpa only [d972, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1735 (pattern : Twelve) (guard : d1855 pattern = 1) : d975 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d975, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1720 pattern childGuard
    simpa only [d975, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d975, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1734 pattern childGuard
    simpa only [d975, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1736 (pattern : Twelve) (guard : d1855 pattern = 1) : d974 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d974, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1712 pattern childGuard
    simpa only [d974, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d974, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1734 pattern childGuard
    simpa only [d974, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1737 (pattern : Twelve) (guard : d1855 pattern = 1) : d977 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1735 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1736 pattern childGuard
    simpa only [d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1738 (pattern : Twelve) (guard : d1855 pattern = 1) : d979 pattern ≤ (0 : Int) + d1104 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d979, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1723 pattern childGuard
    simpa only [d979, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d979, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1737 pattern childGuard
    simpa only [d979, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1739 (pattern : Twelve) (guard : d0 pattern = 1) : d1380 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1740 (pattern : Twelve) (guard : d1853 pattern = 1) : d1385 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1385, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c964 pattern childGuard
    simpa only [d1853, d1385, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1385, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1739 pattern childGuard
    simpa only [d1853, d1385, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1741 (pattern : Twelve) (guard : d1848 pattern = 1) : d19 pattern ≤ (0 : Int) + d19 pattern := by
  omega
theorem c1742 (pattern : Twelve) (guard : d1849 pattern = 1) : d1381 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1741 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d1849, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1743 (pattern : Twelve) (guard : d1854 pattern = 1) : d1386 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1742 pattern childGuard
    simpa only [d1854, d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1386, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1744 (pattern : Twelve) (guard : d1855 pattern = 1) : d1393 pattern ≤ (0 : Int) + d1472 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1393, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1740 pattern childGuard
    simpa only [d1855, d1393, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1393, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1743 pattern childGuard
    simpa only [d1855, d1393, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1745 (pattern : Twelve) (guard : d0 pattern = 1) : d1382 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1746 (pattern : Twelve) (guard : d1853 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1387, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c973 pattern childGuard
    simpa only [d1853, d1387, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1387, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1745 pattern childGuard
    simpa only [d1853, d1387, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1747 (pattern : Twelve) (guard : d1848 pattern = 1) : d817 pattern ≤ (0 : Int) + d817 pattern := by
  omega
theorem c1748 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1849, d942, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1749 (pattern : Twelve) (guard : d1854 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1748 pattern childGuard
    simpa only [d1854, d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1388, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1750 (pattern : Twelve) (guard : d1855 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1473 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1394, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1746 pattern childGuard
    simpa only [d1855, d1394, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1394, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1749 pattern childGuard
    simpa only [d1855, d1394, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1751 (pattern : Twelve) (guard : d1855 pattern = 1) : d1398 pattern ≤ (0 : Int) + d1479 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1398, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1744 pattern childGuard
    simpa only [d1398, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1398, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d1398, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1752 (pattern : Twelve) (guard : d0 pattern = 1) : d1380 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1753 (pattern : Twelve) (guard : d1853 pattern = 1) : d1389 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1389, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c981 pattern childGuard
    simpa only [d1853, d1389, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1389, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1752 pattern childGuard
    simpa only [d1853, d1389, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1754 (pattern : Twelve) (guard : d1855 pattern = 1) : d1395 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1395, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1753 pattern childGuard
    simpa only [d1855, d1395, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1395, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1743 pattern childGuard
    simpa only [d1855, d1395, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1755 (pattern : Twelve) (guard : d1855 pattern = 1) : d1399 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1399, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1754 pattern childGuard
    simpa only [d1399, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1399, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d1399, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1756 (pattern : Twelve) (guard : d1855 pattern = 1) : d1403 pattern ≤ (0 : Int) + d1484 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1403, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1751 pattern childGuard
    simpa only [d1403, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1403, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1755 pattern childGuard
    simpa only [d1403, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1757 (pattern : Twelve) (guard : d1853 pattern = 1) : d1387 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1387, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c992 pattern childGuard
    simpa only [d1853, d1387, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1387, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1745 pattern childGuard
    simpa only [d1853, d1387, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1758 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1064 pattern childGuard
    simpa only [d1849, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1759 (pattern : Twelve) (guard : d1854 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1758 pattern childGuard
    simpa only [d1854, d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1388, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1760 (pattern : Twelve) (guard : d1855 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1475 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1394, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1757 pattern childGuard
    simpa only [d1855, d1394, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1394, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1759 pattern childGuard
    simpa only [d1855, d1394, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1761 (pattern : Twelve) (guard : d0 pattern = 1) : d1383 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1762 (pattern : Twelve) (guard : d1853 pattern = 1) : d1390 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1390, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c998 pattern childGuard
    simpa only [d1853, d1390, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1390, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1761 pattern childGuard
    simpa only [d1853, d1390, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1763 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (0 : Int) + d821 pattern := by
  omega
theorem c1764 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1763 pattern childGuard
    simpa only [d1849, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1849, d945, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1765 (pattern : Twelve) (guard : d1854 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1764 pattern childGuard
    simpa only [d1854, d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1391, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1766 (pattern : Twelve) (guard : d1855 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1476 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1396, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1762 pattern childGuard
    simpa only [d1855, d1396, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1396, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1765 pattern childGuard
    simpa only [d1855, d1396, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1767 (pattern : Twelve) (guard : d1855 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1481 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1400, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1760 pattern childGuard
    simpa only [d1400, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1400, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1766 pattern childGuard
    simpa only [d1400, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1768 (pattern : Twelve) (guard : d1855 pattern = 1) : d1401 pattern ≤ (0 : Int) + d1482 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1401, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d1401, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1401, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d1401, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1769 (pattern : Twelve) (guard : d1855 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1485 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1404, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1767 pattern childGuard
    simpa only [d1404, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1404, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1768 pattern childGuard
    simpa only [d1404, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1770 (pattern : Twelve) (guard : d1855 pattern = 1) : d1405 pattern ≤ (0 : Int) + d1487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1405, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1756 pattern childGuard
    simpa only [d1405, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1405, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1769 pattern childGuard
    simpa only [d1405, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1771 (pattern : Twelve) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1772 (pattern : Twelve) (guard : d1848 pattern = 1) : d1283 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1771 pattern childGuard
    simpa only [d1848, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1773 (pattern : Twelve) (guard : d1849 pattern = 1) : d1384 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1772 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1046 pattern childGuard
    simpa only [d1849, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1774 (pattern : Twelve) (guard : d1854 pattern = 1) : d1392 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1773 pattern childGuard
    simpa only [d1854, d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1392, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1775 (pattern : Twelve) (guard : d1855 pattern = 1) : d1397 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1397, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1753 pattern childGuard
    simpa only [d1855, d1397, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1397, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1774 pattern childGuard
    simpa only [d1855, d1397, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1776 (pattern : Twelve) (guard : d1855 pattern = 1) : d1402 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1402, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1775 pattern childGuard
    simpa only [d1402, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1402, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1750 pattern childGuard
    simpa only [d1402, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1777 (pattern : Twelve) (guard : d1855 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1406, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1776 pattern childGuard
    simpa only [d1406, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1406, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1769 pattern childGuard
    simpa only [d1406, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1778 (pattern : Twelve) (guard : d1855 pattern = 1) : d1408 pattern ≤ (0 : Int) + d1490 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1408, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1770 pattern childGuard
    simpa only [d1408, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1408, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1777 pattern childGuard
    simpa only [d1408, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1779 (pattern : Twelve) (guard : d1855 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1407, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1755 pattern childGuard
    simpa only [d1407, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1407, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1769 pattern childGuard
    simpa only [d1407, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1780 (pattern : Twelve) (guard : d1855 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1779 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1777 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1781 (pattern : Twelve) (guard : d1855 pattern = 1) : d1410 pattern ≤ (0 : Int) + d1491 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1410, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1778 pattern childGuard
    simpa only [d1410, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1410, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1780 pattern childGuard
    simpa only [d1410, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1782 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1329 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1783 (pattern : Twelve) (guard : d1849 pattern = 1) : d942 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d942, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d942, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d942, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1782 pattern childGuard
    simpa only [d1849, d942, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1784 (pattern : Twelve) (guard : d1854 pattern = 1) : d1388 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1388, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1783 pattern childGuard
    simpa only [d1854, d1388, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1388, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1388, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1785 (pattern : Twelve) (guard : d1855 pattern = 1) : d1394 pattern ≤ (0 : Int) + d1477 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1394, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1757 pattern childGuard
    simpa only [d1855, d1394, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1394, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1784 pattern childGuard
    simpa only [d1855, d1394, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1786 (pattern : Twelve) (guard : d0 pattern = 1) : d21 pattern ≤ (0 : Int) + d22 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1787 (pattern : Twelve) (guard : d1848 pattern = 1) : d821 pattern ≤ (0 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1786 pattern childGuard
    simpa only [d1848, d821, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1788 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1787 pattern childGuard
    simpa only [d1849, d945, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1121 pattern childGuard
    simpa only [d1849, d945, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1789 (pattern : Twelve) (guard : d1854 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1391, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1788 pattern childGuard
    simpa only [d1854, d1391, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1391, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1391, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1790 (pattern : Twelve) (guard : d1855 pattern = 1) : d1396 pattern ≤ (0 : Int) + d1478 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1396, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1762 pattern childGuard
    simpa only [d1855, d1396, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1396, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1789 pattern childGuard
    simpa only [d1855, d1396, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1791 (pattern : Twelve) (guard : d1855 pattern = 1) : d1400 pattern ≤ (0 : Int) + d1483 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1400, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1785 pattern childGuard
    simpa only [d1400, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1400, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1790 pattern childGuard
    simpa only [d1400, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1792 (pattern : Twelve) (guard : d1855 pattern = 1) : d1404 pattern ≤ (0 : Int) + d1486 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1404, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1791 pattern childGuard
    simpa only [d1404, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1404, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1768 pattern childGuard
    simpa only [d1404, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1793 (pattern : Twelve) (guard : d1855 pattern = 1) : d1407 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1407, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1755 pattern childGuard
    simpa only [d1407, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1407, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1792 pattern childGuard
    simpa only [d1407, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1794 (pattern : Twelve) (guard : d1855 pattern = 1) : d1406 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1406, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1776 pattern childGuard
    simpa only [d1406, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1406, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1792 pattern childGuard
    simpa only [d1406, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1795 (pattern : Twelve) (guard : d1855 pattern = 1) : d1409 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1793 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1794 pattern childGuard
    simpa only [d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1796 (pattern : Twelve) (guard : d1855 pattern = 1) : d1411 pattern ≤ (0 : Int) + d1492 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1411, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1781 pattern childGuard
    simpa only [d1411, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1411, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1795 pattern childGuard
    simpa only [d1411, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1797 (pattern : Twelve) (guard : d0 pattern = 1) : d1689 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1798 (pattern : Twelve) (guard : d1853 pattern = 1) : d1693 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1693, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1047 pattern childGuard
    simpa only [d1853, d1693, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1693, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1797 pattern childGuard
    simpa only [d1853, d1693, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1799 (pattern : Twelve) (guard : d1848 pattern = 1) : d25 pattern ≤ (0 : Int) + d25 pattern := by
  omega
theorem c1800 (pattern : Twelve) (guard : d1849 pattern = 1) : d1690 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1799 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1105 pattern childGuard
    simpa only [d1849, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1801 (pattern : Twelve) (guard : d1854 pattern = 1) : d1694 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1800 pattern childGuard
    simpa only [d1854, d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1694, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1802 (pattern : Twelve) (guard : d1855 pattern = 1) : d1697 pattern ≤ (0 : Int) + d1730 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1697, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1798 pattern childGuard
    simpa only [d1855, d1697, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1697, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1801 pattern childGuard
    simpa only [d1855, d1697, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1803 (pattern : Twelve) (guard : d0 pattern = 1) : d1691 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1804 (pattern : Twelve) (guard : d1853 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1695, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1053 pattern childGuard
    simpa only [d1853, d1695, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1695, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1803 pattern childGuard
    simpa only [d1853, d1695, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1805 (pattern : Twelve) (guard : d1855 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1731 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1698, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1804 pattern childGuard
    simpa only [d1855, d1698, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1698, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1765 pattern childGuard
    simpa only [d1855, d1698, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1806 (pattern : Twelve) (guard : d1855 pattern = 1) : d1700 pattern ≤ (0 : Int) + d1736 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1700, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1802 pattern childGuard
    simpa only [d1700, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1700, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d1700, d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1807 (pattern : Twelve) (guard : d1853 pattern = 1) : d1695 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1695, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1065 pattern childGuard
    simpa only [d1853, d1695, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1695, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1803 pattern childGuard
    simpa only [d1853, d1695, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1808 (pattern : Twelve) (guard : d1849 pattern = 1) : d945 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1763 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1117 pattern childGuard
    simpa only [d1849, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1809 (pattern : Twelve) (guard : d1854 pattern = 1) : d1391 pattern ≤ (0 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1808 pattern childGuard
    simpa only [d1854, d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1391, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1810 (pattern : Twelve) (guard : d1855 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1732 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1698, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1807 pattern childGuard
    simpa only [d1855, d1698, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1698, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1809 pattern childGuard
    simpa only [d1855, d1698, d1732, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1811 (pattern : Twelve) (guard : d0 pattern = 1) : d1692 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1812 (pattern : Twelve) (guard : d1853 pattern = 1) : d1696 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1853, d1696, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1071 pattern childGuard
    simpa only [d1853, d1696, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1853, d1696, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1811 pattern childGuard
    simpa only [d1853, d1696, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1813 (pattern : Twelve) (guard : d1854 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1854, d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1542 pattern childGuard
    simpa only [d1854, d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1854, d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1854, d1626, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1814 (pattern : Twelve) (guard : d1855 pattern = 1) : d1699 pattern ≤ (0 : Int) + d1733 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1699, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1812 pattern childGuard
    simpa only [d1855, d1699, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1699, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1813 pattern childGuard
    simpa only [d1855, d1699, d1733, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1815 (pattern : Twelve) (guard : d1855 pattern = 1) : d1701 pattern ≤ (0 : Int) + d1737 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1701, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1810 pattern childGuard
    simpa only [d1701, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1701, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1814 pattern childGuard
    simpa only [d1701, d1737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1816 (pattern : Twelve) (guard : d1855 pattern = 1) : d1702 pattern ≤ (0 : Int) + d1738 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1702, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1805 pattern childGuard
    simpa only [d1702, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1702, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1603 pattern childGuard
    simpa only [d1702, d1738, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1817 (pattern : Twelve) (guard : d1855 pattern = 1) : d1703 pattern ≤ (0 : Int) + d1740 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1703, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1815 pattern childGuard
    simpa only [d1703, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1703, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1816 pattern childGuard
    simpa only [d1703, d1740, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1818 (pattern : Twelve) (guard : d1855 pattern = 1) : d1704 pattern ≤ (0 : Int) + d1742 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1704, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1806 pattern childGuard
    simpa only [d1704, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1855 pattern = 1 := by simpa only [d1704, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1817 pattern childGuard
    simpa only [d1704, d1742, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1819 (pattern : Twelve) (guard : d1855 pattern = 1) : d1698 pattern ≤ (0 : Int) + d1734 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1853 pattern = 1 := by simpa only [d1855, d1698, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1807 pattern childGuard
    simpa only [d1855, d1698, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1854 pattern = 1 := by simpa only [d1855, d1698, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1765 pattern childGuard
    simpa only [d1855, d1698, d1734, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
