/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions45
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6900 (pattern : Twelve) : d1628 (change pattern 12 1) = d1628 pattern := by
  change (if pattern.e then d1304 (change pattern 12 1) else d1624 (change pattern 12 1)) = d1628 pattern
  rw [s6853, s6899]
  rfl
theorem s6901 (pattern : Twelve) : d182 (change pattern 12 1) = d182 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d118 (change pattern 12 1)) = d182 pattern
  rw [s6529, s6650]
  rfl
theorem s6902 (pattern : Twelve) : d1621 (change pattern 12 1) = d1621 pattern := by
  change (if pattern.h then d182 (change pattern 12 1) else d1331 (change pattern 12 1)) = d1621 pattern
  rw [s6901, s6879]
  rfl
theorem s6903 (pattern : Twelve) : d1625 (change pattern 12 1) = d1625 pattern := by
  change (if pattern.f then d1621 (change pattern 12 1) else d49 (change pattern 12 1)) = d1625 pattern
  rw [s6902, s6620]
  rfl
theorem s6904 (pattern : Twelve) : d1626 (change pattern 12 1) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d1252 (change pattern 12 1)) = d1626 pattern
  rw [s6529, s6802]
  rfl
theorem s6905 (pattern : Twelve) : d1629 (change pattern 12 1) = d1629 pattern := by
  change (if pattern.e then d1626 (change pattern 12 1) else d1625 (change pattern 12 1)) = d1629 pattern
  rw [s6904, s6903]
  rfl
theorem s6906 (pattern : Twelve) : d1631 (change pattern 12 1) = d1631 pattern := by
  change (if pattern.j then d1629 (change pattern 12 1) else d1628 (change pattern 12 1)) = d1631 pattern
  rw [s6905, s6900]
  rfl
theorem s6907 (pattern : Twelve) : d1632 (change pattern 12 1) = d1632 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1312 (change pattern 12 1)) = d1632 pattern
  rw [s6529, s6854]
  rfl
theorem s6908 (pattern : Twelve) : d1633 (change pattern 12 1) = d1633 pattern := by
  change (if pattern.d then d1632 (change pattern 12 1) else d1631 (change pattern 12 1)) = d1633 pattern
  rw [s6907, s6906]
  rfl
theorem s6909 (pattern : Twelve) : d1634 (change pattern 12 1) = d1634 pattern := by
  change (if pattern.c then d1633 (change pattern 12 1) else d1630 (change pattern 12 1)) = d1634 pattern
  rw [s6908, s6896]
  rfl
theorem s6910 (pattern : Twelve) : d1635 (change pattern 12 1) = d1635 pattern := by
  change (if pattern.g then d1634 (change pattern 12 1) else d1353 (change pattern 12 1)) = d1635 pattern
  rw [s6909, s6889]
  rfl
theorem s6911 (pattern : Twelve) : d1636 (change pattern 12 1) = d1636 pattern := by
  change (if pattern.a then d1635 (change pattern 12 1) else d1323 (change pattern 12 1)) = d1636 pattern
  rw [s6910, s6859]
  rfl
theorem s6912 (pattern : Twelve) : d1649 (change pattern 12 1) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 12 1) else d19 (change pattern 12 1)) = d1649 pattern
  rw [s6860, s6528]
  rfl
theorem s6913 (pattern : Twelve) : d1650 (change pattern 12 1) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d25 (change pattern 12 1)) = d1650 pattern
  rw [s6529, s6582]
  rfl
theorem s6914 (pattern : Twelve) : d1656 (change pattern 12 1) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 12 1) else d1649 (change pattern 12 1)) = d1656 pattern
  rw [s6913, s6912]
  rfl
theorem s6915 (pattern : Twelve) : d1644 (change pattern 12 1) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 1) else d1324 (change pattern 12 1)) = d1644 pattern
  rw [s6539, s6860]
  rfl
theorem s6916 (pattern : Twelve) : d1645 (change pattern 12 1) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d1324 (change pattern 12 1)) = d1645 pattern
  rw [s6529, s6860]
  rfl
theorem s6917 (pattern : Twelve) : d1647 (change pattern 12 1) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 1) else d1644 (change pattern 12 1)) = d1647 pattern
  rw [s6916, s6915]
  rfl
theorem s6918 (pattern : Twelve) : d1651 (change pattern 12 1) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 12 1) else d1286 (change pattern 12 1)) = d1651 pattern
  rw [s6917, s6822]
  rfl
theorem s6919 (pattern : Twelve) : d1657 (change pattern 12 1) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 12 1) else d1651 (change pattern 12 1)) = d1657 pattern
  rw [s6836, s6918]
  rfl
theorem s6920 (pattern : Twelve) : d1660 (change pattern 12 1) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 12 1) else d1656 (change pattern 12 1)) = d1660 pattern
  rw [s6919, s6914]
  rfl
theorem s6921 (pattern : Twelve) : d1652 (change pattern 12 1) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 12 1) else d817 (change pattern 12 1)) = d1652 pattern
  rw [s6915, s6701]
  rfl
theorem s6922 (pattern : Twelve) : d1653 (change pattern 12 1) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d821 (change pattern 12 1)) = d1653 pattern
  rw [s6529, s6722]
  rfl
theorem s6923 (pattern : Twelve) : d1658 (change pattern 12 1) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 12 1) else d1652 (change pattern 12 1)) = d1658 pattern
  rw [s6922, s6921]
  rfl
theorem s6924 (pattern : Twelve) : d1646 (change pattern 12 1) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d20 (change pattern 12 1)) = d1646 pattern
  rw [s6547, s6539]
  rfl
theorem s6925 (pattern : Twelve) : d1648 (change pattern 12 1) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 12 1) else d1646 (change pattern 12 1)) = d1648 pattern
  rw [s6660, s6924]
  rfl
theorem s6926 (pattern : Twelve) : d1654 (change pattern 12 1) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 12 1) else d1289 (change pattern 12 1)) = d1654 pattern
  rw [s6925, s6835]
  rfl
theorem s6927 (pattern : Twelve) : d1655 (change pattern 12 1) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d822 (change pattern 12 1)) = d1655 pattern
  rw [s6529, s6723]
  rfl
theorem s6928 (pattern : Twelve) : d1659 (change pattern 12 1) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 12 1) else d1654 (change pattern 12 1)) = d1659 pattern
  rw [s6927, s6926]
  rfl
theorem s6929 (pattern : Twelve) : d1661 (change pattern 12 1) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 12 1) else d1658 (change pattern 12 1)) = d1661 pattern
  rw [s6928, s6923]
  rfl
theorem s6930 (pattern : Twelve) : d1662 (change pattern 12 1) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1657 (change pattern 12 1)) = d1662 pattern
  rw [s6529, s6919]
  rfl
theorem s6931 (pattern : Twelve) : d1663 (change pattern 12 1) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 12 1) else d1661 (change pattern 12 1)) = d1663 pattern
  rw [s6930, s6929]
  rfl
theorem s6932 (pattern : Twelve) : d1664 (change pattern 12 1) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 12 1) else d1660 (change pattern 12 1)) = d1664 pattern
  rw [s6931, s6920]
  rfl
theorem s6933 (pattern : Twelve) : d1668 (change pattern 12 1) = d1668 pattern := by
  change (if pattern.f then d1644 (change pattern 12 1) else d19 (change pattern 12 1)) = d1668 pattern
  rw [s6915, s6528]
  rfl
theorem s6934 (pattern : Twelve) : d1671 (change pattern 12 1) = d1671 pattern := by
  change (if pattern.e then d1650 (change pattern 12 1) else d1668 (change pattern 12 1)) = d1671 pattern
  rw [s6913, s6933]
  rfl
theorem s6935 (pattern : Twelve) : d1674 (change pattern 12 1) = d1674 pattern := by
  change (if pattern.j then d1657 (change pattern 12 1) else d1671 (change pattern 12 1)) = d1674 pattern
  rw [s6919, s6934]
  rfl
theorem s6936 (pattern : Twelve) : d1665 (change pattern 12 1) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d1324 (change pattern 12 1)) = d1665 pattern
  rw [s6547, s6860]
  rfl
theorem s6937 (pattern : Twelve) : d1666 (change pattern 12 1) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 12 1) else d1644 (change pattern 12 1)) = d1666 pattern
  rw [s6936, s6915]
  rfl
theorem s6938 (pattern : Twelve) : d1669 (change pattern 12 1) = d1669 pattern := by
  change (if pattern.f then d1666 (change pattern 12 1) else d817 (change pattern 12 1)) = d1669 pattern
  rw [s6937, s6701]
  rfl
theorem s6939 (pattern : Twelve) : d1672 (change pattern 12 1) = d1672 pattern := by
  change (if pattern.e then d1300 (change pattern 12 1) else d1669 (change pattern 12 1)) = d1672 pattern
  rw [s6836, s6938]
  rfl
theorem s6940 (pattern : Twelve) : d183 (change pattern 12 1) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d22 (change pattern 12 1)) = d183 pattern
  rw [s6529, s6547]
  rfl
theorem s6941 (pattern : Twelve) : d1667 (change pattern 12 1) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 12 1) else d128 (change pattern 12 1)) = d1667 pattern
  rw [s6940, s6660]
  rfl
theorem s6942 (pattern : Twelve) : d1670 (change pattern 12 1) = d1670 pattern := by
  change (if pattern.f then d1667 (change pattern 12 1) else d1289 (change pattern 12 1)) = d1670 pattern
  rw [s6941, s6835]
  rfl
theorem s6943 (pattern : Twelve) : d1673 (change pattern 12 1) = d1673 pattern := by
  change (if pattern.e then d1626 (change pattern 12 1) else d1670 (change pattern 12 1)) = d1673 pattern
  rw [s6904, s6942]
  rfl
theorem s6944 (pattern : Twelve) : d1675 (change pattern 12 1) = d1675 pattern := by
  change (if pattern.j then d1673 (change pattern 12 1) else d1672 (change pattern 12 1)) = d1675 pattern
  rw [s6943, s6939]
  rfl
theorem s6945 (pattern : Twelve) : d1676 (change pattern 12 1) = d1676 pattern := by
  change (if pattern.d then d1662 (change pattern 12 1) else d1675 (change pattern 12 1)) = d1676 pattern
  rw [s6930, s6944]
  rfl
theorem s6946 (pattern : Twelve) : d1677 (change pattern 12 1) = d1677 pattern := by
  change (if pattern.c then d1676 (change pattern 12 1) else d1674 (change pattern 12 1)) = d1677 pattern
  rw [s6945, s6935]
  rfl
theorem s6947 (pattern : Twelve) : d1814 (change pattern 12 1) = d1814 pattern := by
  change (if pattern.f then d20 (change pattern 12 1) else d25 (change pattern 12 1)) = d1814 pattern
  rw [s6539, s6582]
  rfl
theorem s6948 (pattern : Twelve) : d1815 (change pattern 12 1) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 12 1) else d21 (change pattern 12 1)) = d1815 pattern
  rw [s6529, s6543]
  rfl
theorem s6949 (pattern : Twelve) : d1818 (change pattern 12 1) = d1818 pattern := by
  change (if pattern.e then d1815 (change pattern 12 1) else d1814 (change pattern 12 1)) = d1818 pattern
  rw [s6948, s6947]
  rfl
theorem s6950 (pattern : Twelve) : d1821 (change pattern 12 1) = d1821 pattern := by
  change (if pattern.j then d1659 (change pattern 12 1) else d1818 (change pattern 12 1)) = d1821 pattern
  rw [s6928, s6949]
  rfl
theorem s6951 (pattern : Twelve) : d1816 (change pattern 12 1) = d1816 pattern := by
  change (if pattern.f then d1646 (change pattern 12 1) else d821 (change pattern 12 1)) = d1816 pattern
  rw [s6924, s6722]
  rfl
theorem s6952 (pattern : Twelve) : d1819 (change pattern 12 1) = d1819 pattern := by
  change (if pattern.e then d1655 (change pattern 12 1) else d1816 (change pattern 12 1)) = d1819 pattern
  rw [s6927, s6951]
  rfl
theorem s6953 (pattern : Twelve) : d1817 (change pattern 12 1) = d1817 pattern := by
  change (if pattern.f then d183 (change pattern 12 1) else d822 (change pattern 12 1)) = d1817 pattern
  rw [s6940, s6723]
  rfl
theorem s6954 (pattern : Twelve) : d1820 (change pattern 12 1) = d1820 pattern := by
  change (if pattern.e then d6 (change pattern 12 1) else d1817 (change pattern 12 1)) = d1820 pattern
  rw [s6529, s6953]
  rfl
theorem s6955 (pattern : Twelve) : d1822 (change pattern 12 1) = d1822 pattern := by
  change (if pattern.j then d1820 (change pattern 12 1) else d1819 (change pattern 12 1)) = d1822 pattern
  rw [s6954, s6952]
  rfl
theorem s6956 (pattern : Twelve) : d1823 (change pattern 12 1) = d1823 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d1659 (change pattern 12 1)) = d1823 pattern
  rw [s6529, s6928]
  rfl
theorem s6957 (pattern : Twelve) : d1824 (change pattern 12 1) = d1824 pattern := by
  change (if pattern.d then d1823 (change pattern 12 1) else d1822 (change pattern 12 1)) = d1824 pattern
  rw [s6956, s6955]
  rfl
theorem s6958 (pattern : Twelve) : d1825 (change pattern 12 1) = d1825 pattern := by
  change (if pattern.c then d1824 (change pattern 12 1) else d1821 (change pattern 12 1)) = d1825 pattern
  rw [s6957, s6950]
  rfl
theorem s6959 (pattern : Twelve) : d1826 (change pattern 12 1) = d1826 pattern := by
  change (if pattern.g then d1825 (change pattern 12 1) else d1677 (change pattern 12 1)) = d1826 pattern
  rw [s6958, s6946]
  rfl
theorem s6960 (pattern : Twelve) : d1827 (change pattern 12 1) = d1827 pattern := by
  change (if pattern.a then d1826 (change pattern 12 1) else d1664 (change pattern 12 1)) = d1827 pattern
  rw [s6959, s6932]
  rfl
theorem s6961 (pattern : Twelve) : d0 (change pattern 0 12) = d0 pattern := by
  rfl
theorem s6962 (pattern : Twelve) : d1 (change pattern 0 12) = d1 pattern := by
  rfl
theorem s6963 (pattern : Twelve) : d26 (change pattern 0 12) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 0 12) else d0 (change pattern 0 12)) = d26 pattern
  rw [s6962, s6961]
  rfl
theorem s6964 (pattern : Twelve) : d7 (change pattern 0 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 0 12) else d0 (change pattern 0 12)) = d7 pattern
  rw [s6962, s6961]
  rfl
theorem s6965 (pattern : Twelve) : d17 (change pattern 0 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 0 12) else d0 (change pattern 0 12)) = d17 pattern
  rw [s6964, s6961]
  rfl
theorem s6966 (pattern : Twelve) : d27 (change pattern 0 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 0 12) else d17 (change pattern 0 12)) = d27 pattern
  rw [s6962, s6965]
  rfl
theorem s6967 (pattern : Twelve) : d50 (change pattern 0 12) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 0 12) else d26 (change pattern 0 12)) = d50 pattern
  rw [s6966, s6963]
  rfl
theorem s6968 (pattern : Twelve) : d72 (change pattern 0 12) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 0 12) else d0 (change pattern 0 12)) = d72 pattern
  rw [s6967, s6961]
  rfl
theorem s6969 (pattern : Twelve) : d2 (change pattern 0 12) = d2 pattern := by
  rfl
theorem s6970 (pattern : Twelve) : d8 (change pattern 0 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 0 12) else d1 (change pattern 0 12)) = d8 pattern
  rw [s6969, s6962]
  rfl
theorem s6971 (pattern : Twelve) : d3 (change pattern 0 12) = d3 pattern := by
  rfl
theorem s6972 (pattern : Twelve) : d9 (change pattern 0 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 0 12) else d2 (change pattern 0 12)) = d9 pattern
  rw [s6971, s6969]
  rfl
theorem s6973 (pattern : Twelve) : d18 (change pattern 0 12) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 0 12) else d8 (change pattern 0 12)) = d18 pattern
  rw [s6972, s6970]
  rfl
theorem s6974 (pattern : Twelve) : d28 (change pattern 0 12) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 0 12) else d17 (change pattern 0 12)) = d28 pattern
  rw [s6973, s6965]
  rfl
theorem s6975 (pattern : Twelve) : d10 (change pattern 0 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 0 12) else d0 (change pattern 0 12)) = d10 pattern
  rw [s6969, s6961]
  rfl
theorem s6976 (pattern : Twelve) : d11 (change pattern 0 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 0 12) else d1 (change pattern 0 12)) = d11 pattern
  rw [s6971, s6962]
  rfl
theorem s6977 (pattern : Twelve) : d19 (change pattern 0 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 0 12) else d10 (change pattern 0 12)) = d19 pattern
  rw [s6976, s6975]
  rfl
theorem s6978 (pattern : Twelve) : d6 (change pattern 0 12) = d6 pattern := by
  rfl
theorem s6979 (pattern : Twelve) : d29 (change pattern 0 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d19 (change pattern 0 12)) = d29 pattern
  rw [s6978, s6977]
  rfl
theorem s6980 (pattern : Twelve) : d51 (change pattern 0 12) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 0 12) else d28 (change pattern 0 12)) = d51 pattern
  rw [s6979, s6974]
  rfl
theorem s6981 (pattern : Twelve) : d73 (change pattern 0 12) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 0 12) else d0 (change pattern 0 12)) = d73 pattern
  rw [s6980, s6961]
  rfl
theorem s6982 (pattern : Twelve) : d91 (change pattern 0 12) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 0 12) else d72 (change pattern 0 12)) = d91 pattern
  rw [s6981, s6968]
  rfl
theorem s6983 (pattern : Twelve) : d30 (change pattern 0 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 0 12) else d0 (change pattern 0 12)) = d30 pattern
  rw [s6969, s6961]
  rfl
theorem s6984 (pattern : Twelve) : d5 (change pattern 0 12) = d5 pattern := by
  rfl
theorem s6985 (pattern : Twelve) : d12 (change pattern 0 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 0 12) else d3 (change pattern 0 12)) = d12 pattern
  rw [s6984, s6971]
  rfl
theorem s6986 (pattern : Twelve) : d4 (change pattern 0 12) = d4 pattern := by
  rfl
theorem s6987 (pattern : Twelve) : d13 (change pattern 0 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 0 12) else d4 (change pattern 0 12)) = d13 pattern
  rw [s6978, s6986]
  rfl
theorem s6988 (pattern : Twelve) : d20 (change pattern 0 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 0 12) else d12 (change pattern 0 12)) = d20 pattern
  rw [s6987, s6985]
  rfl
theorem s6989 (pattern : Twelve) : d31 (change pattern 0 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 0 12) else d0 (change pattern 0 12)) = d31 pattern
  rw [s6988, s6961]
  rfl
theorem s6990 (pattern : Twelve) : d52 (change pattern 0 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 0 12) else d30 (change pattern 0 12)) = d52 pattern
  rw [s6989, s6983]
  rfl
theorem s6991 (pattern : Twelve) : d14 (change pattern 0 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 0 12) else d5 (change pattern 0 12)) = d14 pattern
  rw [s6978, s6984]
  rfl
theorem s6992 (pattern : Twelve) : d21 (change pattern 0 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 0 12) else d13 (change pattern 0 12)) = d21 pattern
  rw [s6991, s6987]
  rfl
theorem s6993 (pattern : Twelve) : d32 (change pattern 0 12) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 0 12) else d17 (change pattern 0 12)) = d32 pattern
  rw [s6992, s6965]
  rfl
theorem s6994 (pattern : Twelve) : d53 (change pattern 0 12) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 0 12) else d30 (change pattern 0 12)) = d53 pattern
  rw [s6993, s6983]
  rfl
theorem s6995 (pattern : Twelve) : d74 (change pattern 0 12) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 0 12) else d52 (change pattern 0 12)) = d74 pattern
  rw [s6994, s6990]
  rfl
theorem s6996 (pattern : Twelve) : d22 (change pattern 0 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 0 12) else d14 (change pattern 0 12)) = d22 pattern
  rw [s6978, s6991]
  rfl
theorem s6997 (pattern : Twelve) : d33 (change pattern 0 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 0 12) else d0 (change pattern 0 12)) = d33 pattern
  rw [s6996, s6961]
  rfl
theorem s6998 (pattern : Twelve) : d54 (change pattern 0 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 0 12) else d30 (change pattern 0 12)) = d54 pattern
  rw [s6997, s6983]
  rfl
theorem s6999 (pattern : Twelve) : d23 (change pattern 0 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 0 12) else d2 (change pattern 0 12)) = d23 pattern
  rw [s6972, s6969]
  rfl
theorem s7000 (pattern : Twelve) : d34 (change pattern 0 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 0 12) else d17 (change pattern 0 12)) = d34 pattern
  rw [s6999, s6965]
  rfl
theorem s7001 (pattern : Twelve) : d55 (change pattern 0 12) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 0 12) else d34 (change pattern 0 12)) = d55 pattern
  rw [s6979, s7000]
  rfl
theorem s7002 (pattern : Twelve) : d75 (change pattern 0 12) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 0 12) else d54 (change pattern 0 12)) = d75 pattern
  rw [s7001, s6998]
  rfl
theorem s7003 (pattern : Twelve) : d92 (change pattern 0 12) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 0 12) else d74 (change pattern 0 12)) = d92 pattern
  rw [s7002, s6995]
  rfl
theorem s7004 (pattern : Twelve) : d102 (change pattern 0 12) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 0 12) else d91 (change pattern 0 12)) = d102 pattern
  rw [s7003, s6982]
  rfl
theorem s7005 (pattern : Twelve) : d76 (change pattern 0 12) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 0 12) else d0 (change pattern 0 12)) = d76 pattern
  rw [s7001, s6961]
  rfl
theorem s7006 (pattern : Twelve) : d93 (change pattern 0 12) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 0 12) else d72 (change pattern 0 12)) = d93 pattern
  rw [s7005, s6968]
  rfl
theorem s7007 (pattern : Twelve) : d35 (change pattern 0 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d0 (change pattern 0 12)) = d35 pattern
  rw [s6978, s6961]
  rfl
theorem s7008 (pattern : Twelve) : d56 (change pattern 0 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 0 12) else d30 (change pattern 0 12)) = d56 pattern
  rw [s7007, s6983]
  rfl
theorem s7009 (pattern : Twelve) : d36 (change pattern 0 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d17 (change pattern 0 12)) = d36 pattern
  rw [s6978, s6965]
  rfl
theorem s7010 (pattern : Twelve) : d57 (change pattern 0 12) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 0 12) else d30 (change pattern 0 12)) = d57 pattern
  rw [s7009, s6983]
  rfl
theorem s7011 (pattern : Twelve) : d77 (change pattern 0 12) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 0 12) else d56 (change pattern 0 12)) = d77 pattern
  rw [s7010, s7008]
  rfl
theorem s7012 (pattern : Twelve) : d78 (change pattern 0 12) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 0 12) else d56 (change pattern 0 12)) = d78 pattern
  rw [s7001, s7008]
  rfl
theorem s7013 (pattern : Twelve) : d94 (change pattern 0 12) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 0 12) else d77 (change pattern 0 12)) = d94 pattern
  rw [s7012, s7011]
  rfl
theorem s7014 (pattern : Twelve) : d103 (change pattern 0 12) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 0 12) else d93 (change pattern 0 12)) = d103 pattern
  rw [s7013, s7006]
  rfl
theorem s7015 (pattern : Twelve) : d110 (change pattern 0 12) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 0 12) else d102 (change pattern 0 12)) = d110 pattern
  rw [s7014, s7004]
  rfl
theorem s7016 (pattern : Twelve) : d37 (change pattern 0 12) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 0 12) else d17 (change pattern 0 12)) = d37 pattern
  rw [s6971, s6965]
  rfl
theorem s7017 (pattern : Twelve) : d58 (change pattern 0 12) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 0 12) else d30 (change pattern 0 12)) = d58 pattern
  rw [s7016, s6983]
  rfl
theorem s7018 (pattern : Twelve) : d79 (change pattern 0 12) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 0 12) else d30 (change pattern 0 12)) = d79 pattern
  rw [s7017, s6983]
  rfl
theorem s7019 (pattern : Twelve) : d80 (change pattern 0 12) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 0 12) else d30 (change pattern 0 12)) = d80 pattern
  rw [s7001, s6983]
  rfl
theorem s7020 (pattern : Twelve) : d95 (change pattern 0 12) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 0 12) else d79 (change pattern 0 12)) = d95 pattern
  rw [s7019, s7018]
  rfl
theorem s7021 (pattern : Twelve) : d38 (change pattern 0 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 0 12) else d2 (change pattern 0 12)) = d38 pattern
  rw [s6986, s6969]
  rfl
theorem s7022 (pattern : Twelve) : d39 (change pattern 0 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d2 (change pattern 0 12)) = d39 pattern
  rw [s6978, s6969]
  rfl
theorem s7023 (pattern : Twelve) : d59 (change pattern 0 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 0 12) else d38 (change pattern 0 12)) = d59 pattern
  rw [s7022, s7021]
  rfl
theorem s7024 (pattern : Twelve) : d40 (change pattern 0 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d23 (change pattern 0 12)) = d40 pattern
  rw [s6978, s6999]
  rfl
theorem s7025 (pattern : Twelve) : d60 (change pattern 0 12) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 0 12) else d38 (change pattern 0 12)) = d60 pattern
  rw [s7024, s7021]
  rfl
theorem s7026 (pattern : Twelve) : d81 (change pattern 0 12) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 0 12) else d59 (change pattern 0 12)) = d81 pattern
  rw [s7025, s7023]
  rfl
theorem s7027 (pattern : Twelve) : d15 (change pattern 0 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 0 12) else d4 (change pattern 0 12)) = d15 pattern
  rw [s6984, s6986]
  rfl
theorem s7028 (pattern : Twelve) : d24 (change pattern 0 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 0 12) else d4 (change pattern 0 12)) = d24 pattern
  rw [s7027, s6986]
  rfl
theorem s7029 (pattern : Twelve) : d41 (change pattern 0 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 0 12) else d23 (change pattern 0 12)) = d41 pattern
  rw [s7028, s6999]
  rfl
theorem s7030 (pattern : Twelve) : d16 (change pattern 0 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 0 12) else d2 (change pattern 0 12)) = d16 pattern
  rw [s6986, s6969]
  rfl
theorem s7031 (pattern : Twelve) : d25 (change pattern 0 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 0 12) else d16 (change pattern 0 12)) = d25 pattern
  rw [s6985, s7030]
  rfl
theorem s7032 (pattern : Twelve) : d42 (change pattern 0 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d25 (change pattern 0 12)) = d42 pattern
  rw [s6978, s7031]
  rfl
theorem s7033 (pattern : Twelve) : d61 (change pattern 0 12) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 0 12) else d41 (change pattern 0 12)) = d61 pattern
  rw [s7032, s7029]
  rfl
theorem s7034 (pattern : Twelve) : d82 (change pattern 0 12) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 0 12) else d59 (change pattern 0 12)) = d82 pattern
  rw [s7033, s7023]
  rfl
theorem s7035 (pattern : Twelve) : d96 (change pattern 0 12) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 0 12) else d81 (change pattern 0 12)) = d96 pattern
  rw [s7034, s7026]
  rfl
theorem s7036 (pattern : Twelve) : d104 (change pattern 0 12) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 0 12) else d95 (change pattern 0 12)) = d104 pattern
  rw [s7035, s7020]
  rfl
theorem s7037 (pattern : Twelve) : d105 (change pattern 0 12) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d94 (change pattern 0 12)) = d105 pattern
  rw [s6978, s7013]
  rfl
theorem s7038 (pattern : Twelve) : d111 (change pattern 0 12) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 0 12) else d104 (change pattern 0 12)) = d111 pattern
  rw [s7037, s7036]
  rfl
theorem s7039 (pattern : Twelve) : d114 (change pattern 0 12) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 0 12) else d110 (change pattern 0 12)) = d114 pattern
  rw [s7038, s7015]
  rfl
theorem s7040 (pattern : Twelve) : d97 (change pattern 0 12) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 0 12) else d72 (change pattern 0 12)) = d97 pattern
  rw [s7019, s6968]
  rfl
theorem s7041 (pattern : Twelve) : d43 (change pattern 0 12) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 0 12) else d1 (change pattern 0 12)) = d43 pattern
  rw [s6992, s6962]
  rfl
theorem s7042 (pattern : Twelve) : d62 (change pattern 0 12) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 0 12) else d30 (change pattern 0 12)) = d62 pattern
  rw [s7041, s6983]
  rfl
theorem s7043 (pattern : Twelve) : d83 (change pattern 0 12) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 0 12) else d52 (change pattern 0 12)) = d83 pattern
  rw [s7042, s6990]
  rfl
theorem s7044 (pattern : Twelve) : d44 (change pattern 0 12) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 0 12) else d2 (change pattern 0 12)) = d44 pattern
  rw [s6996, s6969]
  rfl
theorem s7045 (pattern : Twelve) : d63 (change pattern 0 12) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 0 12) else d30 (change pattern 0 12)) = d63 pattern
  rw [s7044, s6983]
  rfl
theorem s7046 (pattern : Twelve) : d64 (change pattern 0 12) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 0 12) else d34 (change pattern 0 12)) = d64 pattern
  rw [s7024, s7000]
  rfl
theorem s7047 (pattern : Twelve) : d84 (change pattern 0 12) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 0 12) else d63 (change pattern 0 12)) = d84 pattern
  rw [s7046, s7045]
  rfl
theorem s7048 (pattern : Twelve) : d98 (change pattern 0 12) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 0 12) else d83 (change pattern 0 12)) = d98 pattern
  rw [s7047, s7043]
  rfl
theorem s7049 (pattern : Twelve) : d106 (change pattern 0 12) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 0 12) else d97 (change pattern 0 12)) = d106 pattern
  rw [s7048, s7040]
  rfl
end NetHack.Sokoban21.Diagram
