import NetHack.Soko22Hazard87.OldNodes004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldNode2000 (p : Pattern) : NetHack.Sokoban22Refined85.d2000 p = d49599 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1923 p else NetHack.Sokoban22Refined85.d1878 p) = d49599 p
  rw [oldNode1923, oldNode1878]
  rfl
theorem oldNode2001 (p : Pattern) : NetHack.Sokoban22Refined85.d2001 p = d49600 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d1925 p else NetHack.Sokoban22Refined85.d2000 p) = d49600 p
  rw [oldNode1925, oldNode2000]
  rfl
theorem oldNode2002 (p : Pattern) : NetHack.Sokoban22Refined85.d2002 p = d49601 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d1928 p else NetHack.Sokoban22Refined85.d2001 p) = d49601 p
  rw [oldNode1928, oldNode2001]
  rfl
theorem oldNode2003 (p : Pattern) : NetHack.Sokoban22Refined85.d2003 p = d49602 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d1936 p else NetHack.Sokoban22Refined85.d2002 p) = d49602 p
  rw [oldNode1936, oldNode2002]
  rfl
theorem oldNode2004 (p : Pattern) : NetHack.Sokoban22Refined85.d2004 p = d49603 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2003 p else NetHack.Sokoban22Refined85.d1999 p) = d49603 p
  rw [oldNode2003, oldNode1999]
  rfl
theorem oldNode2005 (p : Pattern) : NetHack.Sokoban22Refined85.d2005 p = d49604 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d1989 p else NetHack.Sokoban22Refined85.d2004 p) = d49604 p
  rw [oldNode1989, oldNode2004]
  rfl
theorem oldNode2006 (p : Pattern) : NetHack.Sokoban22Refined85.d2006 p = d49605 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d1989 p) = d49605 p
  rw [oldNode12, oldNode1989]
  rfl
theorem oldNode2007 (p : Pattern) : NetHack.Sokoban22Refined85.d2007 p = d49606 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2006 p else NetHack.Sokoban22Refined85.d2005 p) = d49606 p
  rw [oldNode2006, oldNode2005]
  rfl
theorem oldNode2008 (p : Pattern) : NetHack.Sokoban22Refined85.d2008 p = d49607 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d2007 p else NetHack.Sokoban22Refined85.d1996 p) = d49607 p
  rw [oldNode2007, oldNode1996]
  rfl
theorem oldNode2009 (p : Pattern) : NetHack.Sokoban22Refined85.d2009 p = d49608 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d2008 p else NetHack.Sokoban22Refined85.d1849 p) = d49608 p
  rw [oldNode2008, oldNode1849]
  rfl
theorem oldNode2010 (p : Pattern) : NetHack.Sokoban22Refined85.d2010 p = d49609 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d2009 p else NetHack.Sokoban22Refined85.d1870 p) = d49609 p
  rw [oldNode2009, oldNode1870]
  rfl
theorem oldNode2011 (p : Pattern) : NetHack.Sokoban22Refined85.d2011 p = d49610 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1795 p else NetHack.Sokoban22Refined85.d18 p) = d49610 p
  rw [oldNode1795, oldNode18]
  rfl
theorem oldNode2012 (p : Pattern) : NetHack.Sokoban22Refined85.d2012 p = d49611 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1795 p else NetHack.Sokoban22Refined85.d2011 p) = d49611 p
  rw [oldNode1795, oldNode2011]
  rfl
theorem oldNode2013 (p : Pattern) : NetHack.Sokoban22Refined85.d2013 p = d49612 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2012 p) = d49612 p
  rw [oldNode12, oldNode2012]
  rfl
theorem oldNode2014 (p : Pattern) : NetHack.Sokoban22Refined85.d2014 p = d49613 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2013 p else NetHack.Sokoban22Refined85.d19 p) = d49613 p
  rw [oldNode2013, oldNode19]
  rfl
theorem oldNode2015 (p : Pattern) : NetHack.Sokoban22Refined85.d2015 p = d49614 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2014 p else NetHack.Sokoban22Refined85.d1774 p) = d49614 p
  rw [oldNode2014, oldNode1774]
  rfl
theorem oldNode2016 (p : Pattern) : NetHack.Sokoban22Refined85.d2016 p = d49615 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2015 p else NetHack.Sokoban22Refined85.d1774 p) = d49615 p
  rw [oldNode2015, oldNode1774]
  rfl
theorem oldNode2017 (p : Pattern) : NetHack.Sokoban22Refined85.d2017 p = d49616 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d1806 p else NetHack.Sokoban22Refined85.d2015 p) = d49616 p
  rw [oldNode1806, oldNode2015]
  rfl
theorem oldNode2018 (p : Pattern) : NetHack.Sokoban22Refined85.d2018 p = d49617 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2017 p else NetHack.Sokoban22Refined85.d2016 p) = d49617 p
  rw [oldNode2017, oldNode2016]
  rfl
theorem oldNode2019 (p : Pattern) : NetHack.Sokoban22Refined85.d2019 p = d49618 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d1725 p else NetHack.Sokoban22Refined85.d32 p) = d49618 p
  rw [oldNode1725, oldNode32]
  rfl
theorem oldNode2020 (p : Pattern) : NetHack.Sokoban22Refined85.d2020 p = d49619 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2019 p else NetHack.Sokoban22Refined85.d1809 p) = d49619 p
  rw [oldNode2019, oldNode1809]
  rfl
theorem oldNode2021 (p : Pattern) : NetHack.Sokoban22Refined85.d2021 p = d49620 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d1730 p else NetHack.Sokoban22Refined85.d32 p) = d49620 p
  rw [oldNode1730, oldNode32]
  rfl
theorem oldNode2022 (p : Pattern) : NetHack.Sokoban22Refined85.d2022 p = d49621 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d36 p) = d49621 p
  rw [oldNode12, oldNode36]
  rfl
theorem oldNode2023 (p : Pattern) : NetHack.Sokoban22Refined85.d2023 p = d49622 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2022 p else NetHack.Sokoban22Refined85.d2021 p) = d49622 p
  rw [oldNode2022, oldNode2021]
  rfl
theorem oldNode2024 (p : Pattern) : NetHack.Sokoban22Refined85.d2024 p = d49623 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2023 p else NetHack.Sokoban22Refined85.d2020 p) = d49623 p
  rw [oldNode2023, oldNode2020]
  rfl
theorem oldNode2025 (p : Pattern) : NetHack.Sokoban22Refined85.d2025 p = d49624 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2022 p else NetHack.Sokoban22Refined85.d1760 p) = d49624 p
  rw [oldNode2022, oldNode1760]
  rfl
theorem oldNode2026 (p : Pattern) : NetHack.Sokoban22Refined85.d2026 p = d49625 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d539 p else NetHack.Sokoban22Refined85.d2025 p) = d49625 p
  rw [oldNode539, oldNode2025]
  rfl
theorem oldNode2027 (p : Pattern) : NetHack.Sokoban22Refined85.d2027 p = d49626 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2026 p else NetHack.Sokoban22Refined85.d2024 p) = d49626 p
  rw [oldNode2026, oldNode2024]
  rfl
theorem oldNode2028 (p : Pattern) : NetHack.Sokoban22Refined85.d2028 p = d49627 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2027 p else NetHack.Sokoban22Refined85.d2018 p) = d49627 p
  rw [oldNode2027, oldNode2018]
  rfl
theorem oldNode2029 (p : Pattern) : NetHack.Sokoban22Refined85.d2029 p = d49628 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1714 p else NetHack.Sokoban22Refined85.d31 p) = d49628 p
  rw [oldNode1714, oldNode31]
  rfl
theorem oldNode2030 (p : Pattern) : NetHack.Sokoban22Refined85.d2030 p = d49629 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1714 p else NetHack.Sokoban22Refined85.d2029 p) = d49629 p
  rw [oldNode1714, oldNode2029]
  rfl
theorem oldNode2031 (p : Pattern) : NetHack.Sokoban22Refined85.d2031 p = d49630 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2030 p) = d49630 p
  rw [oldNode12, oldNode2030]
  rfl
theorem oldNode2032 (p : Pattern) : NetHack.Sokoban22Refined85.d2032 p = d49631 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2031 p else NetHack.Sokoban22Refined85.d32 p) = d49631 p
  rw [oldNode2031, oldNode32]
  rfl
theorem oldNode2033 (p : Pattern) : NetHack.Sokoban22Refined85.d2033 p = d49632 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2032 p else NetHack.Sokoban22Refined85.d1774 p) = d49632 p
  rw [oldNode2032, oldNode1774]
  rfl
theorem oldNode2034 (p : Pattern) : NetHack.Sokoban22Refined85.d2034 p = d49633 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1805 p else NetHack.Sokoban22Refined85.d2014 p) = d49633 p
  rw [oldNode1805, oldNode2014]
  rfl
theorem oldNode2035 (p : Pattern) : NetHack.Sokoban22Refined85.d2035 p = d49634 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2034 p else NetHack.Sokoban22Refined85.d2033 p) = d49634 p
  rw [oldNode2034, oldNode2033]
  rfl
theorem oldNode2036 (p : Pattern) : NetHack.Sokoban22Refined85.d2036 p = d49635 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1754 p else NetHack.Sokoban22Refined85.d2014 p) = d49635 p
  rw [oldNode1754, oldNode2014]
  rfl
theorem oldNode2037 (p : Pattern) : NetHack.Sokoban22Refined85.d2037 p = d49636 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d1757 p else NetHack.Sokoban22Refined85.d2036 p) = d49636 p
  rw [oldNode1757, oldNode2036]
  rfl
theorem oldNode2038 (p : Pattern) : NetHack.Sokoban22Refined85.d2038 p = d49637 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2037 p else NetHack.Sokoban22Refined85.d2035 p) = d49637 p
  rw [oldNode2037, oldNode2035]
  rfl
theorem oldNode2039 (p : Pattern) : NetHack.Sokoban22Refined85.d2039 p = d49638 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1732 p else NetHack.Sokoban22Refined85.d2019 p) = d49638 p
  rw [oldNode1732, oldNode2019]
  rfl
theorem oldNode2040 (p : Pattern) : NetHack.Sokoban22Refined85.d2040 p = d49639 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d538 p else NetHack.Sokoban22Refined85.d2022 p) = d49639 p
  rw [oldNode538, oldNode2022]
  rfl
theorem oldNode2041 (p : Pattern) : NetHack.Sokoban22Refined85.d2041 p = d49640 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2040 p else NetHack.Sokoban22Refined85.d2039 p) = d49640 p
  rw [oldNode2040, oldNode2039]
  rfl
theorem oldNode2042 (p : Pattern) : NetHack.Sokoban22Refined85.d2042 p = d49641 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2022 p) = d49641 p
  rw [oldNode12, oldNode2022]
  rfl
theorem oldNode2043 (p : Pattern) : NetHack.Sokoban22Refined85.d2043 p = d49642 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2042 p) = d49642 p
  rw [oldNode12, oldNode2042]
  rfl
theorem oldNode2044 (p : Pattern) : NetHack.Sokoban22Refined85.d2044 p = d49643 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2043 p else NetHack.Sokoban22Refined85.d2041 p) = d49643 p
  rw [oldNode2043, oldNode2041]
  rfl
theorem oldNode2045 (p : Pattern) : NetHack.Sokoban22Refined85.d2045 p = d49644 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2044 p else NetHack.Sokoban22Refined85.d2038 p) = d49644 p
  rw [oldNode2044, oldNode2038]
  rfl
theorem oldNode2046 (p : Pattern) : NetHack.Sokoban22Refined85.d2046 p = d49645 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2045 p else NetHack.Sokoban22Refined85.d2028 p) = d49645 p
  rw [oldNode2045, oldNode2028]
  rfl
theorem oldNode2047 (p : Pattern) : NetHack.Sokoban22Refined85.d2047 p = d49646 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1776 p else NetHack.Sokoban22Refined85.d1770 p) = d49646 p
  rw [oldNode1776, oldNode1770]
  rfl
theorem oldNode2048 (p : Pattern) : NetHack.Sokoban22Refined85.d2048 p = d49647 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2047 p else NetHack.Sokoban22Refined85.d1777 p) = d49647 p
  rw [oldNode2047, oldNode1777]
  rfl
theorem oldNode2049 (p : Pattern) : NetHack.Sokoban22Refined85.d2049 p = d49648 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2048 p) = d49648 p
  rw [oldNode12, oldNode2048]
  rfl
theorem oldNode2050 (p : Pattern) : NetHack.Sokoban22Refined85.d2050 p = d49649 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2049 p else NetHack.Sokoban22Refined85.d15 p) = d49649 p
  rw [oldNode2049, oldNode15]
  rfl
theorem oldNode2051 (p : Pattern) : NetHack.Sokoban22Refined85.d2051 p = d49650 p := by
  change (if p 247 then NetHack.Sokoban22Refined85.d10 p else NetHack.Sokoban22Refined85.d0 p) = d49650 p
  rw [oldNode10, oldNode0]
  rfl
theorem oldNode2052 (p : Pattern) : NetHack.Sokoban22Refined85.d2052 p = d49651 p := by
  change (if p 246 then NetHack.Sokoban22Refined85.d23 p else NetHack.Sokoban22Refined85.d2051 p) = d49651 p
  rw [oldNode23, oldNode2051]
  rfl
theorem oldNode2053 (p : Pattern) : NetHack.Sokoban22Refined85.d2053 p = d49652 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d2052 p else NetHack.Sokoban22Refined85.d1770 p) = d49652 p
  rw [oldNode2052, oldNode1770]
  rfl
theorem oldNode2054 (p : Pattern) : NetHack.Sokoban22Refined85.d2054 p = d49653 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2053 p else NetHack.Sokoban22Refined85.d1777 p) = d49653 p
  rw [oldNode2053, oldNode1777]
  rfl
theorem oldNode2055 (p : Pattern) : NetHack.Sokoban22Refined85.d2055 p = d49654 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2054 p) = d49654 p
  rw [oldNode12, oldNode2054]
  rfl
theorem oldNode2056 (p : Pattern) : NetHack.Sokoban22Refined85.d2056 p = d49655 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2055 p else NetHack.Sokoban22Refined85.d15 p) = d49655 p
  rw [oldNode2055, oldNode15]
  rfl
theorem oldNode2057 (p : Pattern) : NetHack.Sokoban22Refined85.d2057 p = d49656 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2056 p else NetHack.Sokoban22Refined85.d2050 p) = d49656 p
  rw [oldNode2056, oldNode2050]
  rfl
theorem oldNode2058 (p : Pattern) : NetHack.Sokoban22Refined85.d2058 p = d49657 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d1811 p else NetHack.Sokoban22Refined85.d2057 p) = d49657 p
  rw [oldNode1811, oldNode2057]
  rfl
theorem oldNode2059 (p : Pattern) : NetHack.Sokoban22Refined85.d2059 p = d49658 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d1812 p else NetHack.Sokoban22Refined85.d2058 p) = d49658 p
  rw [oldNode1812, oldNode2058]
  rfl
theorem oldNode2060 (p : Pattern) : NetHack.Sokoban22Refined85.d2060 p = d49659 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d315 p else NetHack.Sokoban22Refined85.d191 p) = d49659 p
  rw [oldNode315, oldNode191]
  rfl
theorem oldNode2061 (p : Pattern) : NetHack.Sokoban22Refined85.d2061 p = d49660 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d315 p else NetHack.Sokoban22Refined85.d2060 p) = d49660 p
  rw [oldNode315, oldNode2060]
  rfl
theorem oldNode2062 (p : Pattern) : NetHack.Sokoban22Refined85.d2062 p = d49661 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2061 p) = d49661 p
  rw [oldNode12, oldNode2061]
  rfl
theorem oldNode2063 (p : Pattern) : NetHack.Sokoban22Refined85.d2063 p = d49662 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2062 p else NetHack.Sokoban22Refined85.d192 p) = d49662 p
  rw [oldNode2062, oldNode192]
  rfl
theorem oldNode2064 (p : Pattern) : NetHack.Sokoban22Refined85.d2064 p = d49663 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2063 p else NetHack.Sokoban22Refined85.d1799 p) = d49663 p
  rw [oldNode2063, oldNode1799]
  rfl
theorem oldNode2065 (p : Pattern) : NetHack.Sokoban22Refined85.d2065 p = d49664 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2064 p) = d49664 p
  rw [oldNode12, oldNode2064]
  rfl
theorem oldNode2066 (p : Pattern) : NetHack.Sokoban22Refined85.d2066 p = d49665 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2065 p) = d49665 p
  rw [oldNode12, oldNode2065]
  rfl
theorem oldNode2067 (p : Pattern) : NetHack.Sokoban22Refined85.d2067 p = d49666 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2066 p else NetHack.Sokoban22Refined85.d2059 p) = d49666 p
  rw [oldNode2066, oldNode2059]
  rfl
theorem oldNode2068 (p : Pattern) : NetHack.Sokoban22Refined85.d2068 p = d49667 p := by
  change (if p 247 then NetHack.Sokoban22Refined85.d10 p else NetHack.Sokoban22Refined85.d2 p) = d49667 p
  rw [oldNode10, oldNode2]
  rfl
theorem oldNode2069 (p : Pattern) : NetHack.Sokoban22Refined85.d2069 p = d49668 p := by
  change (if p 246 then NetHack.Sokoban22Refined85.d57 p else NetHack.Sokoban22Refined85.d2068 p) = d49668 p
  rw [oldNode57, oldNode2068]
  rfl
theorem oldNode2070 (p : Pattern) : NetHack.Sokoban22Refined85.d2070 p = d49669 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d2069 p else NetHack.Sokoban22Refined85.d1714 p) = d49669 p
  rw [oldNode2069, oldNode1714]
  rfl
theorem oldNode2071 (p : Pattern) : NetHack.Sokoban22Refined85.d2071 p = d49670 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2070 p else NetHack.Sokoban22Refined85.d1712 p) = d49670 p
  rw [oldNode2070, oldNode1712]
  rfl
theorem oldNode2072 (p : Pattern) : NetHack.Sokoban22Refined85.d2072 p = d49671 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2071 p) = d49671 p
  rw [oldNode12, oldNode2071]
  rfl
theorem oldNode2073 (p : Pattern) : NetHack.Sokoban22Refined85.d2073 p = d49672 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2072 p else NetHack.Sokoban22Refined85.d32 p) = d49672 p
  rw [oldNode2072, oldNode32]
  rfl
theorem oldNode2074 (p : Pattern) : NetHack.Sokoban22Refined85.d2074 p = d49673 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1809 p else NetHack.Sokoban22Refined85.d2073 p) = d49673 p
  rw [oldNode1809, oldNode2073]
  rfl
theorem oldNode2075 (p : Pattern) : NetHack.Sokoban22Refined85.d2075 p = d49674 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1756 p else NetHack.Sokoban22Refined85.d1799 p) = d49674 p
  rw [oldNode1756, oldNode1799]
  rfl
theorem oldNode2076 (p : Pattern) : NetHack.Sokoban22Refined85.d2076 p = d49675 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2075 p else NetHack.Sokoban22Refined85.d2074 p) = d49675 p
  rw [oldNode2075, oldNode2074]
  rfl
theorem oldNode2077 (p : Pattern) : NetHack.Sokoban22Refined85.d2077 p = d49676 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d1822 p else NetHack.Sokoban22Refined85.d2076 p) = d49676 p
  rw [oldNode1822, oldNode2076]
  rfl
theorem oldNode2078 (p : Pattern) : NetHack.Sokoban22Refined85.d2078 p = d49677 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2063 p) = d49677 p
  rw [oldNode12, oldNode2063]
  rfl
theorem oldNode2079 (p : Pattern) : NetHack.Sokoban22Refined85.d2079 p = d49678 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2078 p) = d49678 p
  rw [oldNode12, oldNode2078]
  rfl
theorem oldNode2080 (p : Pattern) : NetHack.Sokoban22Refined85.d2080 p = d49679 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2079 p) = d49679 p
  rw [oldNode12, oldNode2079]
  rfl
theorem oldNode2081 (p : Pattern) : NetHack.Sokoban22Refined85.d2081 p = d49680 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2080 p else NetHack.Sokoban22Refined85.d2077 p) = d49680 p
  rw [oldNode2080, oldNode2077]
  rfl
theorem oldNode2082 (p : Pattern) : NetHack.Sokoban22Refined85.d2082 p = d49681 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2081 p else NetHack.Sokoban22Refined85.d2067 p) = d49681 p
  rw [oldNode2081, oldNode2067]
  rfl
theorem oldNode2083 (p : Pattern) : NetHack.Sokoban22Refined85.d2083 p = d49682 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2082 p else NetHack.Sokoban22Refined85.d2046 p) = d49682 p
  rw [oldNode2082, oldNode2046]
  rfl
theorem oldNode2084 (p : Pattern) : NetHack.Sokoban22Refined85.d2084 p = d49683 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2082 p) = d49683 p
  rw [oldNode12, oldNode2082]
  rfl
theorem oldNode2085 (p : Pattern) : NetHack.Sokoban22Refined85.d2085 p = d49684 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2084 p else NetHack.Sokoban22Refined85.d2083 p) = d49684 p
  rw [oldNode2084, oldNode2083]
  rfl
theorem oldNode2086 (p : Pattern) : NetHack.Sokoban22Refined85.d2086 p = d49685 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d2085 p else NetHack.Sokoban22Refined85.d1862 p) = d49685 p
  rw [oldNode2085, oldNode1862]
  rfl
theorem oldNode2087 (p : Pattern) : NetHack.Sokoban22Refined85.d2087 p = d49686 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d2086 p else NetHack.Sokoban22Refined85.d1849 p) = d49686 p
  rw [oldNode2086, oldNode1849]
  rfl
theorem oldNode2088 (p : Pattern) : NetHack.Sokoban22Refined85.d2088 p = d49687 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d1885 p) = d49687 p
  rw [oldNode12, oldNode1885]
  rfl
theorem oldNode2089 (p : Pattern) : NetHack.Sokoban22Refined85.d2089 p = d49688 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2088 p else NetHack.Sokoban22Refined85.d1924 p) = d49688 p
  rw [oldNode2088, oldNode1924]
  rfl
theorem oldNode2090 (p : Pattern) : NetHack.Sokoban22Refined85.d2090 p = d49689 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2088 p) = d49689 p
  rw [oldNode12, oldNode2088]
  rfl
theorem oldNode2091 (p : Pattern) : NetHack.Sokoban22Refined85.d2091 p = d49690 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2090 p else NetHack.Sokoban22Refined85.d2089 p) = d49690 p
  rw [oldNode2090, oldNode2089]
  rfl
theorem oldNode2092 (p : Pattern) : NetHack.Sokoban22Refined85.d2092 p = d49691 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d1910 p) = d49691 p
  rw [oldNode12, oldNode1910]
  rfl
theorem oldNode2093 (p : Pattern) : NetHack.Sokoban22Refined85.d2093 p = d49692 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2092 p else NetHack.Sokoban22Refined85.d1931 p) = d49692 p
  rw [oldNode2092, oldNode1931]
  rfl
theorem oldNode2094 (p : Pattern) : NetHack.Sokoban22Refined85.d2094 p = d49693 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2092 p) = d49693 p
  rw [oldNode12, oldNode2092]
  rfl
theorem oldNode2095 (p : Pattern) : NetHack.Sokoban22Refined85.d2095 p = d49694 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2094 p else NetHack.Sokoban22Refined85.d2093 p) = d49694 p
  rw [oldNode2094, oldNode2093]
  rfl
theorem oldNode2096 (p : Pattern) : NetHack.Sokoban22Refined85.d2096 p = d49695 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2095 p else NetHack.Sokoban22Refined85.d2091 p) = d49695 p
  rw [oldNode2095, oldNode2091]
  rfl
theorem oldNode2097 (p : Pattern) : NetHack.Sokoban22Refined85.d2097 p = d49696 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2096 p else NetHack.Sokoban22Refined85.d1915 p) = d49696 p
  rw [oldNode2096, oldNode1915]
  rfl
theorem oldNode2098 (p : Pattern) : NetHack.Sokoban22Refined85.d2098 p = d49697 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d1968 p) = d49697 p
  rw [oldNode12, oldNode1968]
  rfl
theorem oldNode2099 (p : Pattern) : NetHack.Sokoban22Refined85.d2099 p = d49698 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2098 p else NetHack.Sokoban22Refined85.d1979 p) = d49698 p
  rw [oldNode2098, oldNode1979]
  rfl
theorem oldNode2100 (p : Pattern) : NetHack.Sokoban22Refined85.d2100 p = d49699 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2098 p) = d49699 p
  rw [oldNode12, oldNode2098]
  rfl
theorem oldNode2101 (p : Pattern) : NetHack.Sokoban22Refined85.d2101 p = d49700 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2100 p else NetHack.Sokoban22Refined85.d2099 p) = d49700 p
  rw [oldNode2100, oldNode2099]
  rfl
theorem oldNode2102 (p : Pattern) : NetHack.Sokoban22Refined85.d2102 p = d49701 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d1987 p else NetHack.Sokoban22Refined85.d2101 p) = d49701 p
  rw [oldNode1987, oldNode2101]
  rfl
theorem oldNode2103 (p : Pattern) : NetHack.Sokoban22Refined85.d2103 p = d49702 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2102 p else NetHack.Sokoban22Refined85.d1978 p) = d49702 p
  rw [oldNode2102, oldNode1978]
  rfl
theorem oldNode2104 (p : Pattern) : NetHack.Sokoban22Refined85.d2104 p = d49703 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2103 p else NetHack.Sokoban22Refined85.d2097 p) = d49703 p
  rw [oldNode2103, oldNode2097]
  rfl
theorem oldNode2105 (p : Pattern) : NetHack.Sokoban22Refined85.d2105 p = d49704 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d1994 p else NetHack.Sokoban22Refined85.d2103 p) = d49704 p
  rw [oldNode1994, oldNode2103]
  rfl
theorem oldNode2106 (p : Pattern) : NetHack.Sokoban22Refined85.d2106 p = d49705 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2105 p else NetHack.Sokoban22Refined85.d2104 p) = d49705 p
  rw [oldNode2105, oldNode2104]
  rfl
theorem oldNode2107 (p : Pattern) : NetHack.Sokoban22Refined85.d2107 p = d49706 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1946 p else NetHack.Sokoban22Refined85.d1940 p) = d49706 p
  rw [oldNode1946, oldNode1940]
  rfl
theorem oldNode2108 (p : Pattern) : NetHack.Sokoban22Refined85.d2108 p = d49707 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2107 p else NetHack.Sokoban22Refined85.d1947 p) = d49707 p
  rw [oldNode2107, oldNode1947]
  rfl
theorem oldNode2109 (p : Pattern) : NetHack.Sokoban22Refined85.d2109 p = d49708 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2108 p) = d49708 p
  rw [oldNode12, oldNode2108]
  rfl
theorem oldNode2110 (p : Pattern) : NetHack.Sokoban22Refined85.d2110 p = d49709 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2109 p else NetHack.Sokoban22Refined85.d104 p) = d49709 p
  rw [oldNode2109, oldNode104]
  rfl
theorem oldNode2111 (p : Pattern) : NetHack.Sokoban22Refined85.d2111 p = d49710 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1968 p else NetHack.Sokoban22Refined85.d2110 p) = d49710 p
  rw [oldNode1968, oldNode2110]
  rfl
theorem oldNode2112 (p : Pattern) : NetHack.Sokoban22Refined85.d2112 p = d49711 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2111 p else NetHack.Sokoban22Refined85.d1944 p) = d49711 p
  rw [oldNode2111, oldNode1944]
  rfl
theorem oldNode2113 (p : Pattern) : NetHack.Sokoban22Refined85.d2113 p = d49712 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1968 p else NetHack.Sokoban22Refined85.d1953 p) = d49712 p
  rw [oldNode1968, oldNode1953]
  rfl
theorem oldNode2114 (p : Pattern) : NetHack.Sokoban22Refined85.d2114 p = d49713 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d1888 p else NetHack.Sokoban22Refined85.d2113 p) = d49713 p
  rw [oldNode1888, oldNode2113]
  rfl
theorem oldNode2115 (p : Pattern) : NetHack.Sokoban22Refined85.d2115 p = d49714 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2114 p else NetHack.Sokoban22Refined85.d2112 p) = d49714 p
  rw [oldNode2114, oldNode2112]
  rfl
theorem oldNode2116 (p : Pattern) : NetHack.Sokoban22Refined85.d2116 p = d49715 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d1906 p else NetHack.Sokoban22Refined85.d117 p) = d49715 p
  rw [oldNode1906, oldNode117]
  rfl
theorem oldNode2117 (p : Pattern) : NetHack.Sokoban22Refined85.d2117 p = d49716 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2116 p else NetHack.Sokoban22Refined85.d1973 p) = d49716 p
  rw [oldNode2116, oldNode1973]
  rfl
theorem oldNode2118 (p : Pattern) : NetHack.Sokoban22Refined85.d2118 p = d49717 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2092 p else NetHack.Sokoban22Refined85.d2117 p) = d49717 p
  rw [oldNode2092, oldNode2117]
  rfl
theorem oldNode2119 (p : Pattern) : NetHack.Sokoban22Refined85.d2119 p = d49718 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d121 p) = d49718 p
  rw [oldNode12, oldNode121]
  rfl
theorem oldNode2120 (p : Pattern) : NetHack.Sokoban22Refined85.d2120 p = d49719 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2119 p) = d49719 p
  rw [oldNode12, oldNode2119]
  rfl
theorem oldNode2121 (p : Pattern) : NetHack.Sokoban22Refined85.d2121 p = d49720 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2120 p) = d49720 p
  rw [oldNode12, oldNode2120]
  rfl
theorem oldNode2122 (p : Pattern) : NetHack.Sokoban22Refined85.d2122 p = d49721 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2121 p else NetHack.Sokoban22Refined85.d2118 p) = d49721 p
  rw [oldNode2121, oldNode2118]
  rfl
theorem oldNode2123 (p : Pattern) : NetHack.Sokoban22Refined85.d2123 p = d49722 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2122 p else NetHack.Sokoban22Refined85.d2115 p) = d49722 p
  rw [oldNode2122, oldNode2115]
  rfl
theorem oldNode2124 (p : Pattern) : NetHack.Sokoban22Refined85.d2124 p = d49723 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1895 p else NetHack.Sokoban22Refined85.d116 p) = d49723 p
  rw [oldNode1895, oldNode116]
  rfl
theorem oldNode2125 (p : Pattern) : NetHack.Sokoban22Refined85.d2125 p = d49724 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1895 p else NetHack.Sokoban22Refined85.d2124 p) = d49724 p
  rw [oldNode1895, oldNode2124]
  rfl
theorem oldNode2126 (p : Pattern) : NetHack.Sokoban22Refined85.d2126 p = d49725 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2125 p) = d49725 p
  rw [oldNode12, oldNode2125]
  rfl
theorem oldNode2127 (p : Pattern) : NetHack.Sokoban22Refined85.d2127 p = d49726 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2126 p else NetHack.Sokoban22Refined85.d117 p) = d49726 p
  rw [oldNode2126, oldNode117]
  rfl
theorem oldNode2128 (p : Pattern) : NetHack.Sokoban22Refined85.d2128 p = d49727 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2127 p else NetHack.Sokoban22Refined85.d2110 p) = d49727 p
  rw [oldNode2127, oldNode2110]
  rfl
theorem oldNode2129 (p : Pattern) : NetHack.Sokoban22Refined85.d2129 p = d49728 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1964 p else NetHack.Sokoban22Refined85.d107 p) = d49728 p
  rw [oldNode1964, oldNode107]
  rfl
theorem oldNode2130 (p : Pattern) : NetHack.Sokoban22Refined85.d2130 p = d49729 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1964 p else NetHack.Sokoban22Refined85.d2129 p) = d49729 p
  rw [oldNode1964, oldNode2129]
  rfl
theorem oldNode2131 (p : Pattern) : NetHack.Sokoban22Refined85.d2131 p = d49730 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2130 p) = d49730 p
  rw [oldNode12, oldNode2130]
  rfl
theorem oldNode2132 (p : Pattern) : NetHack.Sokoban22Refined85.d2132 p = d49731 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2131 p else NetHack.Sokoban22Refined85.d108 p) = d49731 p
  rw [oldNode2131, oldNode108]
  rfl
theorem oldNode2133 (p : Pattern) : NetHack.Sokoban22Refined85.d2133 p = d49732 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2132 p) = d49732 p
  rw [oldNode12, oldNode2132]
  rfl
theorem oldNode2134 (p : Pattern) : NetHack.Sokoban22Refined85.d2134 p = d49733 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2133 p else NetHack.Sokoban22Refined85.d2128 p) = d49733 p
  rw [oldNode2133, oldNode2128]
  rfl
theorem oldNode2135 (p : Pattern) : NetHack.Sokoban22Refined85.d2135 p = d49734 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d1961 p else NetHack.Sokoban22Refined85.d1964 p) = d49734 p
  rw [oldNode1961, oldNode1964]
  rfl
theorem oldNode2136 (p : Pattern) : NetHack.Sokoban22Refined85.d2136 p = d49735 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2135 p else NetHack.Sokoban22Refined85.d1962 p) = d49735 p
  rw [oldNode2135, oldNode1962]
  rfl
theorem oldNode2137 (p : Pattern) : NetHack.Sokoban22Refined85.d2137 p = d49736 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2136 p) = d49736 p
  rw [oldNode12, oldNode2136]
  rfl
theorem oldNode2138 (p : Pattern) : NetHack.Sokoban22Refined85.d2138 p = d49737 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2137 p else NetHack.Sokoban22Refined85.d108 p) = d49737 p
  rw [oldNode2137, oldNode108]
  rfl
theorem oldNode2139 (p : Pattern) : NetHack.Sokoban22Refined85.d2139 p = d49738 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2138 p) = d49738 p
  rw [oldNode12, oldNode2138]
  rfl
theorem oldNode2140 (p : Pattern) : NetHack.Sokoban22Refined85.d2140 p = d49739 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2139 p) = d49739 p
  rw [oldNode12, oldNode2139]
  rfl
theorem oldNode2141 (p : Pattern) : NetHack.Sokoban22Refined85.d2141 p = d49740 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2140 p else NetHack.Sokoban22Refined85.d2134 p) = d49740 p
  rw [oldNode2140, oldNode2134]
  rfl
theorem oldNode2142 (p : Pattern) : NetHack.Sokoban22Refined85.d2142 p = d49741 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d1906 p else NetHack.Sokoban22Refined85.d108 p) = d49741 p
  rw [oldNode1906, oldNode108]
  rfl
theorem oldNode2143 (p : Pattern) : NetHack.Sokoban22Refined85.d2143 p = d49742 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1910 p else NetHack.Sokoban22Refined85.d2142 p) = d49742 p
  rw [oldNode1910, oldNode2142]
  rfl
theorem oldNode2144 (p : Pattern) : NetHack.Sokoban22Refined85.d2144 p = d49743 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2120 p else NetHack.Sokoban22Refined85.d2143 p) = d49743 p
  rw [oldNode2120, oldNode2143]
  rfl
theorem oldNode2145 (p : Pattern) : NetHack.Sokoban22Refined85.d2145 p = d49744 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d528 p) = d49744 p
  rw [oldNode12, oldNode528]
  rfl
theorem oldNode2146 (p : Pattern) : NetHack.Sokoban22Refined85.d2146 p = d49745 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2145 p else NetHack.Sokoban22Refined85.d2144 p) = d49745 p
  rw [oldNode2145, oldNode2144]
  rfl
theorem oldNode2147 (p : Pattern) : NetHack.Sokoban22Refined85.d2147 p = d49746 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2146 p else NetHack.Sokoban22Refined85.d2141 p) = d49746 p
  rw [oldNode2146, oldNode2141]
  rfl
theorem oldNode2148 (p : Pattern) : NetHack.Sokoban22Refined85.d2148 p = d49747 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2147 p else NetHack.Sokoban22Refined85.d2123 p) = d49747 p
  rw [oldNode2147, oldNode2123]
  rfl
theorem oldNode2149 (p : Pattern) : NetHack.Sokoban22Refined85.d2149 p = d49748 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1959 p else NetHack.Sokoban22Refined85.d1953 p) = d49748 p
  rw [oldNode1959, oldNode1953]
  rfl
theorem oldNode2150 (p : Pattern) : NetHack.Sokoban22Refined85.d2150 p = d49749 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1756 p else NetHack.Sokoban22Refined85.d1973 p) = d49749 p
  rw [oldNode1756, oldNode1973]
  rfl
theorem oldNode2151 (p : Pattern) : NetHack.Sokoban22Refined85.d2151 p = d49750 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2150 p else NetHack.Sokoban22Refined85.d2149 p) = d49750 p
  rw [oldNode2150, oldNode2149]
  rfl
theorem oldNode2152 (p : Pattern) : NetHack.Sokoban22Refined85.d2152 p = d49751 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d1983 p else NetHack.Sokoban22Refined85.d2151 p) = d49751 p
  rw [oldNode1983, oldNode2151]
  rfl
theorem oldNode2153 (p : Pattern) : NetHack.Sokoban22Refined85.d2153 p = d49752 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d1987 p else NetHack.Sokoban22Refined85.d2152 p) = d49752 p
  rw [oldNode1987, oldNode2152]
  rfl
theorem oldNode2154 (p : Pattern) : NetHack.Sokoban22Refined85.d2154 p = d49753 p := by
  change (if p 247 then NetHack.Sokoban22Refined85.d11 p else NetHack.Sokoban22Refined85.d3 p) = d49753 p
  rw [oldNode11, oldNode3]
  rfl
theorem oldNode2155 (p : Pattern) : NetHack.Sokoban22Refined85.d2155 p = d49754 p := by
  change (if p 246 then NetHack.Sokoban22Refined85.d39 p else NetHack.Sokoban22Refined85.d2154 p) = d49754 p
  rw [oldNode39, oldNode2154]
  rfl
theorem oldNode2156 (p : Pattern) : NetHack.Sokoban22Refined85.d2156 p = d49755 p := by
  change (if p 225 then NetHack.Sokoban22Refined85.d2155 p else NetHack.Sokoban22Refined85.d1895 p) = d49755 p
  rw [oldNode2155, oldNode1895]
  rfl
theorem oldNode2157 (p : Pattern) : NetHack.Sokoban22Refined85.d2157 p = d49756 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d2156 p else NetHack.Sokoban22Refined85.d1893 p) = d49756 p
  rw [oldNode2156, oldNode1893]
  rfl
theorem oldNode2158 (p : Pattern) : NetHack.Sokoban22Refined85.d2158 p = d49757 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2157 p) = d49757 p
  rw [oldNode12, oldNode2157]
  rfl
theorem oldNode2159 (p : Pattern) : NetHack.Sokoban22Refined85.d2159 p = d49758 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2158 p else NetHack.Sokoban22Refined85.d117 p) = d49758 p
  rw [oldNode2158, oldNode117]
  rfl
theorem oldNode2160 (p : Pattern) : NetHack.Sokoban22Refined85.d2160 p = d49759 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1973 p else NetHack.Sokoban22Refined85.d2159 p) = d49759 p
  rw [oldNode1973, oldNode2159]
  rfl
theorem oldNode2161 (p : Pattern) : NetHack.Sokoban22Refined85.d2161 p = d49760 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2098 p else NetHack.Sokoban22Refined85.d2160 p) = d49760 p
  rw [oldNode2098, oldNode2160]
  rfl
theorem oldNode2162 (p : Pattern) : NetHack.Sokoban22Refined85.d2162 p = d49761 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d1986 p else NetHack.Sokoban22Refined85.d2161 p) = d49761 p
  rw [oldNode1986, oldNode2161]
  rfl
theorem oldNode2163 (p : Pattern) : NetHack.Sokoban22Refined85.d2163 p = d49762 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d1806 p) = d49762 p
  rw [oldNode12, oldNode1806]
  rfl
theorem oldNode2164 (p : Pattern) : NetHack.Sokoban22Refined85.d2164 p = d49763 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2163 p) = d49763 p
  rw [oldNode12, oldNode2163]
  rfl
theorem oldNode2165 (p : Pattern) : NetHack.Sokoban22Refined85.d2165 p = d49764 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2164 p else NetHack.Sokoban22Refined85.d2162 p) = d49764 p
  rw [oldNode2164, oldNode2162]
  rfl
theorem oldNode2166 (p : Pattern) : NetHack.Sokoban22Refined85.d2166 p = d49765 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2165 p else NetHack.Sokoban22Refined85.d2153 p) = d49765 p
  rw [oldNode2165, oldNode2153]
  rfl
theorem oldNode2167 (p : Pattern) : NetHack.Sokoban22Refined85.d2167 p = d49766 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2166 p else NetHack.Sokoban22Refined85.d2148 p) = d49766 p
  rw [oldNode2166, oldNode2148]
  rfl
theorem oldNode2168 (p : Pattern) : NetHack.Sokoban22Refined85.d2168 p = d49767 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1805 p else NetHack.Sokoban22Refined85.d1973 p) = d49767 p
  rw [oldNode1805, oldNode1973]
  rfl
theorem oldNode2169 (p : Pattern) : NetHack.Sokoban22Refined85.d2169 p = d49768 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2168 p else NetHack.Sokoban22Refined85.d2149 p) = d49768 p
  rw [oldNode2168, oldNode2149]
  rfl
theorem oldNode2170 (p : Pattern) : NetHack.Sokoban22Refined85.d2170 p = d49769 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1805 p else NetHack.Sokoban22Refined85.d1968 p) = d49769 p
  rw [oldNode1805, oldNode1968]
  rfl
theorem oldNode2171 (p : Pattern) : NetHack.Sokoban22Refined85.d2171 p = d49770 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2170 p) = d49770 p
  rw [oldNode12, oldNode2170]
  rfl
theorem oldNode2172 (p : Pattern) : NetHack.Sokoban22Refined85.d2172 p = d49771 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2171 p else NetHack.Sokoban22Refined85.d2169 p) = d49771 p
  rw [oldNode2171, oldNode2169]
  rfl
theorem oldNode2173 (p : Pattern) : NetHack.Sokoban22Refined85.d2173 p = d49772 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d1756 p else NetHack.Sokoban22Refined85.d1974 p) = d49772 p
  rw [oldNode1756, oldNode1974]
  rfl
theorem oldNode2174 (p : Pattern) : NetHack.Sokoban22Refined85.d2174 p = d49773 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2173 p) = d49773 p
  rw [oldNode12, oldNode2173]
  rfl
theorem oldNode2175 (p : Pattern) : NetHack.Sokoban22Refined85.d2175 p = d49774 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2174 p) = d49774 p
  rw [oldNode12, oldNode2174]
  rfl
theorem oldNode2176 (p : Pattern) : NetHack.Sokoban22Refined85.d2176 p = d49775 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2175 p else NetHack.Sokoban22Refined85.d2172 p) = d49775 p
  rw [oldNode2175, oldNode2172]
  rfl
theorem oldNode2177 (p : Pattern) : NetHack.Sokoban22Refined85.d2177 p = d49776 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2165 p else NetHack.Sokoban22Refined85.d2176 p) = d49776 p
  rw [oldNode2165, oldNode2176]
  rfl
theorem oldNode2178 (p : Pattern) : NetHack.Sokoban22Refined85.d2178 p = d49777 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2177 p) = d49777 p
  rw [oldNode12, oldNode2177]
  rfl
theorem oldNode2179 (p : Pattern) : NetHack.Sokoban22Refined85.d2179 p = d49778 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2178 p else NetHack.Sokoban22Refined85.d2167 p) = d49778 p
  rw [oldNode2178, oldNode2167]
  rfl
theorem oldNode2180 (p : Pattern) : NetHack.Sokoban22Refined85.d2180 p = d49779 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d2179 p else NetHack.Sokoban22Refined85.d2106 p) = d49779 p
  rw [oldNode2179, oldNode2106]
  rfl
theorem oldNode2181 (p : Pattern) : NetHack.Sokoban22Refined85.d2181 p = d49780 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d2180 p else NetHack.Sokoban22Refined85.d1849 p) = d49780 p
  rw [oldNode2180, oldNode1849]
  rfl
theorem oldNode2182 (p : Pattern) : NetHack.Sokoban22Refined85.d2182 p = d49781 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d2181 p else NetHack.Sokoban22Refined85.d2087 p) = d49781 p
  rw [oldNode2181, oldNode2087]
  rfl
theorem oldNode2183 (p : Pattern) : NetHack.Sokoban22Refined85.d2183 p = d49782 p := by
  change (if p 48 then NetHack.Sokoban22Refined85.d2182 p else NetHack.Sokoban22Refined85.d2010 p) = d49782 p
  rw [oldNode2182, oldNode2010]
  rfl
theorem oldNode2184 (p : Pattern) : NetHack.Sokoban22Refined85.d2184 p = d49783 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d318 p else NetHack.Sokoban22Refined85.d14 p) = d49783 p
  rw [oldNode318, oldNode14]
  rfl
theorem oldNode2185 (p : Pattern) : NetHack.Sokoban22Refined85.d2185 p = d49784 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d14 p) = d49784 p
  rw [oldNode12, oldNode14]
  rfl
theorem oldNode2186 (p : Pattern) : NetHack.Sokoban22Refined85.d2186 p = d49785 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2185 p else NetHack.Sokoban22Refined85.d2184 p) = d49785 p
  rw [oldNode2185, oldNode2184]
  rfl
theorem oldNode2187 (p : Pattern) : NetHack.Sokoban22Refined85.d2187 p = d49786 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2185 p) = d49786 p
  rw [oldNode12, oldNode2185]
  rfl
theorem oldNode2188 (p : Pattern) : NetHack.Sokoban22Refined85.d2188 p = d49787 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2186 p) = d49787 p
  rw [oldNode2187, oldNode2186]
  rfl
theorem oldNode2189 (p : Pattern) : NetHack.Sokoban22Refined85.d2189 p = d49788 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d330 p else NetHack.Sokoban22Refined85.d14 p) = d49788 p
  rw [oldNode330, oldNode14]
  rfl
theorem oldNode2190 (p : Pattern) : NetHack.Sokoban22Refined85.d2190 p = d49789 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2185 p else NetHack.Sokoban22Refined85.d2189 p) = d49789 p
  rw [oldNode2185, oldNode2189]
  rfl
theorem oldNode2191 (p : Pattern) : NetHack.Sokoban22Refined85.d2191 p = d49790 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2190 p) = d49790 p
  rw [oldNode2187, oldNode2190]
  rfl
theorem oldNode2192 (p : Pattern) : NetHack.Sokoban22Refined85.d2192 p = d49791 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2191 p else NetHack.Sokoban22Refined85.d2188 p) = d49791 p
  rw [oldNode2191, oldNode2188]
  rfl
theorem oldNode2193 (p : Pattern) : NetHack.Sokoban22Refined85.d2193 p = d49792 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d332 p else NetHack.Sokoban22Refined85.d14 p) = d49792 p
  rw [oldNode332, oldNode14]
  rfl
theorem oldNode2194 (p : Pattern) : NetHack.Sokoban22Refined85.d2194 p = d49793 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2185 p else NetHack.Sokoban22Refined85.d2193 p) = d49793 p
  rw [oldNode2185, oldNode2193]
  rfl
theorem oldNode2195 (p : Pattern) : NetHack.Sokoban22Refined85.d2195 p = d49794 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2194 p) = d49794 p
  rw [oldNode2187, oldNode2194]
  rfl
theorem oldNode2196 (p : Pattern) : NetHack.Sokoban22Refined85.d2196 p = d49795 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d18 p) = d49795 p
  rw [oldNode12, oldNode18]
  rfl
theorem oldNode2197 (p : Pattern) : NetHack.Sokoban22Refined85.d2197 p = d49796 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2196 p) = d49796 p
  rw [oldNode12, oldNode2196]
  rfl
theorem oldNode2198 (p : Pattern) : NetHack.Sokoban22Refined85.d2198 p = d49797 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2197 p else NetHack.Sokoban22Refined85.d2196 p) = d49797 p
  rw [oldNode2197, oldNode2196]
  rfl
theorem oldNode2199 (p : Pattern) : NetHack.Sokoban22Refined85.d2199 p = d49798 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2198 p else NetHack.Sokoban22Refined85.d2195 p) = d49798 p
  rw [oldNode2198, oldNode2195]
  rfl
theorem oldNode2200 (p : Pattern) : NetHack.Sokoban22Refined85.d2200 p = d49799 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2199 p else NetHack.Sokoban22Refined85.d2192 p) = d49799 p
  rw [oldNode2199, oldNode2192]
  rfl
theorem oldNode2201 (p : Pattern) : NetHack.Sokoban22Refined85.d2201 p = d49800 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2185 p) = d49800 p
  rw [oldNode2187, oldNode2185]
  rfl
theorem oldNode2202 (p : Pattern) : NetHack.Sokoban22Refined85.d2202 p = d49801 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2198 p else NetHack.Sokoban22Refined85.d2201 p) = d49801 p
  rw [oldNode2198, oldNode2201]
  rfl
theorem oldNode2203 (p : Pattern) : NetHack.Sokoban22Refined85.d2203 p = d49802 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d24 p) = d49802 p
  rw [oldNode12, oldNode24]
  rfl
theorem oldNode2204 (p : Pattern) : NetHack.Sokoban22Refined85.d2204 p = d49803 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2203 p) = d49803 p
  rw [oldNode12, oldNode2203]
  rfl
theorem oldNode2205 (p : Pattern) : NetHack.Sokoban22Refined85.d2205 p = d49804 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2204 p else NetHack.Sokoban22Refined85.d2203 p) = d49804 p
  rw [oldNode2204, oldNode2203]
  rfl
theorem oldNode2206 (p : Pattern) : NetHack.Sokoban22Refined85.d2206 p = d49805 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2205 p) = d49805 p
  rw [oldNode12, oldNode2205]
  rfl
theorem oldNode2207 (p : Pattern) : NetHack.Sokoban22Refined85.d2207 p = d49806 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2206 p else NetHack.Sokoban22Refined85.d2202 p) = d49806 p
  rw [oldNode2206, oldNode2202]
  rfl
theorem oldNode2208 (p : Pattern) : NetHack.Sokoban22Refined85.d2208 p = d49807 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2207 p else NetHack.Sokoban22Refined85.d2200 p) = d49807 p
  rw [oldNode2207, oldNode2200]
  rfl
theorem oldNode2209 (p : Pattern) : NetHack.Sokoban22Refined85.d2209 p = d49808 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d31 p) = d49808 p
  rw [oldNode12, oldNode31]
  rfl
theorem oldNode2210 (p : Pattern) : NetHack.Sokoban22Refined85.d2210 p = d49809 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2209 p) = d49809 p
  rw [oldNode12, oldNode2209]
  rfl
theorem oldNode2211 (p : Pattern) : NetHack.Sokoban22Refined85.d2211 p = d49810 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2210 p else NetHack.Sokoban22Refined85.d2185 p) = d49810 p
  rw [oldNode2210, oldNode2185]
  rfl
theorem oldNode2212 (p : Pattern) : NetHack.Sokoban22Refined85.d2212 p = d49811 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d35 p) = d49811 p
  rw [oldNode12, oldNode35]
  rfl
theorem oldNode2213 (p : Pattern) : NetHack.Sokoban22Refined85.d2213 p = d49812 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2212 p) = d49812 p
  rw [oldNode12, oldNode2212]
  rfl
theorem oldNode2214 (p : Pattern) : NetHack.Sokoban22Refined85.d2214 p = d49813 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2213 p else NetHack.Sokoban22Refined85.d2185 p) = d49813 p
  rw [oldNode2213, oldNode2185]
  rfl
theorem oldNode2215 (p : Pattern) : NetHack.Sokoban22Refined85.d2215 p = d49814 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2214 p else NetHack.Sokoban22Refined85.d2211 p) = d49814 p
  rw [oldNode2214, oldNode2211]
  rfl
theorem oldNode2216 (p : Pattern) : NetHack.Sokoban22Refined85.d2216 p = d49815 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d40 p) = d49815 p
  rw [oldNode12, oldNode40]
  rfl
theorem oldNode2217 (p : Pattern) : NetHack.Sokoban22Refined85.d2217 p = d49816 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2216 p) = d49816 p
  rw [oldNode12, oldNode2216]
  rfl
theorem oldNode2218 (p : Pattern) : NetHack.Sokoban22Refined85.d2218 p = d49817 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2217 p else NetHack.Sokoban22Refined85.d2185 p) = d49817 p
  rw [oldNode2217, oldNode2185]
  rfl
theorem oldNode2219 (p : Pattern) : NetHack.Sokoban22Refined85.d2219 p = d49818 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2196 p) = d49818 p
  rw [oldNode12, oldNode2196]
  rfl
theorem oldNode2220 (p : Pattern) : NetHack.Sokoban22Refined85.d2220 p = d49819 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2219 p else NetHack.Sokoban22Refined85.d2218 p) = d49819 p
  rw [oldNode2219, oldNode2218]
  rfl
theorem oldNode2221 (p : Pattern) : NetHack.Sokoban22Refined85.d2221 p = d49820 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2220 p else NetHack.Sokoban22Refined85.d2215 p) = d49820 p
  rw [oldNode2220, oldNode2215]
  rfl
theorem oldNode2222 (p : Pattern) : NetHack.Sokoban22Refined85.d2222 p = d49821 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2185 p) = d49821 p
  rw [oldNode12, oldNode2185]
  rfl
theorem oldNode2223 (p : Pattern) : NetHack.Sokoban22Refined85.d2223 p = d49822 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2219 p else NetHack.Sokoban22Refined85.d2222 p) = d49822 p
  rw [oldNode2219, oldNode2222]
  rfl
theorem oldNode2224 (p : Pattern) : NetHack.Sokoban22Refined85.d2224 p = d49823 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2203 p) = d49823 p
  rw [oldNode12, oldNode2203]
  rfl
theorem oldNode2225 (p : Pattern) : NetHack.Sokoban22Refined85.d2225 p = d49824 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2224 p) = d49824 p
  rw [oldNode12, oldNode2224]
  rfl
theorem oldNode2226 (p : Pattern) : NetHack.Sokoban22Refined85.d2226 p = d49825 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2225 p else NetHack.Sokoban22Refined85.d2223 p) = d49825 p
  rw [oldNode2225, oldNode2223]
  rfl
theorem oldNode2227 (p : Pattern) : NetHack.Sokoban22Refined85.d2227 p = d49826 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2226 p else NetHack.Sokoban22Refined85.d2221 p) = d49826 p
  rw [oldNode2226, oldNode2221]
  rfl
theorem oldNode2228 (p : Pattern) : NetHack.Sokoban22Refined85.d2228 p = d49827 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2227 p else NetHack.Sokoban22Refined85.d2208 p) = d49827 p
  rw [oldNode2227, oldNode2208]
  rfl
theorem oldNode2229 (p : Pattern) : NetHack.Sokoban22Refined85.d2229 p = d49828 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d357 p else NetHack.Sokoban22Refined85.d14 p) = d49828 p
  rw [oldNode357, oldNode14]
  rfl
theorem oldNode2230 (p : Pattern) : NetHack.Sokoban22Refined85.d2230 p = d49829 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2185 p else NetHack.Sokoban22Refined85.d2229 p) = d49829 p
  rw [oldNode2185, oldNode2229]
  rfl
theorem oldNode2231 (p : Pattern) : NetHack.Sokoban22Refined85.d2231 p = d49830 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2230 p) = d49830 p
  rw [oldNode2187, oldNode2230]
  rfl
theorem oldNode2232 (p : Pattern) : NetHack.Sokoban22Refined85.d2232 p = d49831 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2210 p else NetHack.Sokoban22Refined85.d2209 p) = d49831 p
  rw [oldNode2210, oldNode2209]
  rfl
theorem oldNode2233 (p : Pattern) : NetHack.Sokoban22Refined85.d2233 p = d49832 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2232 p else NetHack.Sokoban22Refined85.d2231 p) = d49832 p
  rw [oldNode2232, oldNode2231]
  rfl
theorem oldNode2234 (p : Pattern) : NetHack.Sokoban22Refined85.d2234 p = d49833 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2205 p else NetHack.Sokoban22Refined85.d2198 p) = d49833 p
  rw [oldNode2205, oldNode2198]
  rfl
theorem oldNode2235 (p : Pattern) : NetHack.Sokoban22Refined85.d2235 p = d49834 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2234 p else NetHack.Sokoban22Refined85.d2233 p) = d49834 p
  rw [oldNode2234, oldNode2233]
  rfl
theorem oldNode2236 (p : Pattern) : NetHack.Sokoban22Refined85.d2236 p = d49835 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d58 p) = d49835 p
  rw [oldNode12, oldNode58]
  rfl
theorem oldNode2237 (p : Pattern) : NetHack.Sokoban22Refined85.d2237 p = d49836 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2236 p) = d49836 p
  rw [oldNode12, oldNode2236]
  rfl
theorem oldNode2238 (p : Pattern) : NetHack.Sokoban22Refined85.d2238 p = d49837 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2237 p else NetHack.Sokoban22Refined85.d2236 p) = d49837 p
  rw [oldNode2237, oldNode2236]
  rfl
theorem oldNode2239 (p : Pattern) : NetHack.Sokoban22Refined85.d2239 p = d49838 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2238 p else NetHack.Sokoban22Refined85.d2198 p) = d49838 p
  rw [oldNode2238, oldNode2198]
  rfl
theorem oldNode2240 (p : Pattern) : NetHack.Sokoban22Refined85.d2240 p = d49839 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2217 p else NetHack.Sokoban22Refined85.d2216 p) = d49839 p
  rw [oldNode2217, oldNode2216]
  rfl
theorem oldNode2241 (p : Pattern) : NetHack.Sokoban22Refined85.d2241 p = d49840 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2240 p) = d49840 p
  rw [oldNode12, oldNode2240]
  rfl
theorem oldNode2242 (p : Pattern) : NetHack.Sokoban22Refined85.d2242 p = d49841 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2241 p else NetHack.Sokoban22Refined85.d2239 p) = d49841 p
  rw [oldNode2241, oldNode2239]
  rfl
theorem oldNode2243 (p : Pattern) : NetHack.Sokoban22Refined85.d2243 p = d49842 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2242 p else NetHack.Sokoban22Refined85.d2235 p) = d49842 p
  rw [oldNode2242, oldNode2235]
  rfl
theorem oldNode2244 (p : Pattern) : NetHack.Sokoban22Refined85.d2244 p = d49843 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2209 p) = d49843 p
  rw [oldNode12, oldNode2209]
  rfl
theorem oldNode2245 (p : Pattern) : NetHack.Sokoban22Refined85.d2245 p = d49844 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2244 p else NetHack.Sokoban22Refined85.d2214 p) = d49844 p
  rw [oldNode2244, oldNode2214]
  rfl
theorem oldNode2246 (p : Pattern) : NetHack.Sokoban22Refined85.d2246 p = d49845 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2224 p else NetHack.Sokoban22Refined85.d2219 p) = d49845 p
  rw [oldNode2224, oldNode2219]
  rfl
theorem oldNode2247 (p : Pattern) : NetHack.Sokoban22Refined85.d2247 p = d49846 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2246 p else NetHack.Sokoban22Refined85.d2245 p) = d49846 p
  rw [oldNode2246, oldNode2245]
  rfl
theorem oldNode2248 (p : Pattern) : NetHack.Sokoban22Refined85.d2248 p = d49847 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2236 p) = d49847 p
  rw [oldNode12, oldNode2236]
  rfl
theorem oldNode2249 (p : Pattern) : NetHack.Sokoban22Refined85.d2249 p = d49848 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2248 p else NetHack.Sokoban22Refined85.d2219 p) = d49848 p
  rw [oldNode2248, oldNode2219]
  rfl
theorem oldNode2250 (p : Pattern) : NetHack.Sokoban22Refined85.d2250 p = d49849 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2216 p) = d49849 p
  rw [oldNode12, oldNode2216]
  rfl
theorem oldNode2251 (p : Pattern) : NetHack.Sokoban22Refined85.d2251 p = d49850 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2250 p) = d49850 p
  rw [oldNode12, oldNode2250]
  rfl
theorem oldNode2252 (p : Pattern) : NetHack.Sokoban22Refined85.d2252 p = d49851 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2251 p else NetHack.Sokoban22Refined85.d2249 p) = d49851 p
  rw [oldNode2251, oldNode2249]
  rfl
theorem oldNode2253 (p : Pattern) : NetHack.Sokoban22Refined85.d2253 p = d49852 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2252 p else NetHack.Sokoban22Refined85.d2247 p) = d49852 p
  rw [oldNode2252, oldNode2247]
  rfl
theorem oldNode2254 (p : Pattern) : NetHack.Sokoban22Refined85.d2254 p = d49853 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2253 p else NetHack.Sokoban22Refined85.d2243 p) = d49853 p
  rw [oldNode2253, oldNode2243]
  rfl
theorem oldNode2255 (p : Pattern) : NetHack.Sokoban22Refined85.d2255 p = d49854 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2254 p else NetHack.Sokoban22Refined85.d2228 p) = d49854 p
  rw [oldNode2254, oldNode2228]
  rfl
theorem oldNode2256 (p : Pattern) : NetHack.Sokoban22Refined85.d2256 p = d49855 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2202 p else NetHack.Sokoban22Refined85.d2201 p) = d49855 p
  rw [oldNode2202, oldNode2201]
  rfl
theorem oldNode2257 (p : Pattern) : NetHack.Sokoban22Refined85.d2257 p = d49856 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2207 p else NetHack.Sokoban22Refined85.d2256 p) = d49856 p
  rw [oldNode2207, oldNode2256]
  rfl
theorem oldNode2258 (p : Pattern) : NetHack.Sokoban22Refined85.d2258 p = d49857 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2213 p else NetHack.Sokoban22Refined85.d2212 p) = d49857 p
  rw [oldNode2213, oldNode2212]
  rfl
theorem oldNode2259 (p : Pattern) : NetHack.Sokoban22Refined85.d2259 p = d49858 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2258 p else NetHack.Sokoban22Refined85.d2232 p) = d49858 p
  rw [oldNode2258, oldNode2232]
  rfl
theorem oldNode2260 (p : Pattern) : NetHack.Sokoban22Refined85.d2260 p = d49859 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2241 p else NetHack.Sokoban22Refined85.d2259 p) = d49859 p
  rw [oldNode2241, oldNode2259]
  rfl
theorem oldNode2261 (p : Pattern) : NetHack.Sokoban22Refined85.d2261 p = d49860 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2260 p) = d49860 p
  rw [oldNode12, oldNode2260]
  rfl
theorem oldNode2262 (p : Pattern) : NetHack.Sokoban22Refined85.d2262 p = d49861 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2261 p else NetHack.Sokoban22Refined85.d2257 p) = d49861 p
  rw [oldNode2261, oldNode2257]
  rfl
theorem oldNode2263 (p : Pattern) : NetHack.Sokoban22Refined85.d2263 p = d49862 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2232 p else NetHack.Sokoban22Refined85.d2201 p) = d49862 p
  rw [oldNode2232, oldNode2201]
  rfl
theorem oldNode2264 (p : Pattern) : NetHack.Sokoban22Refined85.d2264 p = d49863 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2234 p else NetHack.Sokoban22Refined85.d2263 p) = d49863 p
  rw [oldNode2234, oldNode2263]
  rfl
theorem oldNode2265 (p : Pattern) : NetHack.Sokoban22Refined85.d2265 p = d49864 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2242 p else NetHack.Sokoban22Refined85.d2264 p) = d49864 p
  rw [oldNode2242, oldNode2264]
  rfl
theorem oldNode2266 (p : Pattern) : NetHack.Sokoban22Refined85.d2266 p = d49865 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2258 p) = d49865 p
  rw [oldNode12, oldNode2258]
  rfl
theorem oldNode2267 (p : Pattern) : NetHack.Sokoban22Refined85.d2267 p = d49866 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2266 p) = d49866 p
  rw [oldNode12, oldNode2266]
  rfl
theorem oldNode2268 (p : Pattern) : NetHack.Sokoban22Refined85.d2268 p = d49867 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2267 p) = d49867 p
  rw [oldNode12, oldNode2267]
  rfl
theorem oldNode2269 (p : Pattern) : NetHack.Sokoban22Refined85.d2269 p = d49868 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2268 p else NetHack.Sokoban22Refined85.d2265 p) = d49868 p
  rw [oldNode2268, oldNode2265]
  rfl
theorem oldNode2270 (p : Pattern) : NetHack.Sokoban22Refined85.d2270 p = d49869 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2269 p else NetHack.Sokoban22Refined85.d2262 p) = d49869 p
  rw [oldNode2269, oldNode2262]
  rfl
theorem oldNode2271 (p : Pattern) : NetHack.Sokoban22Refined85.d2271 p = d49870 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2270 p else NetHack.Sokoban22Refined85.d2255 p) = d49870 p
  rw [oldNode2270, oldNode2255]
  rfl
theorem oldNode2272 (p : Pattern) : NetHack.Sokoban22Refined85.d2272 p = d49871 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2201 p else NetHack.Sokoban22Refined85.d2195 p) = d49871 p
  rw [oldNode2201, oldNode2195]
  rfl
theorem oldNode2273 (p : Pattern) : NetHack.Sokoban22Refined85.d2273 p = d49872 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2202 p else NetHack.Sokoban22Refined85.d2272 p) = d49872 p
  rw [oldNode2202, oldNode2272]
  rfl
theorem oldNode2274 (p : Pattern) : NetHack.Sokoban22Refined85.d2274 p = d49873 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2207 p else NetHack.Sokoban22Refined85.d2273 p) = d49873 p
  rw [oldNode2207, oldNode2273]
  rfl
theorem oldNode2275 (p : Pattern) : NetHack.Sokoban22Refined85.d2275 p = d49874 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2261 p else NetHack.Sokoban22Refined85.d2274 p) = d49874 p
  rw [oldNode2261, oldNode2274]
  rfl
theorem oldNode2276 (p : Pattern) : NetHack.Sokoban22Refined85.d2276 p = d49875 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2269 p else NetHack.Sokoban22Refined85.d2275 p) = d49875 p
  rw [oldNode2269, oldNode2275]
  rfl
theorem oldNode2277 (p : Pattern) : NetHack.Sokoban22Refined85.d2277 p = d49876 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2240 p else NetHack.Sokoban22Refined85.d2205 p) = d49876 p
  rw [oldNode2240, oldNode2205]
  rfl
theorem oldNode2278 (p : Pattern) : NetHack.Sokoban22Refined85.d2278 p = d49877 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2241 p else NetHack.Sokoban22Refined85.d2277 p) = d49877 p
  rw [oldNode2241, oldNode2277]
  rfl
theorem oldNode2279 (p : Pattern) : NetHack.Sokoban22Refined85.d2279 p = d49878 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2241 p) = d49878 p
  rw [oldNode12, oldNode2241]
  rfl
theorem oldNode2280 (p : Pattern) : NetHack.Sokoban22Refined85.d2280 p = d49879 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2279 p else NetHack.Sokoban22Refined85.d2278 p) = d49879 p
  rw [oldNode2279, oldNode2278]
  rfl
theorem oldNode2281 (p : Pattern) : NetHack.Sokoban22Refined85.d2281 p = d49880 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2279 p) = d49880 p
  rw [oldNode12, oldNode2279]
  rfl
theorem oldNode2282 (p : Pattern) : NetHack.Sokoban22Refined85.d2282 p = d49881 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2281 p else NetHack.Sokoban22Refined85.d2280 p) = d49881 p
  rw [oldNode2281, oldNode2280]
  rfl
theorem oldNode2283 (p : Pattern) : NetHack.Sokoban22Refined85.d2283 p = d49882 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2281 p) = d49882 p
  rw [oldNode12, oldNode2281]
  rfl
theorem oldNode2284 (p : Pattern) : NetHack.Sokoban22Refined85.d2284 p = d49883 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2283 p else NetHack.Sokoban22Refined85.d2282 p) = d49883 p
  rw [oldNode2283, oldNode2282]
  rfl
theorem oldNode2285 (p : Pattern) : NetHack.Sokoban22Refined85.d2285 p = d49884 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2284 p else NetHack.Sokoban22Refined85.d2276 p) = d49884 p
  rw [oldNode2284, oldNode2276]
  rfl
theorem oldNode2286 (p : Pattern) : NetHack.Sokoban22Refined85.d2286 p = d49885 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2285 p else NetHack.Sokoban22Refined85.d2271 p) = d49885 p
  rw [oldNode2285, oldNode2271]
  rfl
theorem oldNode2287 (p : Pattern) : NetHack.Sokoban22Refined85.d2287 p = d49886 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2201 p else NetHack.Sokoban22Refined85.d2191 p) = d49886 p
  rw [oldNode2201, oldNode2191]
  rfl
theorem oldNode2288 (p : Pattern) : NetHack.Sokoban22Refined85.d2288 p = d49887 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2202 p else NetHack.Sokoban22Refined85.d2287 p) = d49887 p
  rw [oldNode2202, oldNode2287]
  rfl
theorem oldNode2289 (p : Pattern) : NetHack.Sokoban22Refined85.d2289 p = d49888 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2207 p else NetHack.Sokoban22Refined85.d2288 p) = d49888 p
  rw [oldNode2207, oldNode2288]
  rfl
theorem oldNode2290 (p : Pattern) : NetHack.Sokoban22Refined85.d2290 p = d49889 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2227 p else NetHack.Sokoban22Refined85.d2289 p) = d49889 p
  rw [oldNode2227, oldNode2289]
  rfl
theorem oldNode2291 (p : Pattern) : NetHack.Sokoban22Refined85.d2291 p = d49890 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2253 p else NetHack.Sokoban22Refined85.d2265 p) = d49890 p
  rw [oldNode2253, oldNode2265]
  rfl
theorem oldNode2292 (p : Pattern) : NetHack.Sokoban22Refined85.d2292 p = d49891 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2291 p else NetHack.Sokoban22Refined85.d2290 p) = d49891 p
  rw [oldNode2291, oldNode2290]
  rfl
theorem oldNode2293 (p : Pattern) : NetHack.Sokoban22Refined85.d2293 p = d49892 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2270 p else NetHack.Sokoban22Refined85.d2292 p) = d49892 p
  rw [oldNode2270, oldNode2292]
  rfl
theorem oldNode2294 (p : Pattern) : NetHack.Sokoban22Refined85.d2294 p = d49893 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2270 p) = d49893 p
  rw [oldNode12, oldNode2270]
  rfl
theorem oldNode2295 (p : Pattern) : NetHack.Sokoban22Refined85.d2295 p = d49894 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2294 p else NetHack.Sokoban22Refined85.d2293 p) = d49894 p
  rw [oldNode2294, oldNode2293]
  rfl
theorem oldNode2296 (p : Pattern) : NetHack.Sokoban22Refined85.d2296 p = d49895 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d2295 p else NetHack.Sokoban22Refined85.d2286 p) = d49895 p
  rw [oldNode2295, oldNode2286]
  rfl
theorem oldNode2297 (p : Pattern) : NetHack.Sokoban22Refined85.d2297 p = d49896 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d320 p else NetHack.Sokoban22Refined85.d14 p) = d49896 p
  rw [oldNode320, oldNode14]
  rfl
theorem oldNode2298 (p : Pattern) : NetHack.Sokoban22Refined85.d2298 p = d49897 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2185 p else NetHack.Sokoban22Refined85.d2297 p) = d49897 p
  rw [oldNode2185, oldNode2297]
  rfl
theorem oldNode2299 (p : Pattern) : NetHack.Sokoban22Refined85.d2299 p = d49898 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2187 p else NetHack.Sokoban22Refined85.d2298 p) = d49898 p
  rw [oldNode2187, oldNode2298]
  rfl
theorem oldNode2300 (p : Pattern) : NetHack.Sokoban22Refined85.d2300 p = d49899 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2195 p else NetHack.Sokoban22Refined85.d2299 p) = d49899 p
  rw [oldNode2195, oldNode2299]
  rfl
theorem oldNode2301 (p : Pattern) : NetHack.Sokoban22Refined85.d2301 p = d49900 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2202 p else NetHack.Sokoban22Refined85.d2300 p) = d49900 p
  rw [oldNode2202, oldNode2300]
  rfl
theorem oldNode2302 (p : Pattern) : NetHack.Sokoban22Refined85.d2302 p = d49901 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2207 p else NetHack.Sokoban22Refined85.d2301 p) = d49901 p
  rw [oldNode2207, oldNode2301]
  rfl
theorem oldNode2303 (p : Pattern) : NetHack.Sokoban22Refined85.d2303 p = d49902 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2227 p else NetHack.Sokoban22Refined85.d2302 p) = d49902 p
  rw [oldNode2227, oldNode2302]
  rfl
theorem oldNode2304 (p : Pattern) : NetHack.Sokoban22Refined85.d2304 p = d49903 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2232 p else NetHack.Sokoban22Refined85.d2191 p) = d49903 p
  rw [oldNode2232, oldNode2191]
  rfl
theorem oldNode2305 (p : Pattern) : NetHack.Sokoban22Refined85.d2305 p = d49904 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2234 p else NetHack.Sokoban22Refined85.d2304 p) = d49904 p
  rw [oldNode2234, oldNode2304]
  rfl
theorem oldNode2306 (p : Pattern) : NetHack.Sokoban22Refined85.d2306 p = d49905 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2242 p else NetHack.Sokoban22Refined85.d2305 p) = d49905 p
  rw [oldNode2242, oldNode2305]
  rfl
theorem oldNode2307 (p : Pattern) : NetHack.Sokoban22Refined85.d2307 p = d49906 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2253 p else NetHack.Sokoban22Refined85.d2306 p) = d49906 p
  rw [oldNode2253, oldNode2306]
  rfl
theorem oldNode2308 (p : Pattern) : NetHack.Sokoban22Refined85.d2308 p = d49907 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2307 p else NetHack.Sokoban22Refined85.d2303 p) = d49907 p
  rw [oldNode2307, oldNode2303]
  rfl
theorem oldNode2309 (p : Pattern) : NetHack.Sokoban22Refined85.d2309 p = d49908 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2270 p else NetHack.Sokoban22Refined85.d2308 p) = d49908 p
  rw [oldNode2270, oldNode2308]
  rfl
theorem oldNode2310 (p : Pattern) : NetHack.Sokoban22Refined85.d2310 p = d49909 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2284 p else NetHack.Sokoban22Refined85.d2270 p) = d49909 p
  rw [oldNode2284, oldNode2270]
  rfl
theorem oldNode2311 (p : Pattern) : NetHack.Sokoban22Refined85.d2311 p = d49910 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2310 p else NetHack.Sokoban22Refined85.d2309 p) = d49910 p
  rw [oldNode2310, oldNode2309]
  rfl
theorem oldNode2312 (p : Pattern) : NetHack.Sokoban22Refined85.d2312 p = d49911 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2227 p else NetHack.Sokoban22Refined85.d2274 p) = d49911 p
  rw [oldNode2227, oldNode2274]
  rfl
theorem oldNode2313 (p : Pattern) : NetHack.Sokoban22Refined85.d2313 p = d49912 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2291 p else NetHack.Sokoban22Refined85.d2312 p) = d49912 p
  rw [oldNode2291, oldNode2312]
  rfl
theorem oldNode2314 (p : Pattern) : NetHack.Sokoban22Refined85.d2314 p = d49913 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2270 p else NetHack.Sokoban22Refined85.d2313 p) = d49913 p
  rw [oldNode2270, oldNode2313]
  rfl
theorem oldNode2315 (p : Pattern) : NetHack.Sokoban22Refined85.d2315 p = d49914 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2294 p else NetHack.Sokoban22Refined85.d2314 p) = d49914 p
  rw [oldNode2294, oldNode2314]
  rfl
theorem oldNode2316 (p : Pattern) : NetHack.Sokoban22Refined85.d2316 p = d49915 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d2315 p else NetHack.Sokoban22Refined85.d2311 p) = d49915 p
  rw [oldNode2315, oldNode2311]
  rfl
theorem oldNode2317 (p : Pattern) : NetHack.Sokoban22Refined85.d2317 p = d49916 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d2316 p else NetHack.Sokoban22Refined85.d2296 p) = d49916 p
  rw [oldNode2316, oldNode2296]
  rfl
theorem oldNode2318 (p : Pattern) : NetHack.Sokoban22Refined85.d2318 p = d49917 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d320 p else NetHack.Sokoban22Refined85.d103 p) = d49917 p
  rw [oldNode320, oldNode103]
  rfl
theorem oldNode2319 (p : Pattern) : NetHack.Sokoban22Refined85.d2319 p = d49918 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d103 p) = d49918 p
  rw [oldNode12, oldNode103]
  rfl
theorem oldNode2320 (p : Pattern) : NetHack.Sokoban22Refined85.d2320 p = d49919 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2319 p else NetHack.Sokoban22Refined85.d2318 p) = d49919 p
  rw [oldNode2319, oldNode2318]
  rfl
theorem oldNode2321 (p : Pattern) : NetHack.Sokoban22Refined85.d2321 p = d49920 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2319 p) = d49920 p
  rw [oldNode12, oldNode2319]
  rfl
theorem oldNode2322 (p : Pattern) : NetHack.Sokoban22Refined85.d2322 p = d49921 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2321 p else NetHack.Sokoban22Refined85.d2320 p) = d49921 p
  rw [oldNode2321, oldNode2320]
  rfl
theorem oldNode2323 (p : Pattern) : NetHack.Sokoban22Refined85.d2323 p = d49922 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d332 p else NetHack.Sokoban22Refined85.d103 p) = d49922 p
  rw [oldNode332, oldNode103]
  rfl
theorem oldNode2324 (p : Pattern) : NetHack.Sokoban22Refined85.d2324 p = d49923 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2319 p else NetHack.Sokoban22Refined85.d2323 p) = d49923 p
  rw [oldNode2319, oldNode2323]
  rfl
theorem oldNode2325 (p : Pattern) : NetHack.Sokoban22Refined85.d2325 p = d49924 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2321 p else NetHack.Sokoban22Refined85.d2324 p) = d49924 p
  rw [oldNode2321, oldNode2324]
  rfl
theorem oldNode2326 (p : Pattern) : NetHack.Sokoban22Refined85.d2326 p = d49925 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2325 p else NetHack.Sokoban22Refined85.d2322 p) = d49925 p
  rw [oldNode2325, oldNode2322]
  rfl
theorem oldNode2327 (p : Pattern) : NetHack.Sokoban22Refined85.d2327 p = d49926 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2321 p else NetHack.Sokoban22Refined85.d2319 p) = d49926 p
  rw [oldNode2321, oldNode2319]
  rfl
theorem oldNode2328 (p : Pattern) : NetHack.Sokoban22Refined85.d2328 p = d49927 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d107 p) = d49927 p
  rw [oldNode12, oldNode107]
  rfl
theorem oldNode2329 (p : Pattern) : NetHack.Sokoban22Refined85.d2329 p = d49928 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2328 p) = d49928 p
  rw [oldNode12, oldNode2328]
  rfl
theorem oldNode2330 (p : Pattern) : NetHack.Sokoban22Refined85.d2330 p = d49929 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2329 p else NetHack.Sokoban22Refined85.d2328 p) = d49929 p
  rw [oldNode2329, oldNode2328]
  rfl
theorem oldNode2331 (p : Pattern) : NetHack.Sokoban22Refined85.d2331 p = d49930 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2330 p else NetHack.Sokoban22Refined85.d2327 p) = d49930 p
  rw [oldNode2330, oldNode2327]
  rfl
theorem oldNode2332 (p : Pattern) : NetHack.Sokoban22Refined85.d2332 p = d49931 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2331 p else NetHack.Sokoban22Refined85.d2326 p) = d49931 p
  rw [oldNode2331, oldNode2326]
  rfl
theorem oldNode2333 (p : Pattern) : NetHack.Sokoban22Refined85.d2333 p = d49932 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2238 p) = d49932 p
  rw [oldNode12, oldNode2238]
  rfl
theorem oldNode2334 (p : Pattern) : NetHack.Sokoban22Refined85.d2334 p = d49933 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2333 p else NetHack.Sokoban22Refined85.d2331 p) = d49933 p
  rw [oldNode2333, oldNode2331]
  rfl
theorem oldNode2335 (p : Pattern) : NetHack.Sokoban22Refined85.d2335 p = d49934 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2334 p else NetHack.Sokoban22Refined85.d2332 p) = d49934 p
  rw [oldNode2334, oldNode2332]
  rfl
theorem oldNode2336 (p : Pattern) : NetHack.Sokoban22Refined85.d2336 p = d49935 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d116 p) = d49935 p
  rw [oldNode12, oldNode116]
  rfl
theorem oldNode2337 (p : Pattern) : NetHack.Sokoban22Refined85.d2337 p = d49936 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2336 p) = d49936 p
  rw [oldNode12, oldNode2336]
  rfl
theorem oldNode2338 (p : Pattern) : NetHack.Sokoban22Refined85.d2338 p = d49937 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2337 p else NetHack.Sokoban22Refined85.d2319 p) = d49937 p
  rw [oldNode2337, oldNode2319]
  rfl
theorem oldNode2339 (p : Pattern) : NetHack.Sokoban22Refined85.d2339 p = d49938 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d120 p) = d49938 p
  rw [oldNode12, oldNode120]
  rfl
theorem oldNode2340 (p : Pattern) : NetHack.Sokoban22Refined85.d2340 p = d49939 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2339 p) = d49939 p
  rw [oldNode12, oldNode2339]
  rfl
theorem oldNode2341 (p : Pattern) : NetHack.Sokoban22Refined85.d2341 p = d49940 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2340 p else NetHack.Sokoban22Refined85.d2319 p) = d49940 p
  rw [oldNode2340, oldNode2319]
  rfl
theorem oldNode2342 (p : Pattern) : NetHack.Sokoban22Refined85.d2342 p = d49941 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2341 p else NetHack.Sokoban22Refined85.d2338 p) = d49941 p
  rw [oldNode2341, oldNode2338]
  rfl
theorem oldNode2343 (p : Pattern) : NetHack.Sokoban22Refined85.d2343 p = d49942 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2319 p) = d49942 p
  rw [oldNode12, oldNode2319]
  rfl
theorem oldNode2344 (p : Pattern) : NetHack.Sokoban22Refined85.d2344 p = d49943 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2328 p) = d49943 p
  rw [oldNode12, oldNode2328]
  rfl
theorem oldNode2345 (p : Pattern) : NetHack.Sokoban22Refined85.d2345 p = d49944 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2344 p else NetHack.Sokoban22Refined85.d2343 p) = d49944 p
  rw [oldNode2344, oldNode2343]
  rfl
theorem oldNode2346 (p : Pattern) : NetHack.Sokoban22Refined85.d2346 p = d49945 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2345 p else NetHack.Sokoban22Refined85.d2342 p) = d49945 p
  rw [oldNode2345, oldNode2342]
  rfl
theorem oldNode2347 (p : Pattern) : NetHack.Sokoban22Refined85.d2347 p = d49946 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2248 p) = d49946 p
  rw [oldNode12, oldNode2248]
  rfl
theorem oldNode2348 (p : Pattern) : NetHack.Sokoban22Refined85.d2348 p = d49947 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2347 p else NetHack.Sokoban22Refined85.d2345 p) = d49947 p
  rw [oldNode2347, oldNode2345]
  rfl
theorem oldNode2349 (p : Pattern) : NetHack.Sokoban22Refined85.d2349 p = d49948 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2348 p else NetHack.Sokoban22Refined85.d2346 p) = d49948 p
  rw [oldNode2348, oldNode2346]
  rfl
theorem oldNode2350 (p : Pattern) : NetHack.Sokoban22Refined85.d2350 p = d49949 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2349 p else NetHack.Sokoban22Refined85.d2335 p) = d49949 p
  rw [oldNode2349, oldNode2335]
  rfl
theorem oldNode2351 (p : Pattern) : NetHack.Sokoban22Refined85.d2351 p = d49950 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d330 p else NetHack.Sokoban22Refined85.d103 p) = d49950 p
  rw [oldNode330, oldNode103]
  rfl
theorem oldNode2352 (p : Pattern) : NetHack.Sokoban22Refined85.d2352 p = d49951 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d2319 p else NetHack.Sokoban22Refined85.d2351 p) = d49951 p
  rw [oldNode2319, oldNode2351]
  rfl
theorem oldNode2353 (p : Pattern) : NetHack.Sokoban22Refined85.d2353 p = d49952 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2321 p else NetHack.Sokoban22Refined85.d2352 p) = d49952 p
  rw [oldNode2321, oldNode2352]
  rfl
theorem oldNode2354 (p : Pattern) : NetHack.Sokoban22Refined85.d2354 p = d49953 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2337 p else NetHack.Sokoban22Refined85.d2336 p) = d49953 p
  rw [oldNode2337, oldNode2336]
  rfl
theorem oldNode2355 (p : Pattern) : NetHack.Sokoban22Refined85.d2355 p = d49954 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2354 p else NetHack.Sokoban22Refined85.d2353 p) = d49954 p
  rw [oldNode2354, oldNode2353]
  rfl
theorem oldNode2356 (p : Pattern) : NetHack.Sokoban22Refined85.d2356 p = d49955 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2238 p else NetHack.Sokoban22Refined85.d2330 p) = d49955 p
  rw [oldNode2238, oldNode2330]
  rfl
theorem oldNode2357 (p : Pattern) : NetHack.Sokoban22Refined85.d2357 p = d49956 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2356 p else NetHack.Sokoban22Refined85.d2355 p) = d49956 p
  rw [oldNode2356, oldNode2355]
  rfl
theorem oldNode2358 (p : Pattern) : NetHack.Sokoban22Refined85.d2358 p = d49957 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2240 p else NetHack.Sokoban22Refined85.d2330 p) = d49957 p
  rw [oldNode2240, oldNode2330]
  rfl
theorem oldNode2359 (p : Pattern) : NetHack.Sokoban22Refined85.d2359 p = d49958 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2358 p) = d49958 p
  rw [oldNode12, oldNode2358]
  rfl
theorem oldNode2360 (p : Pattern) : NetHack.Sokoban22Refined85.d2360 p = d49959 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2359 p else NetHack.Sokoban22Refined85.d2357 p) = d49959 p
  rw [oldNode2359, oldNode2357]
  rfl
theorem oldNode2361 (p : Pattern) : NetHack.Sokoban22Refined85.d2361 p = d49960 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2336 p) = d49960 p
  rw [oldNode12, oldNode2336]
  rfl
theorem oldNode2362 (p : Pattern) : NetHack.Sokoban22Refined85.d2362 p = d49961 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2361 p else NetHack.Sokoban22Refined85.d2341 p) = d49961 p
  rw [oldNode2361, oldNode2341]
  rfl
theorem oldNode2363 (p : Pattern) : NetHack.Sokoban22Refined85.d2363 p = d49962 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2248 p else NetHack.Sokoban22Refined85.d2344 p) = d49962 p
  rw [oldNode2248, oldNode2344]
  rfl
theorem oldNode2364 (p : Pattern) : NetHack.Sokoban22Refined85.d2364 p = d49963 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2363 p else NetHack.Sokoban22Refined85.d2362 p) = d49963 p
  rw [oldNode2363, oldNode2362]
  rfl
theorem oldNode2365 (p : Pattern) : NetHack.Sokoban22Refined85.d2365 p = d49964 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2250 p else NetHack.Sokoban22Refined85.d2344 p) = d49964 p
  rw [oldNode2250, oldNode2344]
  rfl
theorem oldNode2366 (p : Pattern) : NetHack.Sokoban22Refined85.d2366 p = d49965 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2365 p) = d49965 p
  rw [oldNode12, oldNode2365]
  rfl
theorem oldNode2367 (p : Pattern) : NetHack.Sokoban22Refined85.d2367 p = d49966 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2366 p else NetHack.Sokoban22Refined85.d2364 p) = d49966 p
  rw [oldNode2366, oldNode2364]
  rfl
theorem oldNode2368 (p : Pattern) : NetHack.Sokoban22Refined85.d2368 p = d49967 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2367 p else NetHack.Sokoban22Refined85.d2360 p) = d49967 p
  rw [oldNode2367, oldNode2360]
  rfl
theorem oldNode2369 (p : Pattern) : NetHack.Sokoban22Refined85.d2369 p = d49968 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2368 p else NetHack.Sokoban22Refined85.d2350 p) = d49968 p
  rw [oldNode2368, oldNode2350]
  rfl
theorem oldNode2370 (p : Pattern) : NetHack.Sokoban22Refined85.d2370 p = d49969 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2331 p else NetHack.Sokoban22Refined85.d2327 p) = d49969 p
  rw [oldNode2331, oldNode2327]
  rfl
theorem oldNode2371 (p : Pattern) : NetHack.Sokoban22Refined85.d2371 p = d49970 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2334 p else NetHack.Sokoban22Refined85.d2370 p) = d49970 p
  rw [oldNode2334, oldNode2370]
  rfl
theorem oldNode2372 (p : Pattern) : NetHack.Sokoban22Refined85.d2372 p = d49971 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d2340 p else NetHack.Sokoban22Refined85.d2339 p) = d49971 p
  rw [oldNode2340, oldNode2339]
  rfl
theorem oldNode2373 (p : Pattern) : NetHack.Sokoban22Refined85.d2373 p = d49972 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2372 p else NetHack.Sokoban22Refined85.d2354 p) = d49972 p
  rw [oldNode2372, oldNode2354]
  rfl
theorem oldNode2374 (p : Pattern) : NetHack.Sokoban22Refined85.d2374 p = d49973 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2373 p) = d49973 p
  rw [oldNode12, oldNode2373]
  rfl
theorem oldNode2375 (p : Pattern) : NetHack.Sokoban22Refined85.d2375 p = d49974 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2374 p) = d49974 p
  rw [oldNode12, oldNode2374]
  rfl
theorem oldNode2376 (p : Pattern) : NetHack.Sokoban22Refined85.d2376 p = d49975 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2375 p else NetHack.Sokoban22Refined85.d2371 p) = d49975 p
  rw [oldNode2375, oldNode2371]
  rfl
theorem oldNode2377 (p : Pattern) : NetHack.Sokoban22Refined85.d2377 p = d49976 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2354 p else NetHack.Sokoban22Refined85.d2327 p) = d49976 p
  rw [oldNode2354, oldNode2327]
  rfl
theorem oldNode2378 (p : Pattern) : NetHack.Sokoban22Refined85.d2378 p = d49977 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2356 p else NetHack.Sokoban22Refined85.d2377 p) = d49977 p
  rw [oldNode2356, oldNode2377]
  rfl
theorem oldNode2379 (p : Pattern) : NetHack.Sokoban22Refined85.d2379 p = d49978 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2359 p else NetHack.Sokoban22Refined85.d2378 p) = d49978 p
  rw [oldNode2359, oldNode2378]
  rfl
theorem oldNode2380 (p : Pattern) : NetHack.Sokoban22Refined85.d2380 p = d49979 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2372 p) = d49979 p
  rw [oldNode12, oldNode2372]
  rfl
theorem oldNode2381 (p : Pattern) : NetHack.Sokoban22Refined85.d2381 p = d49980 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2380 p) = d49980 p
  rw [oldNode12, oldNode2380]
  rfl
theorem oldNode2382 (p : Pattern) : NetHack.Sokoban22Refined85.d2382 p = d49981 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2381 p) = d49981 p
  rw [oldNode12, oldNode2381]
  rfl
theorem oldNode2383 (p : Pattern) : NetHack.Sokoban22Refined85.d2383 p = d49982 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2382 p else NetHack.Sokoban22Refined85.d2379 p) = d49982 p
  rw [oldNode2382, oldNode2379]
  rfl
theorem oldNode2384 (p : Pattern) : NetHack.Sokoban22Refined85.d2384 p = d49983 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2383 p else NetHack.Sokoban22Refined85.d2376 p) = d49983 p
  rw [oldNode2383, oldNode2376]
  rfl
theorem oldNode2385 (p : Pattern) : NetHack.Sokoban22Refined85.d2385 p = d49984 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2384 p else NetHack.Sokoban22Refined85.d2369 p) = d49984 p
  rw [oldNode2384, oldNode2369]
  rfl
theorem oldNode2386 (p : Pattern) : NetHack.Sokoban22Refined85.d2386 p = d49985 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2333 p) = d49985 p
  rw [oldNode12, oldNode2333]
  rfl
theorem oldNode2387 (p : Pattern) : NetHack.Sokoban22Refined85.d2387 p = d49986 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2386 p) = d49986 p
  rw [oldNode12, oldNode2386]
  rfl
theorem oldNode2388 (p : Pattern) : NetHack.Sokoban22Refined85.d2388 p = d49987 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2387 p) = d49987 p
  rw [oldNode12, oldNode2387]
  rfl
theorem oldNode2389 (p : Pattern) : NetHack.Sokoban22Refined85.d2389 p = d49988 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2388 p) = d49988 p
  rw [oldNode12, oldNode2388]
  rfl
theorem oldNode2390 (p : Pattern) : NetHack.Sokoban22Refined85.d2390 p = d49989 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2389 p else NetHack.Sokoban22Refined85.d2384 p) = d49989 p
  rw [oldNode2389, oldNode2384]
  rfl
theorem oldNode2391 (p : Pattern) : NetHack.Sokoban22Refined85.d2391 p = d49990 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d2390 p else NetHack.Sokoban22Refined85.d2385 p) = d49990 p
  rw [oldNode2390, oldNode2385]
  rfl
theorem oldNode2392 (p : Pattern) : NetHack.Sokoban22Refined85.d2392 p = d49991 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d2327 p else NetHack.Sokoban22Refined85.d2325 p) = d49991 p
  rw [oldNode2327, oldNode2325]
  rfl
theorem oldNode2393 (p : Pattern) : NetHack.Sokoban22Refined85.d2393 p = d49992 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d2331 p else NetHack.Sokoban22Refined85.d2392 p) = d49992 p
  rw [oldNode2331, oldNode2392]
  rfl
theorem oldNode2394 (p : Pattern) : NetHack.Sokoban22Refined85.d2394 p = d49993 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d2334 p else NetHack.Sokoban22Refined85.d2393 p) = d49993 p
  rw [oldNode2334, oldNode2393]
  rfl
theorem oldNode2395 (p : Pattern) : NetHack.Sokoban22Refined85.d2395 p = d49994 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2349 p else NetHack.Sokoban22Refined85.d2394 p) = d49994 p
  rw [oldNode2349, oldNode2394]
  rfl
theorem oldNode2396 (p : Pattern) : NetHack.Sokoban22Refined85.d2396 p = d49995 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d2367 p else NetHack.Sokoban22Refined85.d2379 p) = d49995 p
  rw [oldNode2367, oldNode2379]
  rfl
theorem oldNode2397 (p : Pattern) : NetHack.Sokoban22Refined85.d2397 p = d49996 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d2396 p else NetHack.Sokoban22Refined85.d2395 p) = d49996 p
  rw [oldNode2396, oldNode2395]
  rfl
theorem oldNode2398 (p : Pattern) : NetHack.Sokoban22Refined85.d2398 p = d49997 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d2384 p else NetHack.Sokoban22Refined85.d2397 p) = d49997 p
  rw [oldNode2384, oldNode2397]
  rfl
theorem oldNode2399 (p : Pattern) : NetHack.Sokoban22Refined85.d2399 p = d49998 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d2384 p) = d49998 p
  rw [oldNode12, oldNode2384]
  rfl
end NetHack.Soko22Hazard87
