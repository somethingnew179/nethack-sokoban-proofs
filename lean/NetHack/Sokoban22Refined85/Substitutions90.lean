/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions89
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10800 (p : Pattern) : d2025 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d2022 (change p 204 (some 182)) else d1760 (change p 204 (some 182))) = d12 p
  rw [sub10797, sub10518]
  simp only [ite_self]
theorem sub10801 (p : Pattern) : d2026 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d539 (change p 204 (some 182)) else d2025 (change p 204 (some 182))) = d12 p
  rw [sub10525, sub10800]
  simp only [ite_self]
theorem sub10802 (p : Pattern) : d2027 (change p 204 (some 182)) = d5864 p := by
  change (if p 161 then d2026 (change p 204 (some 182)) else d2024 (change p 204 (some 182))) = d5864 p
  rw [sub10801, sub10799]
  rfl
theorem sub10803 (p : Pattern) : d2028 (change p 204 (some 182)) = d5956 p := by
  change (if p 160 then d2027 (change p 204 (some 182)) else d2018 (change p 204 (some 182))) = d5956 p
  rw [sub10802, sub10793]
  rfl
theorem sub10804 (p : Pattern) : d2029 (change p 204 (some 182)) = d2029 p := by
  change (if p 225 then d1714 (change p 204 (some 182)) else d31 (change p 204 (some 182))) = d2029 p
  rw [sub10463, sub10456]
  rfl
theorem sub10805 (p : Pattern) : d2030 (change p 204 (some 182)) = d2030 p := by
  change (if p 224 then d1714 (change p 204 (some 182)) else d2029 (change p 204 (some 182))) = d2030 p
  rw [sub10463, sub10804]
  rfl
theorem sub10806 (p : Pattern) : d2031 (change p 204 (some 182)) = d2030 p := by
  change d2030 (change p 204 (some 182)) = d2030 p
  exact sub10805 p
theorem sub10807 (p : Pattern) : d2032 (change p 204 (some 182)) = d2030 p := by
  change d2031 (change p 204 (some 182)) = d2030 p
  exact sub10806 p
theorem sub10808 (p : Pattern) : d2033 (change p 204 (some 182)) = d5957 p := by
  change (if p 163 then d2032 (change p 204 (some 182)) else d1774 (change p 204 (some 182))) = d5957 p
  rw [sub10807, sub10535]
  rfl
theorem sub10809 (p : Pattern) : d2034 (change p 204 (some 182)) = d5958 p := by
  change (if p 163 then d1805 (change p 204 (some 182)) else d2014 (change p 204 (some 182))) = d5958 p
  rw [sub10568, sub10789]
  rfl
theorem sub10810 (p : Pattern) : d2035 (change p 204 (some 182)) = d5959 p := by
  change (if p 162 then d2034 (change p 204 (some 182)) else d2033 (change p 204 (some 182))) = d5959 p
  rw [sub10809, sub10808]
  rfl
theorem sub10811 (p : Pattern) : d2036 (change p 204 (some 182)) = d5960 p := by
  change (if p 163 then d1754 (change p 204 (some 182)) else d2014 (change p 204 (some 182))) = d5960 p
  rw [sub10512, sub10789]
  rfl
theorem sub10812 (p : Pattern) : d2037 (change p 204 (some 182)) = d5961 p := by
  change (if p 162 then d1757 (change p 204 (some 182)) else d2036 (change p 204 (some 182))) = d5961 p
  rw [sub10515, sub10811]
  rfl
theorem sub10813 (p : Pattern) : d2038 (change p 204 (some 182)) = d5962 p := by
  change (if p 161 then d2037 (change p 204 (some 182)) else d2035 (change p 204 (some 182))) = d5962 p
  rw [sub10812, sub10810]
  rfl
theorem sub10814 (p : Pattern) : d2039 (change p 204 (some 182)) = d5872 p := by
  change (if p 163 then d1732 (change p 204 (some 182)) else d2019 (change p 204 (some 182))) = d5872 p
  rw [sub10487, sub10794]
  rfl
theorem sub10815 (p : Pattern) : d2040 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d538 (change p 204 (some 182)) else d2022 (change p 204 (some 182))) = d12 p
  rw [sub10524, sub10797]
  simp only [ite_self]
theorem sub10816 (p : Pattern) : d2041 (change p 204 (some 182)) = d5873 p := by
  change (if p 162 then d2040 (change p 204 (some 182)) else d2039 (change p 204 (some 182))) = d5873 p
  rw [sub10815, sub10814]
  rfl
theorem sub10817 (p : Pattern) : d2042 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d2022 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10797]
  simp only [ite_self]
theorem sub10818 (p : Pattern) : d2043 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2042 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10817]
  simp only [ite_self]
theorem sub10819 (p : Pattern) : d2044 (change p 204 (some 182)) = d5874 p := by
  change (if p 161 then d2043 (change p 204 (some 182)) else d2041 (change p 204 (some 182))) = d5874 p
  rw [sub10818, sub10816]
  rfl
theorem sub10820 (p : Pattern) : d2045 (change p 204 (some 182)) = d5963 p := by
  change (if p 160 then d2044 (change p 204 (some 182)) else d2038 (change p 204 (some 182))) = d5963 p
  rw [sub10819, sub10813]
  rfl
theorem sub10821 (p : Pattern) : d2046 (change p 204 (some 182)) = d5964 p := by
  change (if p 141 then d2045 (change p 204 (some 182)) else d2028 (change p 204 (some 182))) = d5964 p
  rw [sub10820, sub10803]
  rfl
theorem sub10822 (p : Pattern) : d2047 (change p 204 (some 182)) = d2047 p := by
  change (if p 225 then d1776 (change p 204 (some 182)) else d1770 (change p 204 (some 182))) = d2047 p
  rw [sub10537, sub10531]
  rfl
theorem sub10823 (p : Pattern) : d2048 (change p 204 (some 182)) = d2048 p := by
  change (if p 224 then d2047 (change p 204 (some 182)) else d1777 (change p 204 (some 182))) = d2048 p
  rw [sub10822, sub10538]
  rfl
theorem sub10824 (p : Pattern) : d2049 (change p 204 (some 182)) = d2048 p := by
  change d2048 (change p 204 (some 182)) = d2048 p
  exact sub10823 p
theorem sub10825 (p : Pattern) : d2050 (change p 204 (some 182)) = d2048 p := by
  change d2049 (change p 204 (some 182)) = d2048 p
  exact sub10824 p
theorem sub10826 (p : Pattern) : d2051 (change p 204 (some 182)) = d2051 p := by
  change (if p 247 then d10 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d2051 p
  rw [sub10472, sub10414]
  rfl
theorem sub10827 (p : Pattern) : d2052 (change p 204 (some 182)) = d2052 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d2051 (change p 204 (some 182))) = d2052 p
  rw [sub10443, sub10826]
  rfl
theorem sub10828 (p : Pattern) : d2053 (change p 204 (some 182)) = d2053 p := by
  change (if p 225 then d2052 (change p 204 (some 182)) else d1770 (change p 204 (some 182))) = d2053 p
  rw [sub10827, sub10531]
  rfl
theorem sub10829 (p : Pattern) : d2054 (change p 204 (some 182)) = d2054 p := by
  change (if p 224 then d2053 (change p 204 (some 182)) else d1777 (change p 204 (some 182))) = d2054 p
  rw [sub10828, sub10538]
  rfl
theorem sub10830 (p : Pattern) : d2055 (change p 204 (some 182)) = d2054 p := by
  change d2054 (change p 204 (some 182)) = d2054 p
  exact sub10829 p
theorem sub10831 (p : Pattern) : d2056 (change p 204 (some 182)) = d2054 p := by
  change d2055 (change p 204 (some 182)) = d2054 p
  exact sub10830 p
theorem sub10832 (p : Pattern) : d2057 (change p 204 (some 182)) = d5965 p := by
  change (if p 163 then d2056 (change p 204 (some 182)) else d2050 (change p 204 (some 182))) = d5965 p
  rw [sub10831, sub10825]
  rfl
theorem sub10833 (p : Pattern) : d2058 (change p 204 (some 182)) = d5966 p := by
  change (if p 162 then d1811 (change p 204 (some 182)) else d2057 (change p 204 (some 182))) = d5966 p
  rw [sub10574, sub10832]
  rfl
theorem sub10834 (p : Pattern) : d2059 (change p 204 (some 182)) = d5967 p := by
  change (if p 161 then d1812 (change p 204 (some 182)) else d2058 (change p 204 (some 182))) = d5967 p
  rw [sub10575, sub10833]
  rfl
theorem sub10835 (p : Pattern) : d191 (change p 204 (some 182)) = d191 p := by
  change (if p 246 then d190 (change p 204 (some 182)) else d8 (change p 204 (some 182))) = d191 p
  rw [sub10459, sub10457]
  rfl
theorem sub10836 (p : Pattern) : d315 (change p 204 (some 182)) = d315 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d190 (change p 204 (some 182))) = d315 p
  rw [sub10415, sub10459]
  rfl
theorem sub10837 (p : Pattern) : d2060 (change p 204 (some 182)) = d2060 p := by
  change (if p 225 then d315 (change p 204 (some 182)) else d191 (change p 204 (some 182))) = d2060 p
  rw [sub10836, sub10835]
  rfl
theorem sub10838 (p : Pattern) : d2061 (change p 204 (some 182)) = d2061 p := by
  change (if p 224 then d315 (change p 204 (some 182)) else d2060 (change p 204 (some 182))) = d2061 p
  rw [sub10836, sub10837]
  rfl
theorem sub10839 (p : Pattern) : d2062 (change p 204 (some 182)) = d2061 p := by
  change d2061 (change p 204 (some 182)) = d2061 p
  exact sub10838 p
theorem sub10840 (p : Pattern) : d2063 (change p 204 (some 182)) = d2061 p := by
  change d2062 (change p 204 (some 182)) = d2061 p
  exact sub10839 p
theorem sub10841 (p : Pattern) : d2064 (change p 204 (some 182)) = d5968 p := by
  change (if p 163 then d2063 (change p 204 (some 182)) else d1799 (change p 204 (some 182))) = d5968 p
  rw [sub10840, sub10561]
  rfl
theorem sub10842 (p : Pattern) : d2065 (change p 204 (some 182)) = d5969 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2064 (change p 204 (some 182))) = d5969 p
  rw [sub10415, sub10841]
  rfl
theorem sub10843 (p : Pattern) : d2066 (change p 204 (some 182)) = d5970 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d2065 (change p 204 (some 182))) = d5970 p
  rw [sub10415, sub10842]
  rfl
theorem sub10844 (p : Pattern) : d2067 (change p 204 (some 182)) = d5971 p := by
  change (if p 160 then d2066 (change p 204 (some 182)) else d2059 (change p 204 (some 182))) = d5971 p
  rw [sub10843, sub10834]
  rfl
theorem sub10845 (p : Pattern) : d2068 (change p 204 (some 182)) = d2068 p := by
  change (if p 247 then d10 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d2068 p
  rw [sub10472, sub10418]
  rfl
theorem sub10846 (p : Pattern) : d2069 (change p 204 (some 182)) = d2069 p := by
  change (if p 246 then d57 (change p 204 (some 182)) else d2068 (change p 204 (some 182))) = d2069 p
  rw [sub10474, sub10845]
  rfl
theorem sub10847 (p : Pattern) : d2070 (change p 204 (some 182)) = d2070 p := by
  change (if p 225 then d2069 (change p 204 (some 182)) else d1714 (change p 204 (some 182))) = d2070 p
  rw [sub10846, sub10463]
  rfl
theorem sub10848 (p : Pattern) : d2071 (change p 204 (some 182)) = d2071 p := by
  change (if p 224 then d2070 (change p 204 (some 182)) else d1712 (change p 204 (some 182))) = d2071 p
  rw [sub10847, sub10461]
  rfl
theorem sub10849 (p : Pattern) : d2072 (change p 204 (some 182)) = d2071 p := by
  change d2071 (change p 204 (some 182)) = d2071 p
  exact sub10848 p
theorem sub10850 (p : Pattern) : d2073 (change p 204 (some 182)) = d2071 p := by
  change d2072 (change p 204 (some 182)) = d2071 p
  exact sub10849 p
theorem sub10851 (p : Pattern) : d2074 (change p 204 (some 182)) = d5972 p := by
  change (if p 163 then d1809 (change p 204 (some 182)) else d2073 (change p 204 (some 182))) = d5972 p
  rw [sub10572, sub10850]
  rfl
theorem sub10852 (p : Pattern) : d2075 (change p 204 (some 182)) = d5973 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1799 (change p 204 (some 182))) = d5973 p
  rw [sub10514, sub10561]
  rfl
theorem sub10853 (p : Pattern) : d2076 (change p 204 (some 182)) = d5974 p := by
  change (if p 162 then d2075 (change p 204 (some 182)) else d2074 (change p 204 (some 182))) = d5974 p
  rw [sub10852, sub10851]
  rfl
theorem sub10854 (p : Pattern) : d2077 (change p 204 (some 182)) = d5975 p := by
  change (if p 161 then d1822 (change p 204 (some 182)) else d2076 (change p 204 (some 182))) = d5975 p
  rw [sub10585, sub10853]
  rfl
theorem sub10855 (p : Pattern) : d2078 (change p 204 (some 182)) = d5976 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d2063 (change p 204 (some 182))) = d5976 p
  rw [sub10415, sub10840]
  rfl
theorem sub10856 (p : Pattern) : d2079 (change p 204 (some 182)) = d5977 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2078 (change p 204 (some 182))) = d5977 p
  rw [sub10415, sub10855]
  rfl
theorem sub10857 (p : Pattern) : d2080 (change p 204 (some 182)) = d5978 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d2079 (change p 204 (some 182))) = d5978 p
  rw [sub10415, sub10856]
  rfl
theorem sub10858 (p : Pattern) : d2081 (change p 204 (some 182)) = d5979 p := by
  change (if p 160 then d2080 (change p 204 (some 182)) else d2077 (change p 204 (some 182))) = d5979 p
  rw [sub10857, sub10854]
  rfl
theorem sub10859 (p : Pattern) : d2082 (change p 204 (some 182)) = d5980 p := by
  change (if p 141 then d2081 (change p 204 (some 182)) else d2067 (change p 204 (some 182))) = d5980 p
  rw [sub10858, sub10844]
  rfl
theorem sub10860 (p : Pattern) : d2083 (change p 204 (some 182)) = d5981 p := by
  change (if p 138 then d2082 (change p 204 (some 182)) else d2046 (change p 204 (some 182))) = d5981 p
  rw [sub10859, sub10821]
  rfl
theorem sub10861 (p : Pattern) : d2084 (change p 204 (some 182)) = d5982 p := by
  change (if p 138 then d12 (change p 204 (some 182)) else d2082 (change p 204 (some 182))) = d5982 p
  rw [sub10415, sub10859]
  rfl
theorem sub10862 (p : Pattern) : d2085 (change p 204 (some 182)) = d5983 p := by
  change (if p 116 then d2084 (change p 204 (some 182)) else d2083 (change p 204 (some 182))) = d5983 p
  rw [sub10861, sub10860]
  rfl
theorem sub10863 (p : Pattern) : d2086 (change p 204 (some 182)) = d5984 p := by
  change (if p 115 then d2085 (change p 204 (some 182)) else d1862 (change p 204 (some 182))) = d5984 p
  rw [sub10862, sub10624]
  rfl
theorem sub10864 (p : Pattern) : d2087 (change p 204 (some 182)) = d5985 p := by
  change (if p 71 then d2086 (change p 204 (some 182)) else d1849 (change p 204 (some 182))) = d5985 p
  rw [sub10863, sub10612]
  rfl
theorem sub10865 (p : Pattern) : d2088 (change p 204 (some 182)) = d5986 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1885 (change p 204 (some 182))) = d5986 p
  rw [sub10415, sub10656]
  rfl
theorem sub10866 (p : Pattern) : d2089 (change p 204 (some 182)) = d5987 p := by
  change (if p 162 then d2088 (change p 204 (some 182)) else d1924 (change p 204 (some 182))) = d5987 p
  rw [sub10865, sub10698]
  rfl
theorem sub10867 (p : Pattern) : d2090 (change p 204 (some 182)) = d5988 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2088 (change p 204 (some 182))) = d5988 p
  rw [sub10415, sub10865]
  rfl
theorem sub10868 (p : Pattern) : d2091 (change p 204 (some 182)) = d5989 p := by
  change (if p 161 then d2090 (change p 204 (some 182)) else d2089 (change p 204 (some 182))) = d5989 p
  rw [sub10867, sub10866]
  rfl
theorem sub10869 (p : Pattern) : d2092 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1910 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10684]
  simp only [ite_self]
theorem sub10870 (p : Pattern) : d2093 (change p 204 (some 182)) = d5922 p := by
  change (if p 162 then d2092 (change p 204 (some 182)) else d1931 (change p 204 (some 182))) = d5922 p
  rw [sub10869, sub10705]
  rfl
theorem sub10871 (p : Pattern) : d2094 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2092 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10869]
  simp only [ite_self]
theorem sub10872 (p : Pattern) : d2095 (change p 204 (some 182)) = d5923 p := by
  change (if p 161 then d2094 (change p 204 (some 182)) else d2093 (change p 204 (some 182))) = d5923 p
  rw [sub10871, sub10870]
  rfl
theorem sub10873 (p : Pattern) : d2096 (change p 204 (some 182)) = d5990 p := by
  change (if p 160 then d2095 (change p 204 (some 182)) else d2091 (change p 204 (some 182))) = d5990 p
  rw [sub10872, sub10868]
  rfl
theorem sub10874 (p : Pattern) : d2097 (change p 204 (some 182)) = d5991 p := by
  change (if p 141 then d2096 (change p 204 (some 182)) else d1915 (change p 204 (some 182))) = d5991 p
  rw [sub10873, sub10690]
  rfl
theorem sub10875 (p : Pattern) : d2098 (change p 204 (some 182)) = d5992 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1968 (change p 204 (some 182))) = d5992 p
  rw [sub10415, sub10743]
  rfl
theorem sub10876 (p : Pattern) : d2099 (change p 204 (some 182)) = d5993 p := by
  change (if p 162 then d2098 (change p 204 (some 182)) else d1979 (change p 204 (some 182))) = d5993 p
  rw [sub10875, sub10754]
  rfl
theorem sub10877 (p : Pattern) : d2100 (change p 204 (some 182)) = d5994 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2098 (change p 204 (some 182))) = d5994 p
  rw [sub10415, sub10875]
  rfl
theorem sub10878 (p : Pattern) : d2101 (change p 204 (some 182)) = d5995 p := by
  change (if p 161 then d2100 (change p 204 (some 182)) else d2099 (change p 204 (some 182))) = d5995 p
  rw [sub10877, sub10876]
  rfl
theorem sub10879 (p : Pattern) : d2102 (change p 204 (some 182)) = d5996 p := by
  change (if p 160 then d1987 (change p 204 (some 182)) else d2101 (change p 204 (some 182))) = d5996 p
  rw [sub10762, sub10878]
  rfl
theorem sub10880 (p : Pattern) : d2103 (change p 204 (some 182)) = d5997 p := by
  change (if p 141 then d2102 (change p 204 (some 182)) else d1978 (change p 204 (some 182))) = d5997 p
  rw [sub10879, sub10753]
  rfl
theorem sub10881 (p : Pattern) : d2104 (change p 204 (some 182)) = d5998 p := by
  change (if p 138 then d2103 (change p 204 (some 182)) else d2097 (change p 204 (some 182))) = d5998 p
  rw [sub10880, sub10874]
  rfl
theorem sub10882 (p : Pattern) : d2105 (change p 204 (some 182)) = d5999 p := by
  change (if p 138 then d1994 (change p 204 (some 182)) else d2103 (change p 204 (some 182))) = d5999 p
  rw [sub10769, sub10880]
  rfl
theorem sub10883 (p : Pattern) : d2106 (change p 204 (some 182)) = d6000 p := by
  change (if p 116 then d2105 (change p 204 (some 182)) else d2104 (change p 204 (some 182))) = d6000 p
  rw [sub10882, sub10881]
  rfl
theorem sub10884 (p : Pattern) : d2107 (change p 204 (some 182)) = d2107 p := by
  change (if p 225 then d1946 (change p 204 (some 182)) else d1940 (change p 204 (some 182))) = d2107 p
  rw [sub10720, sub10714]
  rfl
theorem sub10885 (p : Pattern) : d2108 (change p 204 (some 182)) = d2108 p := by
  change (if p 224 then d2107 (change p 204 (some 182)) else d1947 (change p 204 (some 182))) = d2108 p
  rw [sub10884, sub10721]
  rfl
theorem sub10886 (p : Pattern) : d2109 (change p 204 (some 182)) = d2108 p := by
  change d2108 (change p 204 (some 182)) = d2108 p
  exact sub10885 p
theorem sub10887 (p : Pattern) : d2110 (change p 204 (some 182)) = d2108 p := by
  change d2109 (change p 204 (some 182)) = d2108 p
  exact sub10886 p
theorem sub10888 (p : Pattern) : d2111 (change p 204 (some 182)) = d6001 p := by
  change (if p 163 then d1968 (change p 204 (some 182)) else d2110 (change p 204 (some 182))) = d6001 p
  rw [sub10743, sub10887]
  rfl
theorem sub10889 (p : Pattern) : d2112 (change p 204 (some 182)) = d6002 p := by
  change (if p 162 then d2111 (change p 204 (some 182)) else d1944 (change p 204 (some 182))) = d6002 p
  rw [sub10888, sub10718]
  rfl
theorem sub10890 (p : Pattern) : d2113 (change p 204 (some 182)) = d6003 p := by
  change (if p 163 then d1968 (change p 204 (some 182)) else d1953 (change p 204 (some 182))) = d6003 p
  rw [sub10743, sub10727]
  rfl
theorem sub10891 (p : Pattern) : d2114 (change p 204 (some 182)) = d6004 p := by
  change (if p 162 then d1888 (change p 204 (some 182)) else d2113 (change p 204 (some 182))) = d6004 p
  rw [sub10659, sub10890]
  rfl
theorem sub10892 (p : Pattern) : d2115 (change p 204 (some 182)) = d6005 p := by
  change (if p 161 then d2114 (change p 204 (some 182)) else d2112 (change p 204 (some 182))) = d6005 p
  rw [sub10891, sub10889]
  rfl
theorem sub10893 (p : Pattern) : d2116 (change p 204 (some 182)) = d1905 p := by
  change d1906 (change p 204 (some 182)) = d1905 p
  exact sub10680 p
theorem sub10894 (p : Pattern) : d2117 (change p 204 (some 182)) = d5911 p := by
  change (if p 163 then d2116 (change p 204 (some 182)) else d1973 (change p 204 (some 182))) = d5911 p
  rw [sub10893, sub10748]
  rfl
theorem sub10895 (p : Pattern) : d2118 (change p 204 (some 182)) = d5912 p := by
  change (if p 162 then d2092 (change p 204 (some 182)) else d2117 (change p 204 (some 182))) = d5912 p
  rw [sub10869, sub10894]
  rfl
theorem sub10896 (p : Pattern) : d2119 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10897 (p : Pattern) : d2120 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d2119 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10896]
  simp only [ite_self]
theorem sub10898 (p : Pattern) : d2121 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2120 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10897]
  simp only [ite_self]
theorem sub10899 (p : Pattern) : d2122 (change p 204 (some 182)) = d5913 p := by
  change (if p 161 then d2121 (change p 204 (some 182)) else d2118 (change p 204 (some 182))) = d5913 p
  rw [sub10898, sub10895]
  rfl
theorem sub10900 (p : Pattern) : d2123 (change p 204 (some 182)) = d6006 p := by
  change (if p 160 then d2122 (change p 204 (some 182)) else d2115 (change p 204 (some 182))) = d6006 p
  rw [sub10899, sub10892]
  rfl
theorem sub10901 (p : Pattern) : d2124 (change p 204 (some 182)) = d2124 p := by
  change (if p 225 then d1895 (change p 204 (some 182)) else d116 (change p 204 (some 182))) = d2124 p
  rw [sub10667, sub10662]
  rfl
theorem sub10902 (p : Pattern) : d2125 (change p 204 (some 182)) = d2125 p := by
  change (if p 224 then d1895 (change p 204 (some 182)) else d2124 (change p 204 (some 182))) = d2125 p
  rw [sub10667, sub10901]
  rfl
theorem sub10903 (p : Pattern) : d2126 (change p 204 (some 182)) = d2125 p := by
  change d2125 (change p 204 (some 182)) = d2125 p
  exact sub10902 p
theorem sub10904 (p : Pattern) : d2127 (change p 204 (some 182)) = d2125 p := by
  change d2126 (change p 204 (some 182)) = d2125 p
  exact sub10903 p
theorem sub10905 (p : Pattern) : d2128 (change p 204 (some 182)) = d6007 p := by
  change (if p 163 then d2127 (change p 204 (some 182)) else d2110 (change p 204 (some 182))) = d6007 p
  rw [sub10904, sub10887]
  rfl
theorem sub10906 (p : Pattern) : d2129 (change p 204 (some 182)) = d2129 p := by
  change (if p 225 then d1964 (change p 204 (some 182)) else d107 (change p 204 (some 182))) = d2129 p
  rw [sub10738, sub10648]
  rfl
theorem sub10907 (p : Pattern) : d2130 (change p 204 (some 182)) = d2130 p := by
  change (if p 224 then d1964 (change p 204 (some 182)) else d2129 (change p 204 (some 182))) = d2130 p
  rw [sub10738, sub10906]
  rfl
theorem sub10908 (p : Pattern) : d2131 (change p 204 (some 182)) = d2130 p := by
  change d2130 (change p 204 (some 182)) = d2130 p
  exact sub10907 p
theorem sub10909 (p : Pattern) : d2132 (change p 204 (some 182)) = d2130 p := by
  change d2131 (change p 204 (some 182)) = d2130 p
  exact sub10908 p
theorem sub10910 (p : Pattern) : d2133 (change p 204 (some 182)) = d6008 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d2132 (change p 204 (some 182))) = d6008 p
  rw [sub10415, sub10909]
  rfl
theorem sub10911 (p : Pattern) : d2134 (change p 204 (some 182)) = d6009 p := by
  change (if p 162 then d2133 (change p 204 (some 182)) else d2128 (change p 204 (some 182))) = d6009 p
  rw [sub10910, sub10905]
  rfl
theorem sub10912 (p : Pattern) : d2135 (change p 204 (some 182)) = d2135 p := by
  change (if p 225 then d1961 (change p 204 (some 182)) else d1964 (change p 204 (some 182))) = d2135 p
  rw [sub10735, sub10738]
  rfl
theorem sub10913 (p : Pattern) : d2136 (change p 204 (some 182)) = d2136 p := by
  change (if p 224 then d2135 (change p 204 (some 182)) else d1962 (change p 204 (some 182))) = d2136 p
  rw [sub10912, sub10736]
  rfl
theorem sub10914 (p : Pattern) : d2137 (change p 204 (some 182)) = d2136 p := by
  change d2136 (change p 204 (some 182)) = d2136 p
  exact sub10913 p
theorem sub10915 (p : Pattern) : d2138 (change p 204 (some 182)) = d2136 p := by
  change d2137 (change p 204 (some 182)) = d2136 p
  exact sub10914 p
theorem sub10916 (p : Pattern) : d2139 (change p 204 (some 182)) = d6010 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d2138 (change p 204 (some 182))) = d6010 p
  rw [sub10415, sub10915]
  rfl
theorem sub10917 (p : Pattern) : d2140 (change p 204 (some 182)) = d6011 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d2139 (change p 204 (some 182))) = d6011 p
  rw [sub10415, sub10916]
  rfl
theorem sub10918 (p : Pattern) : d2141 (change p 204 (some 182)) = d6012 p := by
  change (if p 161 then d2140 (change p 204 (some 182)) else d2134 (change p 204 (some 182))) = d6012 p
  rw [sub10917, sub10911]
  rfl
theorem sub10919 (p : Pattern) : d2142 (change p 204 (some 182)) = d1905 p := by
  change d1906 (change p 204 (some 182)) = d1905 p
  exact sub10680 p
end NetHack.Sokoban22Refined85
