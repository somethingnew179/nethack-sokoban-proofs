/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2040 (p : Pattern) : d23 (change p 10000 (some 138)) = d23 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d21 (change p 10000 (some 138))) = d23 p
  rw [sub2018, sub2038]
  rfl
theorem sub2041 (p : Pattern) : d24 (change p 10000 (some 138)) = d24 p := by
  change (if p 158 then d23 (change p 10000 (some 138)) else d22 (change p 10000 (some 138))) = d24 p
  rw [sub2040, sub2039]
  rfl
theorem sub2042 (p : Pattern) : d25 (change p 10000 (some 138)) = d25 p := by
  change (if p 139 then d24 (change p 10000 (some 138)) else d20 (change p 10000 (some 138))) = d25 p
  rw [sub2041, sub2037]
  rfl
theorem sub2043 (p : Pattern) : d26 (change p 10000 (some 138)) = d25 p := by
  change d25 (change p 10000 (some 138)) = d25 p
  exact sub2042 p
theorem sub2044 (p : Pattern) : d27 (change p 10000 (some 138)) = d46 p := by
  change (if p 134 then d26 (change p 10000 (some 138)) else d16 (change p 10000 (some 138))) = d46 p
  rw [sub2043, sub2033]
  rfl
theorem sub2045 (p : Pattern) : d28 (change p 10000 (some 138)) = d47 p := by
  change (if p 133 then d27 (change p 10000 (some 138)) else d16 (change p 10000 (some 138))) = d47 p
  rw [sub2044, sub2033]
  rfl
theorem sub2046 (p : Pattern) : d29 (change p 10000 (some 138)) = d29 p := by
  change (if p 161 then d1 (change p 10000 (some 138)) else d0 (change p 10000 (some 138))) = d29 p
  rw [sub2025, sub2017]
  rfl
theorem sub2047 (p : Pattern) : d30 (change p 10000 (some 138)) = d30 p := by
  change (if p 160 then d2 (change p 10000 (some 138)) else d29 (change p 10000 (some 138))) = d30 p
  rw [sub2018, sub2046]
  rfl
theorem sub2048 (p : Pattern) : d31 (change p 10000 (some 138)) = d31 p := by
  change (if p 159 then d30 (change p 10000 (some 138)) else d4 (change p 10000 (some 138))) = d31 p
  rw [sub2047, sub2020]
  rfl
theorem sub2049 (p : Pattern) : d32 (change p 10000 (some 138)) = d32 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d30 (change p 10000 (some 138))) = d32 p
  rw [sub2018, sub2047]
  rfl
theorem sub2050 (p : Pattern) : d33 (change p 10000 (some 138)) = d33 p := by
  change (if p 158 then d32 (change p 10000 (some 138)) else d31 (change p 10000 (some 138))) = d33 p
  rw [sub2049, sub2048]
  rfl
theorem sub2051 (p : Pattern) : d34 (change p 10000 (some 138)) = d34 p := by
  change (if p 139 then d24 (change p 10000 (some 138)) else d33 (change p 10000 (some 138))) = d34 p
  rw [sub2041, sub2050]
  rfl
theorem sub2052 (p : Pattern) : d35 (change p 10000 (some 138)) = d34 p := by
  change d34 (change p 10000 (some 138)) = d34 p
  exact sub2051 p
theorem sub2053 (p : Pattern) : d36 (change p 10000 (some 138)) = d48 p := by
  change (if p 134 then d35 (change p 10000 (some 138)) else d16 (change p 10000 (some 138))) = d48 p
  rw [sub2052, sub2033]
  rfl
theorem sub2054 (p : Pattern) : d37 (change p 10000 (some 138)) = d37 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d5 (change p 10000 (some 138))) = d37 p
  rw [sub2018, sub2021]
  rfl
theorem sub2055 (p : Pattern) : d38 (change p 10000 (some 138)) = d38 p := by
  change (if p 158 then d37 (change p 10000 (some 138)) else d6 (change p 10000 (some 138))) = d38 p
  rw [sub2054, sub2022]
  rfl
theorem sub2056 (p : Pattern) : d39 (change p 10000 (some 138)) = d39 p := by
  change (if p 159 then d2 (change p 10000 (some 138)) else d11 (change p 10000 (some 138))) = d39 p
  rw [sub2018, sub2028]
  rfl
theorem sub2057 (p : Pattern) : d40 (change p 10000 (some 138)) = d40 p := by
  change (if p 158 then d39 (change p 10000 (some 138)) else d12 (change p 10000 (some 138))) = d40 p
  rw [sub2056, sub2029]
  rfl
theorem sub2058 (p : Pattern) : d41 (change p 10000 (some 138)) = d41 p := by
  change (if p 139 then d40 (change p 10000 (some 138)) else d38 (change p 10000 (some 138))) = d41 p
  rw [sub2057, sub2055]
  rfl
theorem sub2059 (p : Pattern) : d42 (change p 10000 (some 138)) = d41 p := by
  change d41 (change p 10000 (some 138)) = d41 p
  exact sub2058 p
theorem sub2060 (p : Pattern) : d43 (change p 10000 (some 138)) = d49 p := by
  change (if p 134 then d26 (change p 10000 (some 138)) else d42 (change p 10000 (some 138))) = d49 p
  rw [sub2043, sub2059]
  rfl
theorem sub2061 (p : Pattern) : d44 (change p 10000 (some 138)) = d50 p := by
  change (if p 133 then d43 (change p 10000 (some 138)) else d36 (change p 10000 (some 138))) = d50 p
  rw [sub2060, sub2053]
  rfl
theorem sub2062 (p : Pattern) : d45 (change p 10000 (some 138)) = d51 p := by
  change (if p 132 then d44 (change p 10000 (some 138)) else d28 (change p 10000 (some 138))) = d51 p
  rw [sub2061, sub2045]
  rfl
theorem sub2063 (p : Pattern) : d46 (change p 10000 (some 138)) = d46 p := by
  change (if p 134 then d25 (change p 10000 (some 138)) else d15 (change p 10000 (some 138))) = d46 p
  rw [sub2042, sub2032]
  rfl
theorem sub2064 (p : Pattern) : d47 (change p 10000 (some 138)) = d47 p := by
  change (if p 133 then d46 (change p 10000 (some 138)) else d15 (change p 10000 (some 138))) = d47 p
  rw [sub2063, sub2032]
  rfl
theorem sub2065 (p : Pattern) : d48 (change p 10000 (some 138)) = d48 p := by
  change (if p 134 then d34 (change p 10000 (some 138)) else d15 (change p 10000 (some 138))) = d48 p
  rw [sub2051, sub2032]
  rfl
theorem sub2066 (p : Pattern) : d49 (change p 10000 (some 138)) = d49 p := by
  change (if p 134 then d25 (change p 10000 (some 138)) else d41 (change p 10000 (some 138))) = d49 p
  rw [sub2042, sub2058]
  rfl
theorem sub2067 (p : Pattern) : d50 (change p 10000 (some 138)) = d50 p := by
  change (if p 133 then d49 (change p 10000 (some 138)) else d48 (change p 10000 (some 138))) = d50 p
  rw [sub2066, sub2065]
  rfl
theorem sub2068 (p : Pattern) : d51 (change p 10000 (some 138)) = d51 p := by
  change (if p 132 then d50 (change p 10000 (some 138)) else d47 (change p 10000 (some 138))) = d51 p
  rw [sub2067, sub2064]
  rfl
theorem sub2069 (p : Pattern) : d52 (change p 10000 (some 138)) = d52 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d8 (change p 10000 (some 138))) = d52 p
  rw [sub2018, sub2024]
  rfl
theorem sub2070 (p : Pattern) : d53 (change p 10000 (some 138)) = d52 p := by
  change d52 (change p 10000 (some 138)) = d52 p
  exact sub2069 p
theorem sub2071 (p : Pattern) : d54 (change p 10000 (some 138)) = d54 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d20 (change p 10000 (some 138))) = d54 p
  rw [sub2018, sub2037]
  rfl
theorem sub2072 (p : Pattern) : d55 (change p 10000 (some 138)) = d54 p := by
  change d54 (change p 10000 (some 138)) = d54 p
  exact sub2071 p
theorem sub2073 (p : Pattern) : d56 (change p 10000 (some 138)) = d470 p := by
  change (if p 134 then d55 (change p 10000 (some 138)) else d53 (change p 10000 (some 138))) = d470 p
  rw [sub2072, sub2070]
  rfl
theorem sub2074 (p : Pattern) : d57 (change p 10000 (some 138)) = d524 p := by
  change (if p 133 then d56 (change p 10000 (some 138)) else d53 (change p 10000 (some 138))) = d524 p
  rw [sub2073, sub2070]
  rfl
theorem sub2075 (p : Pattern) : d58 (change p 10000 (some 138)) = d58 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d33 (change p 10000 (some 138))) = d58 p
  rw [sub2018, sub2050]
  rfl
theorem sub2076 (p : Pattern) : d59 (change p 10000 (some 138)) = d58 p := by
  change d58 (change p 10000 (some 138)) = d58 p
  exact sub2075 p
theorem sub2077 (p : Pattern) : d60 (change p 10000 (some 138)) = d519 p := by
  change (if p 134 then d59 (change p 10000 (some 138)) else d53 (change p 10000 (some 138))) = d519 p
  rw [sub2076, sub2070]
  rfl
theorem sub2078 (p : Pattern) : d61 (change p 10000 (some 138)) = d61 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d38 (change p 10000 (some 138))) = d61 p
  rw [sub2018, sub2055]
  rfl
theorem sub2079 (p : Pattern) : d62 (change p 10000 (some 138)) = d61 p := by
  change d61 (change p 10000 (some 138)) = d61 p
  exact sub2078 p
theorem sub2080 (p : Pattern) : d63 (change p 10000 (some 138)) = d473 p := by
  change (if p 134 then d55 (change p 10000 (some 138)) else d62 (change p 10000 (some 138))) = d473 p
  rw [sub2072, sub2079]
  rfl
theorem sub2081 (p : Pattern) : d64 (change p 10000 (some 138)) = d520 p := by
  change (if p 133 then d63 (change p 10000 (some 138)) else d60 (change p 10000 (some 138))) = d520 p
  rw [sub2080, sub2077]
  rfl
theorem sub2082 (p : Pattern) : d65 (change p 10000 (some 138)) = d1295 p := by
  change (if p 132 then d64 (change p 10000 (some 138)) else d57 (change p 10000 (some 138))) = d1295 p
  rw [sub2081, sub2074]
  rfl
theorem sub2083 (p : Pattern) : d66 (change p 10000 (some 138)) = d1296 p := by
  change (if p 113 then d65 (change p 10000 (some 138)) else d51 (change p 10000 (some 138))) = d1296 p
  rw [sub2082, sub2068]
  rfl
theorem sub2084 (p : Pattern) : d67 (change p 10000 (some 138)) = d1297 p := by
  change (if p 112 then d66 (change p 10000 (some 138)) else d45 (change p 10000 (some 138))) = d1297 p
  rw [sub2083, sub2062]
  rfl
theorem sub2085 (p : Pattern) : d68 (change p 10000 (some 138)) = d68 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d40 (change p 10000 (some 138))) = d68 p
  rw [sub2018, sub2057]
  rfl
theorem sub2086 (p : Pattern) : d69 (change p 10000 (some 138)) = d68 p := by
  change d68 (change p 10000 (some 138)) = d68 p
  exact sub2085 p
theorem sub2087 (p : Pattern) : d70 (change p 10000 (some 138)) = d70 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d24 (change p 10000 (some 138))) = d70 p
  rw [sub2018, sub2041]
  rfl
theorem sub2088 (p : Pattern) : d71 (change p 10000 (some 138)) = d70 p := by
  change d70 (change p 10000 (some 138)) = d70 p
  exact sub2087 p
theorem sub2089 (p : Pattern) : d72 (change p 10000 (some 138)) = d75 p := by
  change (if p 134 then d71 (change p 10000 (some 138)) else d69 (change p 10000 (some 138))) = d75 p
  rw [sub2088, sub2086]
  rfl
theorem sub2090 (p : Pattern) : d73 (change p 10000 (some 138)) = d79 p := by
  change (if p 133 then d72 (change p 10000 (some 138)) else d27 (change p 10000 (some 138))) = d79 p
  rw [sub2089, sub2044]
  rfl
theorem sub2091 (p : Pattern) : d74 (change p 10000 (some 138)) = d80 p := by
  change (if p 132 then d73 (change p 10000 (some 138)) else d28 (change p 10000 (some 138))) = d80 p
  rw [sub2090, sub2045]
  rfl
theorem sub2092 (p : Pattern) : d75 (change p 10000 (some 138)) = d75 p := by
  change (if p 134 then d70 (change p 10000 (some 138)) else d68 (change p 10000 (some 138))) = d75 p
  rw [sub2087, sub2085]
  rfl
theorem sub2093 (p : Pattern) : d76 (change p 10000 (some 138)) = d79 p := by
  change (if p 133 then d75 (change p 10000 (some 138)) else d27 (change p 10000 (some 138))) = d79 p
  rw [sub2092, sub2044]
  rfl
theorem sub2094 (p : Pattern) : d77 (change p 10000 (some 138)) = d80 p := by
  change (if p 132 then d76 (change p 10000 (some 138)) else d28 (change p 10000 (some 138))) = d80 p
  rw [sub2093, sub2045]
  rfl
theorem sub2095 (p : Pattern) : d78 (change p 10000 (some 138)) = d80 p := by
  change (if p 113 then d77 (change p 10000 (some 138)) else d74 (change p 10000 (some 138))) = d80 p
  rw [sub2094, sub2091]
  simp only [ite_self]
theorem sub2096 (p : Pattern) : d79 (change p 10000 (some 138)) = d79 p := by
  change (if p 133 then d75 (change p 10000 (some 138)) else d46 (change p 10000 (some 138))) = d79 p
  rw [sub2092, sub2063]
  rfl
theorem sub2097 (p : Pattern) : d80 (change p 10000 (some 138)) = d80 p := by
  change (if p 132 then d79 (change p 10000 (some 138)) else d47 (change p 10000 (some 138))) = d80 p
  rw [sub2096, sub2064]
  rfl
theorem sub2098 (p : Pattern) : d81 (change p 10000 (some 138)) = d491 p := by
  change (if p 133 then d75 (change p 10000 (some 138)) else d56 (change p 10000 (some 138))) = d491 p
  rw [sub2092, sub2073]
  rfl
theorem sub2099 (p : Pattern) : d82 (change p 10000 (some 138)) = d525 p := by
  change (if p 132 then d81 (change p 10000 (some 138)) else d57 (change p 10000 (some 138))) = d525 p
  rw [sub2098, sub2074]
  rfl
theorem sub2100 (p : Pattern) : d83 (change p 10000 (some 138)) = d1298 p := by
  change (if p 113 then d82 (change p 10000 (some 138)) else d80 (change p 10000 (some 138))) = d1298 p
  rw [sub2099, sub2097]
  rfl
theorem sub2101 (p : Pattern) : d84 (change p 10000 (some 138)) = d1299 p := by
  change (if p 112 then d83 (change p 10000 (some 138)) else d78 (change p 10000 (some 138))) = d1299 p
  rw [sub2100, sub2095]
  rfl
theorem sub2102 (p : Pattern) : d85 (change p 10000 (some 138)) = d1300 p := by
  change (if p 106 then d84 (change p 10000 (some 138)) else d67 (change p 10000 (some 138))) = d1300 p
  rw [sub2101, sub2084]
  rfl
theorem sub2103 (p : Pattern) : d86 (change p 10000 (some 138)) = d52 p := by
  change d52 (change p 10000 (some 138)) = d52 p
  exact sub2069 p
theorem sub2104 (p : Pattern) : d87 (change p 10000 (some 138)) = d54 p := by
  change d54 (change p 10000 (some 138)) = d54 p
  exact sub2071 p
theorem sub2105 (p : Pattern) : d88 (change p 10000 (some 138)) = d470 p := by
  change (if p 134 then d87 (change p 10000 (some 138)) else d86 (change p 10000 (some 138))) = d470 p
  rw [sub2104, sub2103]
  rfl
theorem sub2106 (p : Pattern) : d89 (change p 10000 (some 138)) = d524 p := by
  change (if p 133 then d88 (change p 10000 (some 138)) else d86 (change p 10000 (some 138))) = d524 p
  rw [sub2105, sub2103]
  rfl
theorem sub2107 (p : Pattern) : d90 (change p 10000 (some 138)) = d58 p := by
  change d58 (change p 10000 (some 138)) = d58 p
  exact sub2075 p
theorem sub2108 (p : Pattern) : d91 (change p 10000 (some 138)) = d519 p := by
  change (if p 134 then d90 (change p 10000 (some 138)) else d86 (change p 10000 (some 138))) = d519 p
  rw [sub2107, sub2103]
  rfl
theorem sub2109 (p : Pattern) : d92 (change p 10000 (some 138)) = d61 p := by
  change d61 (change p 10000 (some 138)) = d61 p
  exact sub2078 p
theorem sub2110 (p : Pattern) : d93 (change p 10000 (some 138)) = d473 p := by
  change (if p 134 then d87 (change p 10000 (some 138)) else d92 (change p 10000 (some 138))) = d473 p
  rw [sub2104, sub2109]
  rfl
theorem sub2111 (p : Pattern) : d94 (change p 10000 (some 138)) = d520 p := by
  change (if p 133 then d93 (change p 10000 (some 138)) else d91 (change p 10000 (some 138))) = d520 p
  rw [sub2110, sub2108]
  rfl
theorem sub2112 (p : Pattern) : d95 (change p 10000 (some 138)) = d1295 p := by
  change (if p 132 then d94 (change p 10000 (some 138)) else d89 (change p 10000 (some 138))) = d1295 p
  rw [sub2111, sub2106]
  rfl
theorem sub2113 (p : Pattern) : d96 (change p 10000 (some 138)) = d1296 p := by
  change (if p 113 then d95 (change p 10000 (some 138)) else d45 (change p 10000 (some 138))) = d1296 p
  rw [sub2112, sub2062]
  rfl
theorem sub2114 (p : Pattern) : d97 (change p 10000 (some 138)) = d97 p := by
  change (if p 139 then d2 (change p 10000 (some 138)) else d14 (change p 10000 (some 138))) = d97 p
  rw [sub2018, sub2031]
  rfl
theorem sub2115 (p : Pattern) : d98 (change p 10000 (some 138)) = d97 p := by
  change d97 (change p 10000 (some 138)) = d97 p
  exact sub2114 p
theorem sub2116 (p : Pattern) : d99 (change p 10000 (some 138)) = d109 p := by
  change (if p 134 then d71 (change p 10000 (some 138)) else d98 (change p 10000 (some 138))) = d109 p
  rw [sub2088, sub2115]
  rfl
theorem sub2117 (p : Pattern) : d100 (change p 10000 (some 138)) = d110 p := by
  change (if p 133 then d99 (change p 10000 (some 138)) else d98 (change p 10000 (some 138))) = d110 p
  rw [sub2116, sub2115]
  rfl
theorem sub2118 (p : Pattern) : d101 (change p 10000 (some 138)) = d125 p := by
  change (if p 133 then d72 (change p 10000 (some 138)) else d99 (change p 10000 (some 138))) = d125 p
  rw [sub2089, sub2116]
  rfl
theorem sub2119 (p : Pattern) : d102 (change p 10000 (some 138)) = d126 p := by
  change (if p 132 then d101 (change p 10000 (some 138)) else d100 (change p 10000 (some 138))) = d126 p
  rw [sub2118, sub2117]
  rfl
theorem sub2120 (p : Pattern) : d103 (change p 10000 (some 138)) = d1301 p := by
  change (if p 112 then d102 (change p 10000 (some 138)) else d96 (change p 10000 (some 138))) = d1301 p
  rw [sub2119, sub2113]
  rfl
theorem sub2121 (p : Pattern) : d104 (change p 10000 (some 138)) = d491 p := by
  change (if p 133 then d75 (change p 10000 (some 138)) else d88 (change p 10000 (some 138))) = d491 p
  rw [sub2092, sub2105]
  rfl
theorem sub2122 (p : Pattern) : d105 (change p 10000 (some 138)) = d525 p := by
  change (if p 132 then d104 (change p 10000 (some 138)) else d89 (change p 10000 (some 138))) = d525 p
  rw [sub2121, sub2106]
  rfl
theorem sub2123 (p : Pattern) : d106 (change p 10000 (some 138)) = d1298 p := by
  change (if p 113 then d105 (change p 10000 (some 138)) else d77 (change p 10000 (some 138))) = d1298 p
  rw [sub2122, sub2094]
  rfl
theorem sub2124 (p : Pattern) : d107 (change p 10000 (some 138)) = d111 p := by
  change (if p 133 then d2 (change p 10000 (some 138)) else d99 (change p 10000 (some 138))) = d111 p
  rw [sub2018, sub2116]
  rfl
theorem sub2125 (p : Pattern) : d108 (change p 10000 (some 138)) = d112 p := by
  change (if p 132 then d107 (change p 10000 (some 138)) else d100 (change p 10000 (some 138))) = d112 p
  rw [sub2124, sub2117]
  rfl
theorem sub2126 (p : Pattern) : d109 (change p 10000 (some 138)) = d109 p := by
  change (if p 134 then d70 (change p 10000 (some 138)) else d97 (change p 10000 (some 138))) = d109 p
  rw [sub2087, sub2114]
  rfl
theorem sub2127 (p : Pattern) : d110 (change p 10000 (some 138)) = d110 p := by
  change (if p 133 then d109 (change p 10000 (some 138)) else d97 (change p 10000 (some 138))) = d110 p
  rw [sub2126, sub2114]
  rfl
theorem sub2128 (p : Pattern) : d111 (change p 10000 (some 138)) = d111 p := by
  change (if p 133 then d2 (change p 10000 (some 138)) else d109 (change p 10000 (some 138))) = d111 p
  rw [sub2018, sub2126]
  rfl
theorem sub2129 (p : Pattern) : d112 (change p 10000 (some 138)) = d112 p := by
  change (if p 132 then d111 (change p 10000 (some 138)) else d110 (change p 10000 (some 138))) = d112 p
  rw [sub2128, sub2127]
  rfl
theorem sub2130 (p : Pattern) : d113 (change p 10000 (some 138)) = d112 p := by
  change (if p 113 then d112 (change p 10000 (some 138)) else d108 (change p 10000 (some 138))) = d112 p
  rw [sub2129, sub2125]
  simp only [ite_self]
theorem sub2131 (p : Pattern) : d114 (change p 10000 (some 138)) = d1302 p := by
  change (if p 112 then d113 (change p 10000 (some 138)) else d106 (change p 10000 (some 138))) = d1302 p
  rw [sub2130, sub2123]
  rfl
theorem sub2132 (p : Pattern) : d115 (change p 10000 (some 138)) = d1303 p := by
  change (if p 106 then d114 (change p 10000 (some 138)) else d103 (change p 10000 (some 138))) = d1303 p
  rw [sub2131, sub2120]
  rfl
theorem sub2133 (p : Pattern) : d116 (change p 10000 (some 138)) = d1304 p := by
  change (if p 86 then d115 (change p 10000 (some 138)) else d85 (change p 10000 (some 138))) = d1304 p
  rw [sub2132, sub2102]
  rfl
theorem sub2134 (p : Pattern) : d117 (change p 10000 (some 138)) = d1299 p := by
  change (if p 112 then d83 (change p 10000 (some 138)) else d77 (change p 10000 (some 138))) = d1299 p
  rw [sub2100, sub2094]
  rfl
theorem sub2135 (p : Pattern) : d118 (change p 10000 (some 138)) = d1300 p := by
  change (if p 106 then d117 (change p 10000 (some 138)) else d67 (change p 10000 (some 138))) = d1300 p
  rw [sub2134, sub2084]
  rfl
theorem sub2136 (p : Pattern) : d120 (change p 10000 (some 138)) = d58 p := by
  change d58 (change p 10000 (some 138)) = d58 p
  exact sub2075 p
theorem sub2137 (p : Pattern) : d121 (change p 10000 (some 138)) = d519 p := by
  change (if p 134 then d120 (change p 10000 (some 138)) else d86 (change p 10000 (some 138))) = d519 p
  rw [sub2136, sub2103]
  rfl
theorem sub2138 (p : Pattern) : d122 (change p 10000 (some 138)) = d520 p := by
  change (if p 133 then d93 (change p 10000 (some 138)) else d121 (change p 10000 (some 138))) = d520 p
  rw [sub2110, sub2137]
  rfl
theorem sub2139 (p : Pattern) : d123 (change p 10000 (some 138)) = d1295 p := by
  change (if p 132 then d122 (change p 10000 (some 138)) else d89 (change p 10000 (some 138))) = d1295 p
  rw [sub2138, sub2106]
  rfl
theorem sub2140 (p : Pattern) : d124 (change p 10000 (some 138)) = d1296 p := by
  change (if p 113 then d123 (change p 10000 (some 138)) else d45 (change p 10000 (some 138))) = d1296 p
  rw [sub2139, sub2062]
  rfl
theorem sub2141 (p : Pattern) : d125 (change p 10000 (some 138)) = d125 p := by
  change (if p 133 then d75 (change p 10000 (some 138)) else d109 (change p 10000 (some 138))) = d125 p
  rw [sub2092, sub2126]
  rfl
theorem sub2142 (p : Pattern) : d126 (change p 10000 (some 138)) = d126 p := by
  change (if p 132 then d125 (change p 10000 (some 138)) else d110 (change p 10000 (some 138))) = d126 p
  rw [sub2141, sub2127]
  rfl
theorem sub2143 (p : Pattern) : d127 (change p 10000 (some 138)) = d126 p := by
  change (if p 113 then d126 (change p 10000 (some 138)) else d102 (change p 10000 (some 138))) = d126 p
  rw [sub2142, sub2119]
  simp only [ite_self]
theorem sub2144 (p : Pattern) : d128 (change p 10000 (some 138)) = d1301 p := by
  change (if p 112 then d127 (change p 10000 (some 138)) else d124 (change p 10000 (some 138))) = d1301 p
  rw [sub2143, sub2140]
  rfl
theorem sub2145 (p : Pattern) : d129 (change p 10000 (some 138)) = d1298 p := by
  change (if p 113 then d82 (change p 10000 (some 138)) else d77 (change p 10000 (some 138))) = d1298 p
  rw [sub2099, sub2094]
  rfl
theorem sub2146 (p : Pattern) : d130 (change p 10000 (some 138)) = d130 p := by
  change (if p 113 then d2 (change p 10000 (some 138)) else d112 (change p 10000 (some 138))) = d130 p
  rw [sub2018, sub2129]
  rfl
theorem sub2147 (p : Pattern) : d131 (change p 10000 (some 138)) = d1305 p := by
  change (if p 112 then d130 (change p 10000 (some 138)) else d129 (change p 10000 (some 138))) = d1305 p
  rw [sub2146, sub2145]
  rfl
theorem sub2148 (p : Pattern) : d132 (change p 10000 (some 138)) = d1306 p := by
  change (if p 106 then d131 (change p 10000 (some 138)) else d128 (change p 10000 (some 138))) = d1306 p
  rw [sub2147, sub2144]
  rfl
theorem sub2149 (p : Pattern) : d133 (change p 10000 (some 138)) = d1307 p := by
  change (if p 86 then d132 (change p 10000 (some 138)) else d118 (change p 10000 (some 138))) = d1307 p
  rw [sub2148, sub2135]
  rfl
theorem sub2150 (p : Pattern) : d134 (change p 10000 (some 138)) = d1308 p := by
  change (if p 80 then d133 (change p 10000 (some 138)) else d116 (change p 10000 (some 138))) = d1308 p
  rw [sub2149, sub2133]
  rfl
theorem sub2151 (p : Pattern) : d0 (change p 10000 (some 134)) = d0 p := by
  rfl
theorem sub2152 (p : Pattern) : d2 (change p 10000 (some 134)) = d2 p := by
  rfl
theorem sub2153 (p : Pattern) : d3 (change p 10000 (some 134)) = d3 p := by
  change (if p 161 then d2 (change p 10000 (some 134)) else d0 (change p 10000 (some 134))) = d3 p
  rw [sub2152, sub2151]
  rfl
theorem sub2154 (p : Pattern) : d4 (change p 10000 (some 134)) = d4 p := by
  change (if p 160 then d3 (change p 10000 (some 134)) else d0 (change p 10000 (some 134))) = d4 p
  rw [sub2153, sub2151]
  rfl
theorem sub2155 (p : Pattern) : d5 (change p 10000 (some 134)) = d5 p := by
  change (if p 160 then d2 (change p 10000 (some 134)) else d0 (change p 10000 (some 134))) = d5 p
  rw [sub2152, sub2151]
  rfl
theorem sub2156 (p : Pattern) : d6 (change p 10000 (some 134)) = d6 p := by
  change (if p 159 then d5 (change p 10000 (some 134)) else d4 (change p 10000 (some 134))) = d6 p
  rw [sub2155, sub2154]
  rfl
theorem sub2157 (p : Pattern) : d7 (change p 10000 (some 134)) = d7 p := by
  change (if p 159 then d2 (change p 10000 (some 134)) else d4 (change p 10000 (some 134))) = d7 p
  rw [sub2152, sub2154]
  rfl
theorem sub2158 (p : Pattern) : d8 (change p 10000 (some 134)) = d8 p := by
  change (if p 158 then d7 (change p 10000 (some 134)) else d6 (change p 10000 (some 134))) = d8 p
  rw [sub2157, sub2156]
  rfl
theorem sub2159 (p : Pattern) : d1 (change p 10000 (some 134)) = d1 p := by
  rfl
end NetHack.Sokoban32Refined
