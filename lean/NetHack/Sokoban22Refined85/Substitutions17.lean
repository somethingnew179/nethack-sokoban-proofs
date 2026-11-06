/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2040 (p : Pattern) : d46 (change p 71 (some 49)) = d46 p := by
  change (if p 182 then d12 (change p 71 (some 49)) else d14 (change p 71 (some 49))) = d46 p
  rw [sub2001, sub2003]
  rfl
theorem sub2041 (p : Pattern) : d47 (change p 71 (some 49)) = d47 p := by
  change (if p 163 then d43 (change p 71 (some 49)) else d46 (change p 71 (some 49))) = d47 p
  rw [sub2037, sub2040]
  rfl
theorem sub2042 (p : Pattern) : d48 (change p 71 (some 49)) = d48 p := by
  change (if p 182 then d12 (change p 71 (some 49)) else d24 (change p 71 (some 49))) = d48 p
  rw [sub2001, sub2015]
  rfl
theorem sub2043 (p : Pattern) : d49 (change p 71 (some 49)) = d49 p := by
  change (if p 163 then d12 (change p 71 (some 49)) else d48 (change p 71 (some 49))) = d49 p
  rw [sub2001, sub2042]
  rfl
theorem sub2044 (p : Pattern) : d50 (change p 71 (some 49)) = d50 p := by
  change (if p 162 then d49 (change p 71 (some 49)) else d47 (change p 71 (some 49))) = d50 p
  rw [sub2043, sub2041]
  rfl
theorem sub2045 (p : Pattern) : d51 (change p 71 (some 49)) = d51 p := by
  change (if p 161 then d50 (change p 71 (some 49)) else d45 (change p 71 (some 49))) = d51 p
  rw [sub2044, sub2039]
  rfl
theorem sub2046 (p : Pattern) : d52 (change p 71 (some 49)) = d52 p := by
  change (if p 160 then d51 (change p 71 (some 49)) else d29 (change p 71 (some 49))) = d52 p
  rw [sub2045, sub2020]
  rfl
theorem sub2047 (p : Pattern) : d53 (change p 71 (some 49)) = d53 p := by
  change (if p 182 then d32 (change p 71 (some 49)) else d31 (change p 71 (some 49))) = d53 p
  rw [sub2024, sub2023]
  rfl
theorem sub2048 (p : Pattern) : d54 (change p 71 (some 49)) = d54 p := by
  change (if p 163 then d53 (change p 71 (some 49)) else d16 (change p 71 (some 49))) = d54 p
  rw [sub2047, sub2005]
  rfl
theorem sub2049 (p : Pattern) : d55 (change p 71 (some 49)) = d55 p := by
  change (if p 163 then d26 (change p 71 (some 49)) else d20 (change p 71 (some 49))) = d55 p
  rw [sub2017, sub2010]
  rfl
theorem sub2050 (p : Pattern) : d56 (change p 71 (some 49)) = d56 p := by
  change (if p 162 then d55 (change p 71 (some 49)) else d54 (change p 71 (some 49))) = d56 p
  rw [sub2049, sub2048]
  rfl
theorem sub2051 (p : Pattern) : d10 (change p 71 (some 49)) = d10 p := by
  rfl
theorem sub2052 (p : Pattern) : d57 (change p 71 (some 49)) = d57 p := by
  change (if p 247 then d12 (change p 71 (some 49)) else d10 (change p 71 (some 49))) = d57 p
  rw [sub2001, sub2051]
  rfl
theorem sub2053 (p : Pattern) : d58 (change p 71 (some 49)) = d58 p := by
  change (if p 246 then d57 (change p 71 (some 49)) else d10 (change p 71 (some 49))) = d58 p
  rw [sub2052, sub2051]
  rfl
theorem sub2054 (p : Pattern) : d59 (change p 71 (some 49)) = d59 p := by
  change (if p 204 then d12 (change p 71 (some 49)) else d58 (change p 71 (some 49))) = d59 p
  rw [sub2001, sub2053]
  rfl
theorem sub2055 (p : Pattern) : d60 (change p 71 (some 49)) = d60 p := by
  change (if p 182 then d59 (change p 71 (some 49)) else d58 (change p 71 (some 49))) = d60 p
  rw [sub2054, sub2053]
  rfl
theorem sub2056 (p : Pattern) : d61 (change p 71 (some 49)) = d61 p := by
  change (if p 163 then d60 (change p 71 (some 49)) else d20 (change p 71 (some 49))) = d61 p
  rw [sub2055, sub2010]
  rfl
theorem sub2057 (p : Pattern) : d62 (change p 71 (some 49)) = d62 p := by
  change (if p 182 then d41 (change p 71 (some 49)) else d40 (change p 71 (some 49))) = d62 p
  rw [sub2035, sub2034]
  rfl
theorem sub2058 (p : Pattern) : d63 (change p 71 (some 49)) = d63 p := by
  change (if p 163 then d12 (change p 71 (some 49)) else d62 (change p 71 (some 49))) = d63 p
  rw [sub2001, sub2057]
  rfl
theorem sub2059 (p : Pattern) : d64 (change p 71 (some 49)) = d64 p := by
  change (if p 162 then d63 (change p 71 (some 49)) else d61 (change p 71 (some 49))) = d64 p
  rw [sub2058, sub2056]
  rfl
theorem sub2060 (p : Pattern) : d65 (change p 71 (some 49)) = d65 p := by
  change (if p 161 then d64 (change p 71 (some 49)) else d56 (change p 71 (some 49))) = d65 p
  rw [sub2059, sub2050]
  rfl
theorem sub2061 (p : Pattern) : d66 (change p 71 (some 49)) = d66 p := by
  change (if p 182 then d12 (change p 71 (some 49)) else d31 (change p 71 (some 49))) = d66 p
  rw [sub2001, sub2023]
  rfl
theorem sub2062 (p : Pattern) : d67 (change p 71 (some 49)) = d67 p := by
  change (if p 163 then d66 (change p 71 (some 49)) else d37 (change p 71 (some 49))) = d67 p
  rw [sub2061, sub2030]
  rfl
theorem sub2063 (p : Pattern) : d68 (change p 71 (some 49)) = d68 p := by
  change (if p 163 then d48 (change p 71 (some 49)) else d43 (change p 71 (some 49))) = d68 p
  rw [sub2042, sub2037]
  rfl
theorem sub2064 (p : Pattern) : d69 (change p 71 (some 49)) = d69 p := by
  change (if p 162 then d68 (change p 71 (some 49)) else d67 (change p 71 (some 49))) = d69 p
  rw [sub2063, sub2062]
  rfl
theorem sub2065 (p : Pattern) : d70 (change p 71 (some 49)) = d70 p := by
  change (if p 182 then d12 (change p 71 (some 49)) else d58 (change p 71 (some 49))) = d70 p
  rw [sub2001, sub2053]
  rfl
theorem sub2066 (p : Pattern) : d71 (change p 71 (some 49)) = d71 p := by
  change (if p 163 then d70 (change p 71 (some 49)) else d43 (change p 71 (some 49))) = d71 p
  rw [sub2065, sub2037]
  rfl
theorem sub2067 (p : Pattern) : d72 (change p 71 (some 49)) = d72 p := by
  change (if p 182 then d12 (change p 71 (some 49)) else d40 (change p 71 (some 49))) = d72 p
  rw [sub2001, sub2034]
  rfl
theorem sub2068 (p : Pattern) : d73 (change p 71 (some 49)) = d73 p := by
  change (if p 163 then d12 (change p 71 (some 49)) else d72 (change p 71 (some 49))) = d73 p
  rw [sub2001, sub2067]
  rfl
theorem sub2069 (p : Pattern) : d74 (change p 71 (some 49)) = d74 p := by
  change (if p 162 then d73 (change p 71 (some 49)) else d71 (change p 71 (some 49))) = d74 p
  rw [sub2068, sub2066]
  rfl
theorem sub2070 (p : Pattern) : d75 (change p 71 (some 49)) = d75 p := by
  change (if p 161 then d74 (change p 71 (some 49)) else d69 (change p 71 (some 49))) = d75 p
  rw [sub2069, sub2064]
  rfl
theorem sub2071 (p : Pattern) : d76 (change p 71 (some 49)) = d76 p := by
  change (if p 160 then d75 (change p 71 (some 49)) else d65 (change p 71 (some 49))) = d76 p
  rw [sub2070, sub2060]
  rfl
theorem sub2072 (p : Pattern) : d77 (change p 71 (some 49)) = d77 p := by
  change (if p 141 then d76 (change p 71 (some 49)) else d52 (change p 71 (some 49))) = d77 p
  rw [sub2071, sub2046]
  rfl
theorem sub2073 (p : Pattern) : d78 (change p 71 (some 49)) = d78 p := by
  change (if p 182 then d36 (change p 71 (some 49)) else d35 (change p 71 (some 49))) = d78 p
  rw [sub2029, sub2028]
  rfl
theorem sub2074 (p : Pattern) : d79 (change p 71 (some 49)) = d79 p := by
  change (if p 163 then d78 (change p 71 (some 49)) else d53 (change p 71 (some 49))) = d79 p
  rw [sub2073, sub2047]
  rfl
theorem sub2075 (p : Pattern) : d80 (change p 71 (some 49)) = d80 p := by
  change (if p 162 then d63 (change p 71 (some 49)) else d79 (change p 71 (some 49))) = d80 p
  rw [sub2058, sub2074]
  rfl
theorem sub2076 (p : Pattern) : d81 (change p 71 (some 49)) = d81 p := by
  change (if p 161 then d12 (change p 71 (some 49)) else d80 (change p 71 (some 49))) = d81 p
  rw [sub2001, sub2075]
  rfl
theorem sub2077 (p : Pattern) : d82 (change p 71 (some 49)) = d82 p := by
  change (if p 160 then d81 (change p 71 (some 49)) else d29 (change p 71 (some 49))) = d82 p
  rw [sub2076, sub2020]
  rfl
theorem sub2078 (p : Pattern) : d83 (change p 71 (some 49)) = d83 p := by
  change (if p 163 then d12 (change p 71 (some 49)) else d78 (change p 71 (some 49))) = d83 p
  rw [sub2001, sub2073]
  rfl
theorem sub2079 (p : Pattern) : d84 (change p 71 (some 49)) = d84 p := by
  change (if p 162 then d12 (change p 71 (some 49)) else d83 (change p 71 (some 49))) = d84 p
  rw [sub2001, sub2078]
  rfl
theorem sub2080 (p : Pattern) : d85 (change p 71 (some 49)) = d85 p := by
  change (if p 161 then d12 (change p 71 (some 49)) else d84 (change p 71 (some 49))) = d85 p
  rw [sub2001, sub2079]
  rfl
theorem sub2081 (p : Pattern) : d86 (change p 71 (some 49)) = d86 p := by
  change (if p 160 then d85 (change p 71 (some 49)) else d65 (change p 71 (some 49))) = d86 p
  rw [sub2080, sub2060]
  rfl
theorem sub2082 (p : Pattern) : d87 (change p 71 (some 49)) = d87 p := by
  change (if p 141 then d86 (change p 71 (some 49)) else d82 (change p 71 (some 49))) = d87 p
  rw [sub2081, sub2077]
  rfl
theorem sub2083 (p : Pattern) : d88 (change p 71 (some 49)) = d88 p := by
  change (if p 138 then d87 (change p 71 (some 49)) else d77 (change p 71 (some 49))) = d88 p
  rw [sub2082, sub2072]
  rfl
theorem sub2084 (p : Pattern) : d89 (change p 71 (some 49)) = d89 p := by
  change (if p 163 then d62 (change p 71 (some 49)) else d26 (change p 71 (some 49))) = d89 p
  rw [sub2057, sub2017]
  rfl
theorem sub2085 (p : Pattern) : d90 (change p 71 (some 49)) = d90 p := by
  change (if p 162 then d63 (change p 71 (some 49)) else d89 (change p 71 (some 49))) = d90 p
  rw [sub2058, sub2084]
  rfl
theorem sub2086 (p : Pattern) : d91 (change p 71 (some 49)) = d91 p := by
  change (if p 162 then d12 (change p 71 (some 49)) else d63 (change p 71 (some 49))) = d91 p
  rw [sub2001, sub2058]
  rfl
theorem sub2087 (p : Pattern) : d92 (change p 71 (some 49)) = d92 p := by
  change (if p 161 then d91 (change p 71 (some 49)) else d90 (change p 71 (some 49))) = d92 p
  rw [sub2086, sub2085]
  rfl
theorem sub2088 (p : Pattern) : d93 (change p 71 (some 49)) = d93 p := by
  change (if p 161 then d12 (change p 71 (some 49)) else d91 (change p 71 (some 49))) = d93 p
  rw [sub2001, sub2086]
  rfl
theorem sub2089 (p : Pattern) : d94 (change p 71 (some 49)) = d94 p := by
  change (if p 160 then d93 (change p 71 (some 49)) else d92 (change p 71 (some 49))) = d94 p
  rw [sub2088, sub2087]
  rfl
theorem sub2090 (p : Pattern) : d95 (change p 71 (some 49)) = d95 p := by
  change (if p 160 then d12 (change p 71 (some 49)) else d93 (change p 71 (some 49))) = d95 p
  rw [sub2001, sub2088]
  rfl
theorem sub2091 (p : Pattern) : d96 (change p 71 (some 49)) = d96 p := by
  change (if p 141 then d95 (change p 71 (some 49)) else d94 (change p 71 (some 49))) = d96 p
  rw [sub2090, sub2089]
  rfl
theorem sub2092 (p : Pattern) : d97 (change p 71 (some 49)) = d97 p := by
  change (if p 138 then d96 (change p 71 (some 49)) else d87 (change p 71 (some 49))) = d97 p
  rw [sub2091, sub2082]
  rfl
theorem sub2093 (p : Pattern) : d98 (change p 71 (some 49)) = d98 p := by
  change (if p 116 then d97 (change p 71 (some 49)) else d88 (change p 71 (some 49))) = d98 p
  rw [sub2092, sub2083]
  rfl
theorem sub2094 (p : Pattern) : d99 (change p 71 (some 49)) = d99 p := by
  change (if p 138 then d12 (change p 71 (some 49)) else d87 (change p 71 (some 49))) = d99 p
  rw [sub2001, sub2082]
  rfl
theorem sub2095 (p : Pattern) : d100 (change p 71 (some 49)) = d100 p := by
  change (if p 116 then d99 (change p 71 (some 49)) else d88 (change p 71 (some 49))) = d100 p
  rw [sub2094, sub2083]
  rfl
theorem sub2096 (p : Pattern) : d101 (change p 71 (some 49)) = d101 p := by
  change (if p 115 then d100 (change p 71 (some 49)) else d98 (change p 71 (some 49))) = d101 p
  rw [sub2095, sub2093]
  rfl
theorem sub2097 (p : Pattern) : d485 (change p 71 (some 49)) = d101 p := by
  change d101 (change p 71 (some 49)) = d101 p
  exact sub2096 p
theorem sub2098 (p : Pattern) : d486 (change p 71 (some 49)) = d101 p := by
  change d101 (change p 71 (some 49)) = d101 p
  exact sub2096 p
theorem sub2099 (p : Pattern) : d487 (change p 71 (some 49)) = d101 p := by
  change d486 (change p 71 (some 49)) = d101 p
  exact sub2098 p
theorem sub2100 (p : Pattern) : d488 (change p 71 (some 49)) = d101 p := by
  change (if p 48 then d487 (change p 71 (some 49)) else d485 (change p 71 (some 49))) = d101 p
  rw [sub2099, sub2097]
  simp only [ite_self]
theorem sub2101 (p : Pattern) : d0 (change p 116 (some 138)) = d0 p := by
  rfl
theorem sub2102 (p : Pattern) : d12 (change p 116 (some 138)) = d12 p := by
  rfl
theorem sub2103 (p : Pattern) : d13 (change p 116 (some 138)) = d13 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d0 (change p 116 (some 138))) = d13 p
  rw [sub2102, sub2101]
  rfl
theorem sub2104 (p : Pattern) : d14 (change p 116 (some 138)) = d14 p := by
  change (if p 246 then d13 (change p 116 (some 138)) else d0 (change p 116 (some 138))) = d14 p
  rw [sub2103, sub2101]
  rfl
theorem sub2105 (p : Pattern) : d15 (change p 116 (some 138)) = d15 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d14 (change p 116 (some 138))) = d15 p
  rw [sub2102, sub2104]
  rfl
theorem sub2106 (p : Pattern) : d16 (change p 116 (some 138)) = d16 p := by
  change (if p 182 then d15 (change p 116 (some 138)) else d14 (change p 116 (some 138))) = d16 p
  rw [sub2105, sub2104]
  rfl
theorem sub2107 (p : Pattern) : d4 (change p 116 (some 138)) = d4 p := by
  rfl
theorem sub2108 (p : Pattern) : d17 (change p 116 (some 138)) = d17 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d4 (change p 116 (some 138))) = d17 p
  rw [sub2102, sub2107]
  rfl
theorem sub2109 (p : Pattern) : d18 (change p 116 (some 138)) = d18 p := by
  change (if p 246 then d17 (change p 116 (some 138)) else d4 (change p 116 (some 138))) = d18 p
  rw [sub2108, sub2107]
  rfl
theorem sub2110 (p : Pattern) : d19 (change p 116 (some 138)) = d19 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d18 (change p 116 (some 138))) = d19 p
  rw [sub2102, sub2109]
  rfl
theorem sub2111 (p : Pattern) : d20 (change p 116 (some 138)) = d20 p := by
  change (if p 182 then d19 (change p 116 (some 138)) else d18 (change p 116 (some 138))) = d20 p
  rw [sub2110, sub2109]
  rfl
theorem sub2112 (p : Pattern) : d21 (change p 116 (some 138)) = d21 p := by
  change (if p 163 then d20 (change p 116 (some 138)) else d16 (change p 116 (some 138))) = d21 p
  rw [sub2111, sub2106]
  rfl
theorem sub2113 (p : Pattern) : d22 (change p 116 (some 138)) = d22 p := by
  change (if p 162 then d21 (change p 116 (some 138)) else d16 (change p 116 (some 138))) = d22 p
  rw [sub2112, sub2106]
  rfl
theorem sub2114 (p : Pattern) : d9 (change p 116 (some 138)) = d9 p := by
  rfl
theorem sub2115 (p : Pattern) : d23 (change p 116 (some 138)) = d23 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d9 (change p 116 (some 138))) = d23 p
  rw [sub2102, sub2114]
  rfl
theorem sub2116 (p : Pattern) : d24 (change p 116 (some 138)) = d24 p := by
  change (if p 246 then d23 (change p 116 (some 138)) else d9 (change p 116 (some 138))) = d24 p
  rw [sub2115, sub2114]
  rfl
theorem sub2117 (p : Pattern) : d25 (change p 116 (some 138)) = d25 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d24 (change p 116 (some 138))) = d25 p
  rw [sub2102, sub2116]
  rfl
theorem sub2118 (p : Pattern) : d26 (change p 116 (some 138)) = d26 p := by
  change (if p 182 then d25 (change p 116 (some 138)) else d24 (change p 116 (some 138))) = d26 p
  rw [sub2117, sub2116]
  rfl
theorem sub2119 (p : Pattern) : d27 (change p 116 (some 138)) = d27 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d26 (change p 116 (some 138))) = d27 p
  rw [sub2102, sub2118]
  rfl
theorem sub2120 (p : Pattern) : d28 (change p 116 (some 138)) = d28 p := by
  change (if p 162 then d27 (change p 116 (some 138)) else d21 (change p 116 (some 138))) = d28 p
  rw [sub2119, sub2112]
  rfl
theorem sub2121 (p : Pattern) : d29 (change p 116 (some 138)) = d29 p := by
  change (if p 161 then d28 (change p 116 (some 138)) else d22 (change p 116 (some 138))) = d29 p
  rw [sub2120, sub2113]
  rfl
theorem sub2122 (p : Pattern) : d2 (change p 116 (some 138)) = d2 p := by
  rfl
theorem sub2123 (p : Pattern) : d30 (change p 116 (some 138)) = d30 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d2 (change p 116 (some 138))) = d30 p
  rw [sub2102, sub2122]
  rfl
theorem sub2124 (p : Pattern) : d31 (change p 116 (some 138)) = d31 p := by
  change (if p 246 then d30 (change p 116 (some 138)) else d2 (change p 116 (some 138))) = d31 p
  rw [sub2123, sub2122]
  rfl
theorem sub2125 (p : Pattern) : d32 (change p 116 (some 138)) = d32 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d31 (change p 116 (some 138))) = d32 p
  rw [sub2102, sub2124]
  rfl
theorem sub2126 (p : Pattern) : d53 (change p 116 (some 138)) = d53 p := by
  change (if p 182 then d32 (change p 116 (some 138)) else d31 (change p 116 (some 138))) = d53 p
  rw [sub2125, sub2124]
  rfl
theorem sub2127 (p : Pattern) : d6 (change p 116 (some 138)) = d6 p := by
  rfl
theorem sub2128 (p : Pattern) : d34 (change p 116 (some 138)) = d34 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d6 (change p 116 (some 138))) = d34 p
  rw [sub2102, sub2127]
  rfl
theorem sub2129 (p : Pattern) : d35 (change p 116 (some 138)) = d35 p := by
  change (if p 246 then d34 (change p 116 (some 138)) else d6 (change p 116 (some 138))) = d35 p
  rw [sub2128, sub2127]
  rfl
theorem sub2130 (p : Pattern) : d36 (change p 116 (some 138)) = d36 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d35 (change p 116 (some 138))) = d36 p
  rw [sub2102, sub2129]
  rfl
theorem sub2131 (p : Pattern) : d78 (change p 116 (some 138)) = d78 p := by
  change (if p 182 then d36 (change p 116 (some 138)) else d35 (change p 116 (some 138))) = d78 p
  rw [sub2130, sub2129]
  rfl
theorem sub2132 (p : Pattern) : d79 (change p 116 (some 138)) = d79 p := by
  change (if p 163 then d78 (change p 116 (some 138)) else d53 (change p 116 (some 138))) = d79 p
  rw [sub2131, sub2126]
  rfl
theorem sub2133 (p : Pattern) : d11 (change p 116 (some 138)) = d11 p := by
  rfl
theorem sub2134 (p : Pattern) : d39 (change p 116 (some 138)) = d39 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d11 (change p 116 (some 138))) = d39 p
  rw [sub2102, sub2133]
  rfl
theorem sub2135 (p : Pattern) : d40 (change p 116 (some 138)) = d40 p := by
  change (if p 246 then d39 (change p 116 (some 138)) else d11 (change p 116 (some 138))) = d40 p
  rw [sub2134, sub2133]
  rfl
theorem sub2136 (p : Pattern) : d41 (change p 116 (some 138)) = d41 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d40 (change p 116 (some 138))) = d41 p
  rw [sub2102, sub2135]
  rfl
theorem sub2137 (p : Pattern) : d62 (change p 116 (some 138)) = d62 p := by
  change (if p 182 then d41 (change p 116 (some 138)) else d40 (change p 116 (some 138))) = d62 p
  rw [sub2136, sub2135]
  rfl
theorem sub2138 (p : Pattern) : d63 (change p 116 (some 138)) = d63 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d62 (change p 116 (some 138))) = d63 p
  rw [sub2102, sub2137]
  rfl
theorem sub2139 (p : Pattern) : d80 (change p 116 (some 138)) = d80 p := by
  change (if p 162 then d63 (change p 116 (some 138)) else d79 (change p 116 (some 138))) = d80 p
  rw [sub2138, sub2132]
  rfl
theorem sub2140 (p : Pattern) : d81 (change p 116 (some 138)) = d81 p := by
  change (if p 161 then d12 (change p 116 (some 138)) else d80 (change p 116 (some 138))) = d81 p
  rw [sub2102, sub2139]
  rfl
theorem sub2141 (p : Pattern) : d82 (change p 116 (some 138)) = d82 p := by
  change (if p 160 then d81 (change p 116 (some 138)) else d29 (change p 116 (some 138))) = d82 p
  rw [sub2140, sub2121]
  rfl
theorem sub2142 (p : Pattern) : d54 (change p 116 (some 138)) = d54 p := by
  change (if p 163 then d53 (change p 116 (some 138)) else d16 (change p 116 (some 138))) = d54 p
  rw [sub2126, sub2106]
  rfl
theorem sub2143 (p : Pattern) : d55 (change p 116 (some 138)) = d55 p := by
  change (if p 163 then d26 (change p 116 (some 138)) else d20 (change p 116 (some 138))) = d55 p
  rw [sub2118, sub2111]
  rfl
theorem sub2144 (p : Pattern) : d56 (change p 116 (some 138)) = d56 p := by
  change (if p 162 then d55 (change p 116 (some 138)) else d54 (change p 116 (some 138))) = d56 p
  rw [sub2143, sub2142]
  rfl
theorem sub2145 (p : Pattern) : d10 (change p 116 (some 138)) = d10 p := by
  rfl
theorem sub2146 (p : Pattern) : d57 (change p 116 (some 138)) = d57 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d10 (change p 116 (some 138))) = d57 p
  rw [sub2102, sub2145]
  rfl
theorem sub2147 (p : Pattern) : d58 (change p 116 (some 138)) = d58 p := by
  change (if p 246 then d57 (change p 116 (some 138)) else d10 (change p 116 (some 138))) = d58 p
  rw [sub2146, sub2145]
  rfl
theorem sub2148 (p : Pattern) : d59 (change p 116 (some 138)) = d59 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d58 (change p 116 (some 138))) = d59 p
  rw [sub2102, sub2147]
  rfl
theorem sub2149 (p : Pattern) : d60 (change p 116 (some 138)) = d60 p := by
  change (if p 182 then d59 (change p 116 (some 138)) else d58 (change p 116 (some 138))) = d60 p
  rw [sub2148, sub2147]
  rfl
theorem sub2150 (p : Pattern) : d61 (change p 116 (some 138)) = d61 p := by
  change (if p 163 then d60 (change p 116 (some 138)) else d20 (change p 116 (some 138))) = d61 p
  rw [sub2149, sub2111]
  rfl
theorem sub2151 (p : Pattern) : d64 (change p 116 (some 138)) = d64 p := by
  change (if p 162 then d63 (change p 116 (some 138)) else d61 (change p 116 (some 138))) = d64 p
  rw [sub2138, sub2150]
  rfl
theorem sub2152 (p : Pattern) : d65 (change p 116 (some 138)) = d65 p := by
  change (if p 161 then d64 (change p 116 (some 138)) else d56 (change p 116 (some 138))) = d65 p
  rw [sub2151, sub2144]
  rfl
theorem sub2153 (p : Pattern) : d83 (change p 116 (some 138)) = d83 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d78 (change p 116 (some 138))) = d83 p
  rw [sub2102, sub2131]
  rfl
theorem sub2154 (p : Pattern) : d84 (change p 116 (some 138)) = d84 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d83 (change p 116 (some 138))) = d84 p
  rw [sub2102, sub2153]
  rfl
theorem sub2155 (p : Pattern) : d85 (change p 116 (some 138)) = d85 p := by
  change (if p 161 then d12 (change p 116 (some 138)) else d84 (change p 116 (some 138))) = d85 p
  rw [sub2102, sub2154]
  rfl
theorem sub2156 (p : Pattern) : d86 (change p 116 (some 138)) = d86 p := by
  change (if p 160 then d85 (change p 116 (some 138)) else d65 (change p 116 (some 138))) = d86 p
  rw [sub2155, sub2152]
  rfl
theorem sub2157 (p : Pattern) : d87 (change p 116 (some 138)) = d87 p := by
  change (if p 141 then d86 (change p 116 (some 138)) else d82 (change p 116 (some 138))) = d87 p
  rw [sub2156, sub2141]
  rfl
theorem sub2158 (p : Pattern) : d88 (change p 116 (some 138)) = d87 p := by
  change d87 (change p 116 (some 138)) = d87 p
  exact sub2157 p
theorem sub2159 (p : Pattern) : d499 (change p 116 (some 138)) = d87 p := by
  change d88 (change p 116 (some 138)) = d87 p
  exact sub2158 p
end NetHack.Sokoban22Refined85
