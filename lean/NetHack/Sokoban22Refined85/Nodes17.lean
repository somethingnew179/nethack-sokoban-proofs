/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2040 (p : Pattern) : Int := if p 163 then d538 p else d2022 p
theorem agree2040 (p q : Pattern) (h : Agree support p q) : d2040 p = d2040 q := by
  simp only [d2040, h 163 (by decide), agree538 p q h, agree2022 p q h]
theorem nonnegative2040 (p : Pattern) : 0 ≤ d2040 p :=
  nonnegative_ite (p 163) (nonnegative538 p) (nonnegative2022 p)
def d2041 (p : Pattern) : Int := if p 162 then d2040 p else d2039 p
theorem agree2041 (p q : Pattern) (h : Agree support p q) : d2041 p = d2041 q := by
  simp only [d2041, h 162 (by decide), agree2040 p q h, agree2039 p q h]
theorem nonnegative2041 (p : Pattern) : 0 ≤ d2041 p :=
  nonnegative_ite (p 162) (nonnegative2040 p) (nonnegative2039 p)
def d2042 (p : Pattern) : Int := if p 163 then d12 p else d2022 p
theorem agree2042 (p q : Pattern) (h : Agree support p q) : d2042 p = d2042 q := by
  simp only [d2042, h 163 (by decide), agree12 p q h, agree2022 p q h]
theorem nonnegative2042 (p : Pattern) : 0 ≤ d2042 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2022 p)
def d2043 (p : Pattern) : Int := if p 162 then d12 p else d2042 p
theorem agree2043 (p q : Pattern) (h : Agree support p q) : d2043 p = d2043 q := by
  simp only [d2043, h 162 (by decide), agree12 p q h, agree2042 p q h]
theorem nonnegative2043 (p : Pattern) : 0 ≤ d2043 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2042 p)
def d2044 (p : Pattern) : Int := if p 161 then d2043 p else d2041 p
theorem agree2044 (p q : Pattern) (h : Agree support p q) : d2044 p = d2044 q := by
  simp only [d2044, h 161 (by decide), agree2043 p q h, agree2041 p q h]
theorem nonnegative2044 (p : Pattern) : 0 ≤ d2044 p :=
  nonnegative_ite (p 161) (nonnegative2043 p) (nonnegative2041 p)
def d2045 (p : Pattern) : Int := if p 160 then d2044 p else d2038 p
theorem agree2045 (p q : Pattern) (h : Agree support p q) : d2045 p = d2045 q := by
  simp only [d2045, h 160 (by decide), agree2044 p q h, agree2038 p q h]
theorem nonnegative2045 (p : Pattern) : 0 ≤ d2045 p :=
  nonnegative_ite (p 160) (nonnegative2044 p) (nonnegative2038 p)
def d2046 (p : Pattern) : Int := if p 141 then d2045 p else d2028 p
theorem agree2046 (p q : Pattern) (h : Agree support p q) : d2046 p = d2046 q := by
  simp only [d2046, h 141 (by decide), agree2045 p q h, agree2028 p q h]
theorem nonnegative2046 (p : Pattern) : 0 ≤ d2046 p :=
  nonnegative_ite (p 141) (nonnegative2045 p) (nonnegative2028 p)
def d2047 (p : Pattern) : Int := if p 225 then d1776 p else d1770 p
theorem agree2047 (p q : Pattern) (h : Agree support p q) : d2047 p = d2047 q := by
  simp only [d2047, h 225 (by decide), agree1776 p q h, agree1770 p q h]
theorem nonnegative2047 (p : Pattern) : 0 ≤ d2047 p :=
  nonnegative_ite (p 225) (nonnegative1776 p) (nonnegative1770 p)
def d2048 (p : Pattern) : Int := if p 224 then d2047 p else d1777 p
theorem agree2048 (p q : Pattern) (h : Agree support p q) : d2048 p = d2048 q := by
  simp only [d2048, h 224 (by decide), agree2047 p q h, agree1777 p q h]
theorem nonnegative2048 (p : Pattern) : 0 ≤ d2048 p :=
  nonnegative_ite (p 224) (nonnegative2047 p) (nonnegative1777 p)
def d2049 (p : Pattern) : Int := if p 204 then d12 p else d2048 p
theorem agree2049 (p q : Pattern) (h : Agree support p q) : d2049 p = d2049 q := by
  simp only [d2049, h 204 (by decide), agree12 p q h, agree2048 p q h]
theorem nonnegative2049 (p : Pattern) : 0 ≤ d2049 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2048 p)
def d2050 (p : Pattern) : Int := if p 182 then d2049 p else d15 p
theorem agree2050 (p q : Pattern) (h : Agree support p q) : d2050 p = d2050 q := by
  simp only [d2050, h 182 (by decide), agree2049 p q h, agree15 p q h]
theorem nonnegative2050 (p : Pattern) : 0 ≤ d2050 p :=
  nonnegative_ite (p 182) (nonnegative2049 p) (nonnegative15 p)
def d2051 (p : Pattern) : Int := if p 247 then d10 p else d0 p
theorem agree2051 (p q : Pattern) (h : Agree support p q) : d2051 p = d2051 q := by
  simp only [d2051, h 247 (by decide), agree10 p q h, agree0 p q h]
theorem nonnegative2051 (p : Pattern) : 0 ≤ d2051 p :=
  nonnegative_ite (p 247) (nonnegative10 p) (nonnegative0 p)
def d2052 (p : Pattern) : Int := if p 246 then d23 p else d2051 p
theorem agree2052 (p q : Pattern) (h : Agree support p q) : d2052 p = d2052 q := by
  simp only [d2052, h 246 (by decide), agree23 p q h, agree2051 p q h]
theorem nonnegative2052 (p : Pattern) : 0 ≤ d2052 p :=
  nonnegative_ite (p 246) (nonnegative23 p) (nonnegative2051 p)
def d2053 (p : Pattern) : Int := if p 225 then d2052 p else d1770 p
theorem agree2053 (p q : Pattern) (h : Agree support p q) : d2053 p = d2053 q := by
  simp only [d2053, h 225 (by decide), agree2052 p q h, agree1770 p q h]
theorem nonnegative2053 (p : Pattern) : 0 ≤ d2053 p :=
  nonnegative_ite (p 225) (nonnegative2052 p) (nonnegative1770 p)
def d2054 (p : Pattern) : Int := if p 224 then d2053 p else d1777 p
theorem agree2054 (p q : Pattern) (h : Agree support p q) : d2054 p = d2054 q := by
  simp only [d2054, h 224 (by decide), agree2053 p q h, agree1777 p q h]
theorem nonnegative2054 (p : Pattern) : 0 ≤ d2054 p :=
  nonnegative_ite (p 224) (nonnegative2053 p) (nonnegative1777 p)
def d2055 (p : Pattern) : Int := if p 204 then d12 p else d2054 p
theorem agree2055 (p q : Pattern) (h : Agree support p q) : d2055 p = d2055 q := by
  simp only [d2055, h 204 (by decide), agree12 p q h, agree2054 p q h]
theorem nonnegative2055 (p : Pattern) : 0 ≤ d2055 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2054 p)
def d2056 (p : Pattern) : Int := if p 182 then d2055 p else d15 p
theorem agree2056 (p q : Pattern) (h : Agree support p q) : d2056 p = d2056 q := by
  simp only [d2056, h 182 (by decide), agree2055 p q h, agree15 p q h]
theorem nonnegative2056 (p : Pattern) : 0 ≤ d2056 p :=
  nonnegative_ite (p 182) (nonnegative2055 p) (nonnegative15 p)
def d2057 (p : Pattern) : Int := if p 163 then d2056 p else d2050 p
theorem agree2057 (p q : Pattern) (h : Agree support p q) : d2057 p = d2057 q := by
  simp only [d2057, h 163 (by decide), agree2056 p q h, agree2050 p q h]
theorem nonnegative2057 (p : Pattern) : 0 ≤ d2057 p :=
  nonnegative_ite (p 163) (nonnegative2056 p) (nonnegative2050 p)
def d2058 (p : Pattern) : Int := if p 162 then d1811 p else d2057 p
theorem agree2058 (p q : Pattern) (h : Agree support p q) : d2058 p = d2058 q := by
  simp only [d2058, h 162 (by decide), agree1811 p q h, agree2057 p q h]
theorem nonnegative2058 (p : Pattern) : 0 ≤ d2058 p :=
  nonnegative_ite (p 162) (nonnegative1811 p) (nonnegative2057 p)
def d2059 (p : Pattern) : Int := if p 161 then d1812 p else d2058 p
theorem agree2059 (p q : Pattern) (h : Agree support p q) : d2059 p = d2059 q := by
  simp only [d2059, h 161 (by decide), agree1812 p q h, agree2058 p q h]
theorem nonnegative2059 (p : Pattern) : 0 ≤ d2059 p :=
  nonnegative_ite (p 161) (nonnegative1812 p) (nonnegative2058 p)
def d2060 (p : Pattern) : Int := if p 225 then d315 p else d191 p
theorem agree2060 (p q : Pattern) (h : Agree support p q) : d2060 p = d2060 q := by
  simp only [d2060, h 225 (by decide), agree315 p q h, agree191 p q h]
theorem nonnegative2060 (p : Pattern) : 0 ≤ d2060 p :=
  nonnegative_ite (p 225) (nonnegative315 p) (nonnegative191 p)
def d2061 (p : Pattern) : Int := if p 224 then d315 p else d2060 p
theorem agree2061 (p q : Pattern) (h : Agree support p q) : d2061 p = d2061 q := by
  simp only [d2061, h 224 (by decide), agree315 p q h, agree2060 p q h]
theorem nonnegative2061 (p : Pattern) : 0 ≤ d2061 p :=
  nonnegative_ite (p 224) (nonnegative315 p) (nonnegative2060 p)
def d2062 (p : Pattern) : Int := if p 204 then d12 p else d2061 p
theorem agree2062 (p q : Pattern) (h : Agree support p q) : d2062 p = d2062 q := by
  simp only [d2062, h 204 (by decide), agree12 p q h, agree2061 p q h]
theorem nonnegative2062 (p : Pattern) : 0 ≤ d2062 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2061 p)
def d2063 (p : Pattern) : Int := if p 182 then d2062 p else d192 p
theorem agree2063 (p q : Pattern) (h : Agree support p q) : d2063 p = d2063 q := by
  simp only [d2063, h 182 (by decide), agree2062 p q h, agree192 p q h]
theorem nonnegative2063 (p : Pattern) : 0 ≤ d2063 p :=
  nonnegative_ite (p 182) (nonnegative2062 p) (nonnegative192 p)
def d2064 (p : Pattern) : Int := if p 163 then d2063 p else d1799 p
theorem agree2064 (p q : Pattern) (h : Agree support p q) : d2064 p = d2064 q := by
  simp only [d2064, h 163 (by decide), agree2063 p q h, agree1799 p q h]
theorem nonnegative2064 (p : Pattern) : 0 ≤ d2064 p :=
  nonnegative_ite (p 163) (nonnegative2063 p) (nonnegative1799 p)
def d2065 (p : Pattern) : Int := if p 162 then d12 p else d2064 p
theorem agree2065 (p q : Pattern) (h : Agree support p q) : d2065 p = d2065 q := by
  simp only [d2065, h 162 (by decide), agree12 p q h, agree2064 p q h]
theorem nonnegative2065 (p : Pattern) : 0 ≤ d2065 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2064 p)
def d2066 (p : Pattern) : Int := if p 161 then d12 p else d2065 p
theorem agree2066 (p q : Pattern) (h : Agree support p q) : d2066 p = d2066 q := by
  simp only [d2066, h 161 (by decide), agree12 p q h, agree2065 p q h]
theorem nonnegative2066 (p : Pattern) : 0 ≤ d2066 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2065 p)
def d2067 (p : Pattern) : Int := if p 160 then d2066 p else d2059 p
theorem agree2067 (p q : Pattern) (h : Agree support p q) : d2067 p = d2067 q := by
  simp only [d2067, h 160 (by decide), agree2066 p q h, agree2059 p q h]
theorem nonnegative2067 (p : Pattern) : 0 ≤ d2067 p :=
  nonnegative_ite (p 160) (nonnegative2066 p) (nonnegative2059 p)
def d2068 (p : Pattern) : Int := if p 247 then d10 p else d2 p
theorem agree2068 (p q : Pattern) (h : Agree support p q) : d2068 p = d2068 q := by
  simp only [d2068, h 247 (by decide), agree10 p q h, agree2 p q h]
theorem nonnegative2068 (p : Pattern) : 0 ≤ d2068 p :=
  nonnegative_ite (p 247) (nonnegative10 p) (nonnegative2 p)
def d2069 (p : Pattern) : Int := if p 246 then d57 p else d2068 p
theorem agree2069 (p q : Pattern) (h : Agree support p q) : d2069 p = d2069 q := by
  simp only [d2069, h 246 (by decide), agree57 p q h, agree2068 p q h]
theorem nonnegative2069 (p : Pattern) : 0 ≤ d2069 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative2068 p)
def d2070 (p : Pattern) : Int := if p 225 then d2069 p else d1714 p
theorem agree2070 (p q : Pattern) (h : Agree support p q) : d2070 p = d2070 q := by
  simp only [d2070, h 225 (by decide), agree2069 p q h, agree1714 p q h]
theorem nonnegative2070 (p : Pattern) : 0 ≤ d2070 p :=
  nonnegative_ite (p 225) (nonnegative2069 p) (nonnegative1714 p)
def d2071 (p : Pattern) : Int := if p 224 then d2070 p else d1712 p
theorem agree2071 (p q : Pattern) (h : Agree support p q) : d2071 p = d2071 q := by
  simp only [d2071, h 224 (by decide), agree2070 p q h, agree1712 p q h]
theorem nonnegative2071 (p : Pattern) : 0 ≤ d2071 p :=
  nonnegative_ite (p 224) (nonnegative2070 p) (nonnegative1712 p)
def d2072 (p : Pattern) : Int := if p 204 then d12 p else d2071 p
theorem agree2072 (p q : Pattern) (h : Agree support p q) : d2072 p = d2072 q := by
  simp only [d2072, h 204 (by decide), agree12 p q h, agree2071 p q h]
theorem nonnegative2072 (p : Pattern) : 0 ≤ d2072 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2071 p)
def d2073 (p : Pattern) : Int := if p 182 then d2072 p else d32 p
theorem agree2073 (p q : Pattern) (h : Agree support p q) : d2073 p = d2073 q := by
  simp only [d2073, h 182 (by decide), agree2072 p q h, agree32 p q h]
theorem nonnegative2073 (p : Pattern) : 0 ≤ d2073 p :=
  nonnegative_ite (p 182) (nonnegative2072 p) (nonnegative32 p)
def d2074 (p : Pattern) : Int := if p 163 then d1809 p else d2073 p
theorem agree2074 (p q : Pattern) (h : Agree support p q) : d2074 p = d2074 q := by
  simp only [d2074, h 163 (by decide), agree1809 p q h, agree2073 p q h]
theorem nonnegative2074 (p : Pattern) : 0 ≤ d2074 p :=
  nonnegative_ite (p 163) (nonnegative1809 p) (nonnegative2073 p)
def d2075 (p : Pattern) : Int := if p 163 then d1756 p else d1799 p
theorem agree2075 (p q : Pattern) (h : Agree support p q) : d2075 p = d2075 q := by
  simp only [d2075, h 163 (by decide), agree1756 p q h, agree1799 p q h]
theorem nonnegative2075 (p : Pattern) : 0 ≤ d2075 p :=
  nonnegative_ite (p 163) (nonnegative1756 p) (nonnegative1799 p)
def d2076 (p : Pattern) : Int := if p 162 then d2075 p else d2074 p
theorem agree2076 (p q : Pattern) (h : Agree support p q) : d2076 p = d2076 q := by
  simp only [d2076, h 162 (by decide), agree2075 p q h, agree2074 p q h]
theorem nonnegative2076 (p : Pattern) : 0 ≤ d2076 p :=
  nonnegative_ite (p 162) (nonnegative2075 p) (nonnegative2074 p)
def d2077 (p : Pattern) : Int := if p 161 then d1822 p else d2076 p
theorem agree2077 (p q : Pattern) (h : Agree support p q) : d2077 p = d2077 q := by
  simp only [d2077, h 161 (by decide), agree1822 p q h, agree2076 p q h]
theorem nonnegative2077 (p : Pattern) : 0 ≤ d2077 p :=
  nonnegative_ite (p 161) (nonnegative1822 p) (nonnegative2076 p)
def d2078 (p : Pattern) : Int := if p 163 then d12 p else d2063 p
theorem agree2078 (p q : Pattern) (h : Agree support p q) : d2078 p = d2078 q := by
  simp only [d2078, h 163 (by decide), agree12 p q h, agree2063 p q h]
theorem nonnegative2078 (p : Pattern) : 0 ≤ d2078 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2063 p)
def d2079 (p : Pattern) : Int := if p 162 then d12 p else d2078 p
theorem agree2079 (p q : Pattern) (h : Agree support p q) : d2079 p = d2079 q := by
  simp only [d2079, h 162 (by decide), agree12 p q h, agree2078 p q h]
theorem nonnegative2079 (p : Pattern) : 0 ≤ d2079 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2078 p)
def d2080 (p : Pattern) : Int := if p 161 then d12 p else d2079 p
theorem agree2080 (p q : Pattern) (h : Agree support p q) : d2080 p = d2080 q := by
  simp only [d2080, h 161 (by decide), agree12 p q h, agree2079 p q h]
theorem nonnegative2080 (p : Pattern) : 0 ≤ d2080 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2079 p)
def d2081 (p : Pattern) : Int := if p 160 then d2080 p else d2077 p
theorem agree2081 (p q : Pattern) (h : Agree support p q) : d2081 p = d2081 q := by
  simp only [d2081, h 160 (by decide), agree2080 p q h, agree2077 p q h]
theorem nonnegative2081 (p : Pattern) : 0 ≤ d2081 p :=
  nonnegative_ite (p 160) (nonnegative2080 p) (nonnegative2077 p)
def d2082 (p : Pattern) : Int := if p 141 then d2081 p else d2067 p
theorem agree2082 (p q : Pattern) (h : Agree support p q) : d2082 p = d2082 q := by
  simp only [d2082, h 141 (by decide), agree2081 p q h, agree2067 p q h]
theorem nonnegative2082 (p : Pattern) : 0 ≤ d2082 p :=
  nonnegative_ite (p 141) (nonnegative2081 p) (nonnegative2067 p)
def d2083 (p : Pattern) : Int := if p 138 then d2082 p else d2046 p
theorem agree2083 (p q : Pattern) (h : Agree support p q) : d2083 p = d2083 q := by
  simp only [d2083, h 138 (by decide), agree2082 p q h, agree2046 p q h]
theorem nonnegative2083 (p : Pattern) : 0 ≤ d2083 p :=
  nonnegative_ite (p 138) (nonnegative2082 p) (nonnegative2046 p)
def d2084 (p : Pattern) : Int := if p 138 then d12 p else d2082 p
theorem agree2084 (p q : Pattern) (h : Agree support p q) : d2084 p = d2084 q := by
  simp only [d2084, h 138 (by decide), agree12 p q h, agree2082 p q h]
theorem nonnegative2084 (p : Pattern) : 0 ≤ d2084 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2082 p)
def d2085 (p : Pattern) : Int := if p 116 then d2084 p else d2083 p
theorem agree2085 (p q : Pattern) (h : Agree support p q) : d2085 p = d2085 q := by
  simp only [d2085, h 116 (by decide), agree2084 p q h, agree2083 p q h]
theorem nonnegative2085 (p : Pattern) : 0 ≤ d2085 p :=
  nonnegative_ite (p 116) (nonnegative2084 p) (nonnegative2083 p)
def d2086 (p : Pattern) : Int := if p 115 then d2085 p else d1862 p
theorem agree2086 (p q : Pattern) (h : Agree support p q) : d2086 p = d2086 q := by
  simp only [d2086, h 115 (by decide), agree2085 p q h, agree1862 p q h]
theorem nonnegative2086 (p : Pattern) : 0 ≤ d2086 p :=
  nonnegative_ite (p 115) (nonnegative2085 p) (nonnegative1862 p)
def d2087 (p : Pattern) : Int := if p 71 then d2086 p else d1849 p
theorem agree2087 (p q : Pattern) (h : Agree support p q) : d2087 p = d2087 q := by
  simp only [d2087, h 71 (by decide), agree2086 p q h, agree1849 p q h]
theorem nonnegative2087 (p : Pattern) : 0 ≤ d2087 p :=
  nonnegative_ite (p 71) (nonnegative2086 p) (nonnegative1849 p)
def d2088 (p : Pattern) : Int := if p 163 then d12 p else d1885 p
theorem agree2088 (p q : Pattern) (h : Agree support p q) : d2088 p = d2088 q := by
  simp only [d2088, h 163 (by decide), agree12 p q h, agree1885 p q h]
theorem nonnegative2088 (p : Pattern) : 0 ≤ d2088 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1885 p)
def d2089 (p : Pattern) : Int := if p 162 then d2088 p else d1924 p
theorem agree2089 (p q : Pattern) (h : Agree support p q) : d2089 p = d2089 q := by
  simp only [d2089, h 162 (by decide), agree2088 p q h, agree1924 p q h]
theorem nonnegative2089 (p : Pattern) : 0 ≤ d2089 p :=
  nonnegative_ite (p 162) (nonnegative2088 p) (nonnegative1924 p)
def d2090 (p : Pattern) : Int := if p 162 then d12 p else d2088 p
theorem agree2090 (p q : Pattern) (h : Agree support p q) : d2090 p = d2090 q := by
  simp only [d2090, h 162 (by decide), agree12 p q h, agree2088 p q h]
theorem nonnegative2090 (p : Pattern) : 0 ≤ d2090 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2088 p)
def d2091 (p : Pattern) : Int := if p 161 then d2090 p else d2089 p
theorem agree2091 (p q : Pattern) (h : Agree support p q) : d2091 p = d2091 q := by
  simp only [d2091, h 161 (by decide), agree2090 p q h, agree2089 p q h]
theorem nonnegative2091 (p : Pattern) : 0 ≤ d2091 p :=
  nonnegative_ite (p 161) (nonnegative2090 p) (nonnegative2089 p)
def d2092 (p : Pattern) : Int := if p 163 then d12 p else d1910 p
theorem agree2092 (p q : Pattern) (h : Agree support p q) : d2092 p = d2092 q := by
  simp only [d2092, h 163 (by decide), agree12 p q h, agree1910 p q h]
theorem nonnegative2092 (p : Pattern) : 0 ≤ d2092 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1910 p)
def d2093 (p : Pattern) : Int := if p 162 then d2092 p else d1931 p
theorem agree2093 (p q : Pattern) (h : Agree support p q) : d2093 p = d2093 q := by
  simp only [d2093, h 162 (by decide), agree2092 p q h, agree1931 p q h]
theorem nonnegative2093 (p : Pattern) : 0 ≤ d2093 p :=
  nonnegative_ite (p 162) (nonnegative2092 p) (nonnegative1931 p)
def d2094 (p : Pattern) : Int := if p 162 then d12 p else d2092 p
theorem agree2094 (p q : Pattern) (h : Agree support p q) : d2094 p = d2094 q := by
  simp only [d2094, h 162 (by decide), agree12 p q h, agree2092 p q h]
theorem nonnegative2094 (p : Pattern) : 0 ≤ d2094 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2092 p)
def d2095 (p : Pattern) : Int := if p 161 then d2094 p else d2093 p
theorem agree2095 (p q : Pattern) (h : Agree support p q) : d2095 p = d2095 q := by
  simp only [d2095, h 161 (by decide), agree2094 p q h, agree2093 p q h]
theorem nonnegative2095 (p : Pattern) : 0 ≤ d2095 p :=
  nonnegative_ite (p 161) (nonnegative2094 p) (nonnegative2093 p)
def d2096 (p : Pattern) : Int := if p 160 then d2095 p else d2091 p
theorem agree2096 (p q : Pattern) (h : Agree support p q) : d2096 p = d2096 q := by
  simp only [d2096, h 160 (by decide), agree2095 p q h, agree2091 p q h]
theorem nonnegative2096 (p : Pattern) : 0 ≤ d2096 p :=
  nonnegative_ite (p 160) (nonnegative2095 p) (nonnegative2091 p)
def d2097 (p : Pattern) : Int := if p 141 then d2096 p else d1915 p
theorem agree2097 (p q : Pattern) (h : Agree support p q) : d2097 p = d2097 q := by
  simp only [d2097, h 141 (by decide), agree2096 p q h, agree1915 p q h]
theorem nonnegative2097 (p : Pattern) : 0 ≤ d2097 p :=
  nonnegative_ite (p 141) (nonnegative2096 p) (nonnegative1915 p)
def d2098 (p : Pattern) : Int := if p 163 then d12 p else d1968 p
theorem agree2098 (p q : Pattern) (h : Agree support p q) : d2098 p = d2098 q := by
  simp only [d2098, h 163 (by decide), agree12 p q h, agree1968 p q h]
theorem nonnegative2098 (p : Pattern) : 0 ≤ d2098 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative1968 p)
def d2099 (p : Pattern) : Int := if p 162 then d2098 p else d1979 p
theorem agree2099 (p q : Pattern) (h : Agree support p q) : d2099 p = d2099 q := by
  simp only [d2099, h 162 (by decide), agree2098 p q h, agree1979 p q h]
theorem nonnegative2099 (p : Pattern) : 0 ≤ d2099 p :=
  nonnegative_ite (p 162) (nonnegative2098 p) (nonnegative1979 p)
def d2100 (p : Pattern) : Int := if p 162 then d12 p else d2098 p
theorem agree2100 (p q : Pattern) (h : Agree support p q) : d2100 p = d2100 q := by
  simp only [d2100, h 162 (by decide), agree12 p q h, agree2098 p q h]
theorem nonnegative2100 (p : Pattern) : 0 ≤ d2100 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2098 p)
def d2101 (p : Pattern) : Int := if p 161 then d2100 p else d2099 p
theorem agree2101 (p q : Pattern) (h : Agree support p q) : d2101 p = d2101 q := by
  simp only [d2101, h 161 (by decide), agree2100 p q h, agree2099 p q h]
theorem nonnegative2101 (p : Pattern) : 0 ≤ d2101 p :=
  nonnegative_ite (p 161) (nonnegative2100 p) (nonnegative2099 p)
def d2102 (p : Pattern) : Int := if p 160 then d1987 p else d2101 p
theorem agree2102 (p q : Pattern) (h : Agree support p q) : d2102 p = d2102 q := by
  simp only [d2102, h 160 (by decide), agree1987 p q h, agree2101 p q h]
theorem nonnegative2102 (p : Pattern) : 0 ≤ d2102 p :=
  nonnegative_ite (p 160) (nonnegative1987 p) (nonnegative2101 p)
def d2103 (p : Pattern) : Int := if p 141 then d2102 p else d1978 p
theorem agree2103 (p q : Pattern) (h : Agree support p q) : d2103 p = d2103 q := by
  simp only [d2103, h 141 (by decide), agree2102 p q h, agree1978 p q h]
theorem nonnegative2103 (p : Pattern) : 0 ≤ d2103 p :=
  nonnegative_ite (p 141) (nonnegative2102 p) (nonnegative1978 p)
def d2104 (p : Pattern) : Int := if p 138 then d2103 p else d2097 p
theorem agree2104 (p q : Pattern) (h : Agree support p q) : d2104 p = d2104 q := by
  simp only [d2104, h 138 (by decide), agree2103 p q h, agree2097 p q h]
theorem nonnegative2104 (p : Pattern) : 0 ≤ d2104 p :=
  nonnegative_ite (p 138) (nonnegative2103 p) (nonnegative2097 p)
def d2105 (p : Pattern) : Int := if p 138 then d1994 p else d2103 p
theorem agree2105 (p q : Pattern) (h : Agree support p q) : d2105 p = d2105 q := by
  simp only [d2105, h 138 (by decide), agree1994 p q h, agree2103 p q h]
theorem nonnegative2105 (p : Pattern) : 0 ≤ d2105 p :=
  nonnegative_ite (p 138) (nonnegative1994 p) (nonnegative2103 p)
def d2106 (p : Pattern) : Int := if p 116 then d2105 p else d2104 p
theorem agree2106 (p q : Pattern) (h : Agree support p q) : d2106 p = d2106 q := by
  simp only [d2106, h 116 (by decide), agree2105 p q h, agree2104 p q h]
theorem nonnegative2106 (p : Pattern) : 0 ≤ d2106 p :=
  nonnegative_ite (p 116) (nonnegative2105 p) (nonnegative2104 p)
def d2107 (p : Pattern) : Int := if p 225 then d1946 p else d1940 p
theorem agree2107 (p q : Pattern) (h : Agree support p q) : d2107 p = d2107 q := by
  simp only [d2107, h 225 (by decide), agree1946 p q h, agree1940 p q h]
theorem nonnegative2107 (p : Pattern) : 0 ≤ d2107 p :=
  nonnegative_ite (p 225) (nonnegative1946 p) (nonnegative1940 p)
def d2108 (p : Pattern) : Int := if p 224 then d2107 p else d1947 p
theorem agree2108 (p q : Pattern) (h : Agree support p q) : d2108 p = d2108 q := by
  simp only [d2108, h 224 (by decide), agree2107 p q h, agree1947 p q h]
theorem nonnegative2108 (p : Pattern) : 0 ≤ d2108 p :=
  nonnegative_ite (p 224) (nonnegative2107 p) (nonnegative1947 p)
def d2109 (p : Pattern) : Int := if p 204 then d12 p else d2108 p
theorem agree2109 (p q : Pattern) (h : Agree support p q) : d2109 p = d2109 q := by
  simp only [d2109, h 204 (by decide), agree12 p q h, agree2108 p q h]
theorem nonnegative2109 (p : Pattern) : 0 ≤ d2109 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2108 p)
def d2110 (p : Pattern) : Int := if p 182 then d2109 p else d104 p
theorem agree2110 (p q : Pattern) (h : Agree support p q) : d2110 p = d2110 q := by
  simp only [d2110, h 182 (by decide), agree2109 p q h, agree104 p q h]
theorem nonnegative2110 (p : Pattern) : 0 ≤ d2110 p :=
  nonnegative_ite (p 182) (nonnegative2109 p) (nonnegative104 p)
def d2111 (p : Pattern) : Int := if p 163 then d1968 p else d2110 p
theorem agree2111 (p q : Pattern) (h : Agree support p q) : d2111 p = d2111 q := by
  simp only [d2111, h 163 (by decide), agree1968 p q h, agree2110 p q h]
theorem nonnegative2111 (p : Pattern) : 0 ≤ d2111 p :=
  nonnegative_ite (p 163) (nonnegative1968 p) (nonnegative2110 p)
def d2112 (p : Pattern) : Int := if p 162 then d2111 p else d1944 p
theorem agree2112 (p q : Pattern) (h : Agree support p q) : d2112 p = d2112 q := by
  simp only [d2112, h 162 (by decide), agree2111 p q h, agree1944 p q h]
theorem nonnegative2112 (p : Pattern) : 0 ≤ d2112 p :=
  nonnegative_ite (p 162) (nonnegative2111 p) (nonnegative1944 p)
def d2113 (p : Pattern) : Int := if p 163 then d1968 p else d1953 p
theorem agree2113 (p q : Pattern) (h : Agree support p q) : d2113 p = d2113 q := by
  simp only [d2113, h 163 (by decide), agree1968 p q h, agree1953 p q h]
theorem nonnegative2113 (p : Pattern) : 0 ≤ d2113 p :=
  nonnegative_ite (p 163) (nonnegative1968 p) (nonnegative1953 p)
def d2114 (p : Pattern) : Int := if p 162 then d1888 p else d2113 p
theorem agree2114 (p q : Pattern) (h : Agree support p q) : d2114 p = d2114 q := by
  simp only [d2114, h 162 (by decide), agree1888 p q h, agree2113 p q h]
theorem nonnegative2114 (p : Pattern) : 0 ≤ d2114 p :=
  nonnegative_ite (p 162) (nonnegative1888 p) (nonnegative2113 p)
def d2115 (p : Pattern) : Int := if p 161 then d2114 p else d2112 p
theorem agree2115 (p q : Pattern) (h : Agree support p q) : d2115 p = d2115 q := by
  simp only [d2115, h 161 (by decide), agree2114 p q h, agree2112 p q h]
theorem nonnegative2115 (p : Pattern) : 0 ≤ d2115 p :=
  nonnegative_ite (p 161) (nonnegative2114 p) (nonnegative2112 p)
def d2116 (p : Pattern) : Int := if p 182 then d1906 p else d117 p
theorem agree2116 (p q : Pattern) (h : Agree support p q) : d2116 p = d2116 q := by
  simp only [d2116, h 182 (by decide), agree1906 p q h, agree117 p q h]
theorem nonnegative2116 (p : Pattern) : 0 ≤ d2116 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative117 p)
def d2117 (p : Pattern) : Int := if p 163 then d2116 p else d1973 p
theorem agree2117 (p q : Pattern) (h : Agree support p q) : d2117 p = d2117 q := by
  simp only [d2117, h 163 (by decide), agree2116 p q h, agree1973 p q h]
theorem nonnegative2117 (p : Pattern) : 0 ≤ d2117 p :=
  nonnegative_ite (p 163) (nonnegative2116 p) (nonnegative1973 p)
def d2118 (p : Pattern) : Int := if p 162 then d2092 p else d2117 p
theorem agree2118 (p q : Pattern) (h : Agree support p q) : d2118 p = d2118 q := by
  simp only [d2118, h 162 (by decide), agree2092 p q h, agree2117 p q h]
theorem nonnegative2118 (p : Pattern) : 0 ≤ d2118 p :=
  nonnegative_ite (p 162) (nonnegative2092 p) (nonnegative2117 p)
def d2119 (p : Pattern) : Int := if p 182 then d12 p else d121 p
theorem agree2119 (p q : Pattern) (h : Agree support p q) : d2119 p = d2119 q := by
  simp only [d2119, h 182 (by decide), agree12 p q h, agree121 p q h]
theorem nonnegative2119 (p : Pattern) : 0 ≤ d2119 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative121 p)
def d2120 (p : Pattern) : Int := if p 163 then d12 p else d2119 p
theorem agree2120 (p q : Pattern) (h : Agree support p q) : d2120 p = d2120 q := by
  simp only [d2120, h 163 (by decide), agree12 p q h, agree2119 p q h]
theorem nonnegative2120 (p : Pattern) : 0 ≤ d2120 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2119 p)
def d2121 (p : Pattern) : Int := if p 162 then d12 p else d2120 p
theorem agree2121 (p q : Pattern) (h : Agree support p q) : d2121 p = d2121 q := by
  simp only [d2121, h 162 (by decide), agree12 p q h, agree2120 p q h]
theorem nonnegative2121 (p : Pattern) : 0 ≤ d2121 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2120 p)
def d2122 (p : Pattern) : Int := if p 161 then d2121 p else d2118 p
theorem agree2122 (p q : Pattern) (h : Agree support p q) : d2122 p = d2122 q := by
  simp only [d2122, h 161 (by decide), agree2121 p q h, agree2118 p q h]
theorem nonnegative2122 (p : Pattern) : 0 ≤ d2122 p :=
  nonnegative_ite (p 161) (nonnegative2121 p) (nonnegative2118 p)
def d2123 (p : Pattern) : Int := if p 160 then d2122 p else d2115 p
theorem agree2123 (p q : Pattern) (h : Agree support p q) : d2123 p = d2123 q := by
  simp only [d2123, h 160 (by decide), agree2122 p q h, agree2115 p q h]
theorem nonnegative2123 (p : Pattern) : 0 ≤ d2123 p :=
  nonnegative_ite (p 160) (nonnegative2122 p) (nonnegative2115 p)
def d2124 (p : Pattern) : Int := if p 225 then d1895 p else d116 p
theorem agree2124 (p q : Pattern) (h : Agree support p q) : d2124 p = d2124 q := by
  simp only [d2124, h 225 (by decide), agree1895 p q h, agree116 p q h]
theorem nonnegative2124 (p : Pattern) : 0 ≤ d2124 p :=
  nonnegative_ite (p 225) (nonnegative1895 p) (nonnegative116 p)
def d2125 (p : Pattern) : Int := if p 224 then d1895 p else d2124 p
theorem agree2125 (p q : Pattern) (h : Agree support p q) : d2125 p = d2125 q := by
  simp only [d2125, h 224 (by decide), agree1895 p q h, agree2124 p q h]
theorem nonnegative2125 (p : Pattern) : 0 ≤ d2125 p :=
  nonnegative_ite (p 224) (nonnegative1895 p) (nonnegative2124 p)
def d2126 (p : Pattern) : Int := if p 204 then d12 p else d2125 p
theorem agree2126 (p q : Pattern) (h : Agree support p q) : d2126 p = d2126 q := by
  simp only [d2126, h 204 (by decide), agree12 p q h, agree2125 p q h]
theorem nonnegative2126 (p : Pattern) : 0 ≤ d2126 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2125 p)
def d2127 (p : Pattern) : Int := if p 182 then d2126 p else d117 p
theorem agree2127 (p q : Pattern) (h : Agree support p q) : d2127 p = d2127 q := by
  simp only [d2127, h 182 (by decide), agree2126 p q h, agree117 p q h]
theorem nonnegative2127 (p : Pattern) : 0 ≤ d2127 p :=
  nonnegative_ite (p 182) (nonnegative2126 p) (nonnegative117 p)
def d2128 (p : Pattern) : Int := if p 163 then d2127 p else d2110 p
theorem agree2128 (p q : Pattern) (h : Agree support p q) : d2128 p = d2128 q := by
  simp only [d2128, h 163 (by decide), agree2127 p q h, agree2110 p q h]
theorem nonnegative2128 (p : Pattern) : 0 ≤ d2128 p :=
  nonnegative_ite (p 163) (nonnegative2127 p) (nonnegative2110 p)
def d2129 (p : Pattern) : Int := if p 225 then d1964 p else d107 p
theorem agree2129 (p q : Pattern) (h : Agree support p q) : d2129 p = d2129 q := by
  simp only [d2129, h 225 (by decide), agree1964 p q h, agree107 p q h]
theorem nonnegative2129 (p : Pattern) : 0 ≤ d2129 p :=
  nonnegative_ite (p 225) (nonnegative1964 p) (nonnegative107 p)
def d2130 (p : Pattern) : Int := if p 224 then d1964 p else d2129 p
theorem agree2130 (p q : Pattern) (h : Agree support p q) : d2130 p = d2130 q := by
  simp only [d2130, h 224 (by decide), agree1964 p q h, agree2129 p q h]
theorem nonnegative2130 (p : Pattern) : 0 ≤ d2130 p :=
  nonnegative_ite (p 224) (nonnegative1964 p) (nonnegative2129 p)
def d2131 (p : Pattern) : Int := if p 204 then d12 p else d2130 p
theorem agree2131 (p q : Pattern) (h : Agree support p q) : d2131 p = d2131 q := by
  simp only [d2131, h 204 (by decide), agree12 p q h, agree2130 p q h]
theorem nonnegative2131 (p : Pattern) : 0 ≤ d2131 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2130 p)
def d2132 (p : Pattern) : Int := if p 182 then d2131 p else d108 p
theorem agree2132 (p q : Pattern) (h : Agree support p q) : d2132 p = d2132 q := by
  simp only [d2132, h 182 (by decide), agree2131 p q h, agree108 p q h]
theorem nonnegative2132 (p : Pattern) : 0 ≤ d2132 p :=
  nonnegative_ite (p 182) (nonnegative2131 p) (nonnegative108 p)
def d2133 (p : Pattern) : Int := if p 163 then d12 p else d2132 p
theorem agree2133 (p q : Pattern) (h : Agree support p q) : d2133 p = d2133 q := by
  simp only [d2133, h 163 (by decide), agree12 p q h, agree2132 p q h]
theorem nonnegative2133 (p : Pattern) : 0 ≤ d2133 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2132 p)
def d2134 (p : Pattern) : Int := if p 162 then d2133 p else d2128 p
theorem agree2134 (p q : Pattern) (h : Agree support p q) : d2134 p = d2134 q := by
  simp only [d2134, h 162 (by decide), agree2133 p q h, agree2128 p q h]
theorem nonnegative2134 (p : Pattern) : 0 ≤ d2134 p :=
  nonnegative_ite (p 162) (nonnegative2133 p) (nonnegative2128 p)
def d2135 (p : Pattern) : Int := if p 225 then d1961 p else d1964 p
theorem agree2135 (p q : Pattern) (h : Agree support p q) : d2135 p = d2135 q := by
  simp only [d2135, h 225 (by decide), agree1961 p q h, agree1964 p q h]
theorem nonnegative2135 (p : Pattern) : 0 ≤ d2135 p :=
  nonnegative_ite (p 225) (nonnegative1961 p) (nonnegative1964 p)
def d2136 (p : Pattern) : Int := if p 224 then d2135 p else d1962 p
theorem agree2136 (p q : Pattern) (h : Agree support p q) : d2136 p = d2136 q := by
  simp only [d2136, h 224 (by decide), agree2135 p q h, agree1962 p q h]
theorem nonnegative2136 (p : Pattern) : 0 ≤ d2136 p :=
  nonnegative_ite (p 224) (nonnegative2135 p) (nonnegative1962 p)
def d2137 (p : Pattern) : Int := if p 204 then d12 p else d2136 p
theorem agree2137 (p q : Pattern) (h : Agree support p q) : d2137 p = d2137 q := by
  simp only [d2137, h 204 (by decide), agree12 p q h, agree2136 p q h]
theorem nonnegative2137 (p : Pattern) : 0 ≤ d2137 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2136 p)
def d2138 (p : Pattern) : Int := if p 182 then d2137 p else d108 p
theorem agree2138 (p q : Pattern) (h : Agree support p q) : d2138 p = d2138 q := by
  simp only [d2138, h 182 (by decide), agree2137 p q h, agree108 p q h]
theorem nonnegative2138 (p : Pattern) : 0 ≤ d2138 p :=
  nonnegative_ite (p 182) (nonnegative2137 p) (nonnegative108 p)
def d2139 (p : Pattern) : Int := if p 163 then d12 p else d2138 p
theorem agree2139 (p q : Pattern) (h : Agree support p q) : d2139 p = d2139 q := by
  simp only [d2139, h 163 (by decide), agree12 p q h, agree2138 p q h]
theorem nonnegative2139 (p : Pattern) : 0 ≤ d2139 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2138 p)
def d2140 (p : Pattern) : Int := if p 162 then d12 p else d2139 p
theorem agree2140 (p q : Pattern) (h : Agree support p q) : d2140 p = d2140 q := by
  simp only [d2140, h 162 (by decide), agree12 p q h, agree2139 p q h]
theorem nonnegative2140 (p : Pattern) : 0 ≤ d2140 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2139 p)
def d2141 (p : Pattern) : Int := if p 161 then d2140 p else d2134 p
theorem agree2141 (p q : Pattern) (h : Agree support p q) : d2141 p = d2141 q := by
  simp only [d2141, h 161 (by decide), agree2140 p q h, agree2134 p q h]
theorem nonnegative2141 (p : Pattern) : 0 ≤ d2141 p :=
  nonnegative_ite (p 161) (nonnegative2140 p) (nonnegative2134 p)
def d2142 (p : Pattern) : Int := if p 182 then d1906 p else d108 p
theorem agree2142 (p q : Pattern) (h : Agree support p q) : d2142 p = d2142 q := by
  simp only [d2142, h 182 (by decide), agree1906 p q h, agree108 p q h]
theorem nonnegative2142 (p : Pattern) : 0 ≤ d2142 p :=
  nonnegative_ite (p 182) (nonnegative1906 p) (nonnegative108 p)
def d2143 (p : Pattern) : Int := if p 163 then d1910 p else d2142 p
theorem agree2143 (p q : Pattern) (h : Agree support p q) : d2143 p = d2143 q := by
  simp only [d2143, h 163 (by decide), agree1910 p q h, agree2142 p q h]
theorem nonnegative2143 (p : Pattern) : 0 ≤ d2143 p :=
  nonnegative_ite (p 163) (nonnegative1910 p) (nonnegative2142 p)
def d2144 (p : Pattern) : Int := if p 162 then d2120 p else d2143 p
theorem agree2144 (p q : Pattern) (h : Agree support p q) : d2144 p = d2144 q := by
  simp only [d2144, h 162 (by decide), agree2120 p q h, agree2143 p q h]
theorem nonnegative2144 (p : Pattern) : 0 ≤ d2144 p :=
  nonnegative_ite (p 162) (nonnegative2120 p) (nonnegative2143 p)
def d2145 (p : Pattern) : Int := if p 162 then d12 p else d528 p
theorem agree2145 (p q : Pattern) (h : Agree support p q) : d2145 p = d2145 q := by
  simp only [d2145, h 162 (by decide), agree12 p q h, agree528 p q h]
theorem nonnegative2145 (p : Pattern) : 0 ≤ d2145 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative528 p)
def d2146 (p : Pattern) : Int := if p 161 then d2145 p else d2144 p
theorem agree2146 (p q : Pattern) (h : Agree support p q) : d2146 p = d2146 q := by
  simp only [d2146, h 161 (by decide), agree2145 p q h, agree2144 p q h]
theorem nonnegative2146 (p : Pattern) : 0 ≤ d2146 p :=
  nonnegative_ite (p 161) (nonnegative2145 p) (nonnegative2144 p)
def d2147 (p : Pattern) : Int := if p 160 then d2146 p else d2141 p
theorem agree2147 (p q : Pattern) (h : Agree support p q) : d2147 p = d2147 q := by
  simp only [d2147, h 160 (by decide), agree2146 p q h, agree2141 p q h]
theorem nonnegative2147 (p : Pattern) : 0 ≤ d2147 p :=
  nonnegative_ite (p 160) (nonnegative2146 p) (nonnegative2141 p)
def d2148 (p : Pattern) : Int := if p 141 then d2147 p else d2123 p
theorem agree2148 (p q : Pattern) (h : Agree support p q) : d2148 p = d2148 q := by
  simp only [d2148, h 141 (by decide), agree2147 p q h, agree2123 p q h]
theorem nonnegative2148 (p : Pattern) : 0 ≤ d2148 p :=
  nonnegative_ite (p 141) (nonnegative2147 p) (nonnegative2123 p)
def d2149 (p : Pattern) : Int := if p 163 then d1959 p else d1953 p
theorem agree2149 (p q : Pattern) (h : Agree support p q) : d2149 p = d2149 q := by
  simp only [d2149, h 163 (by decide), agree1959 p q h, agree1953 p q h]
theorem nonnegative2149 (p : Pattern) : 0 ≤ d2149 p :=
  nonnegative_ite (p 163) (nonnegative1959 p) (nonnegative1953 p)
def d2150 (p : Pattern) : Int := if p 163 then d1756 p else d1973 p
theorem agree2150 (p q : Pattern) (h : Agree support p q) : d2150 p = d2150 q := by
  simp only [d2150, h 163 (by decide), agree1756 p q h, agree1973 p q h]
theorem nonnegative2150 (p : Pattern) : 0 ≤ d2150 p :=
  nonnegative_ite (p 163) (nonnegative1756 p) (nonnegative1973 p)
def d2151 (p : Pattern) : Int := if p 162 then d2150 p else d2149 p
theorem agree2151 (p q : Pattern) (h : Agree support p q) : d2151 p = d2151 q := by
  simp only [d2151, h 162 (by decide), agree2150 p q h, agree2149 p q h]
theorem nonnegative2151 (p : Pattern) : 0 ≤ d2151 p :=
  nonnegative_ite (p 162) (nonnegative2150 p) (nonnegative2149 p)
def d2152 (p : Pattern) : Int := if p 161 then d1983 p else d2151 p
theorem agree2152 (p q : Pattern) (h : Agree support p q) : d2152 p = d2152 q := by
  simp only [d2152, h 161 (by decide), agree1983 p q h, agree2151 p q h]
theorem nonnegative2152 (p : Pattern) : 0 ≤ d2152 p :=
  nonnegative_ite (p 161) (nonnegative1983 p) (nonnegative2151 p)
def d2153 (p : Pattern) : Int := if p 160 then d1987 p else d2152 p
theorem agree2153 (p q : Pattern) (h : Agree support p q) : d2153 p = d2153 q := by
  simp only [d2153, h 160 (by decide), agree1987 p q h, agree2152 p q h]
theorem nonnegative2153 (p : Pattern) : 0 ≤ d2153 p :=
  nonnegative_ite (p 160) (nonnegative1987 p) (nonnegative2152 p)
def d2154 (p : Pattern) : Int := if p 247 then d11 p else d3 p
theorem agree2154 (p q : Pattern) (h : Agree support p q) : d2154 p = d2154 q := by
  simp only [d2154, h 247 (by decide), agree11 p q h, agree3 p q h]
theorem nonnegative2154 (p : Pattern) : 0 ≤ d2154 p :=
  nonnegative_ite (p 247) (nonnegative11 p) (nonnegative3 p)
def d2155 (p : Pattern) : Int := if p 246 then d39 p else d2154 p
theorem agree2155 (p q : Pattern) (h : Agree support p q) : d2155 p = d2155 q := by
  simp only [d2155, h 246 (by decide), agree39 p q h, agree2154 p q h]
theorem nonnegative2155 (p : Pattern) : 0 ≤ d2155 p :=
  nonnegative_ite (p 246) (nonnegative39 p) (nonnegative2154 p)
def d2156 (p : Pattern) : Int := if p 225 then d2155 p else d1895 p
theorem agree2156 (p q : Pattern) (h : Agree support p q) : d2156 p = d2156 q := by
  simp only [d2156, h 225 (by decide), agree2155 p q h, agree1895 p q h]
theorem nonnegative2156 (p : Pattern) : 0 ≤ d2156 p :=
  nonnegative_ite (p 225) (nonnegative2155 p) (nonnegative1895 p)
def d2157 (p : Pattern) : Int := if p 224 then d2156 p else d1893 p
theorem agree2157 (p q : Pattern) (h : Agree support p q) : d2157 p = d2157 q := by
  simp only [d2157, h 224 (by decide), agree2156 p q h, agree1893 p q h]
theorem nonnegative2157 (p : Pattern) : 0 ≤ d2157 p :=
  nonnegative_ite (p 224) (nonnegative2156 p) (nonnegative1893 p)
def d2158 (p : Pattern) : Int := if p 204 then d12 p else d2157 p
theorem agree2158 (p q : Pattern) (h : Agree support p q) : d2158 p = d2158 q := by
  simp only [d2158, h 204 (by decide), agree12 p q h, agree2157 p q h]
theorem nonnegative2158 (p : Pattern) : 0 ≤ d2158 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2157 p)
def d2159 (p : Pattern) : Int := if p 182 then d2158 p else d117 p
theorem agree2159 (p q : Pattern) (h : Agree support p q) : d2159 p = d2159 q := by
  simp only [d2159, h 182 (by decide), agree2158 p q h, agree117 p q h]
theorem nonnegative2159 (p : Pattern) : 0 ≤ d2159 p :=
  nonnegative_ite (p 182) (nonnegative2158 p) (nonnegative117 p)
end NetHack.Sokoban22Refined85
