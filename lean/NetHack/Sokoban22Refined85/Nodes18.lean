/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2160 (p : Pattern) : Int := if p 163 then d1973 p else d2159 p
theorem agree2160 (p q : Pattern) (h : Agree support p q) : d2160 p = d2160 q := by
  simp only [d2160, h 163 (by decide), agree1973 p q h, agree2159 p q h]
theorem nonnegative2160 (p : Pattern) : 0 ≤ d2160 p :=
  nonnegative_ite (p 163) (nonnegative1973 p) (nonnegative2159 p)
def d2161 (p : Pattern) : Int := if p 162 then d2098 p else d2160 p
theorem agree2161 (p q : Pattern) (h : Agree support p q) : d2161 p = d2161 q := by
  simp only [d2161, h 162 (by decide), agree2098 p q h, agree2160 p q h]
theorem nonnegative2161 (p : Pattern) : 0 ≤ d2161 p :=
  nonnegative_ite (p 162) (nonnegative2098 p) (nonnegative2160 p)
def d2162 (p : Pattern) : Int := if p 161 then d1986 p else d2161 p
theorem agree2162 (p q : Pattern) (h : Agree support p q) : d2162 p = d2162 q := by
  simp only [d2162, h 161 (by decide), agree1986 p q h, agree2161 p q h]
theorem nonnegative2162 (p : Pattern) : 0 ≤ d2162 p :=
  nonnegative_ite (p 161) (nonnegative1986 p) (nonnegative2161 p)
def d2163 (p : Pattern) : Int := if p 162 then d12 p else d1806 p
theorem agree2163 (p q : Pattern) (h : Agree support p q) : d2163 p = d2163 q := by
  simp only [d2163, h 162 (by decide), agree12 p q h, agree1806 p q h]
theorem nonnegative2163 (p : Pattern) : 0 ≤ d2163 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1806 p)
def d2164 (p : Pattern) : Int := if p 161 then d12 p else d2163 p
theorem agree2164 (p q : Pattern) (h : Agree support p q) : d2164 p = d2164 q := by
  simp only [d2164, h 161 (by decide), agree12 p q h, agree2163 p q h]
theorem nonnegative2164 (p : Pattern) : 0 ≤ d2164 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2163 p)
def d2165 (p : Pattern) : Int := if p 160 then d2164 p else d2162 p
theorem agree2165 (p q : Pattern) (h : Agree support p q) : d2165 p = d2165 q := by
  simp only [d2165, h 160 (by decide), agree2164 p q h, agree2162 p q h]
theorem nonnegative2165 (p : Pattern) : 0 ≤ d2165 p :=
  nonnegative_ite (p 160) (nonnegative2164 p) (nonnegative2162 p)
def d2166 (p : Pattern) : Int := if p 141 then d2165 p else d2153 p
theorem agree2166 (p q : Pattern) (h : Agree support p q) : d2166 p = d2166 q := by
  simp only [d2166, h 141 (by decide), agree2165 p q h, agree2153 p q h]
theorem nonnegative2166 (p : Pattern) : 0 ≤ d2166 p :=
  nonnegative_ite (p 141) (nonnegative2165 p) (nonnegative2153 p)
def d2167 (p : Pattern) : Int := if p 138 then d2166 p else d2148 p
theorem agree2167 (p q : Pattern) (h : Agree support p q) : d2167 p = d2167 q := by
  simp only [d2167, h 138 (by decide), agree2166 p q h, agree2148 p q h]
theorem nonnegative2167 (p : Pattern) : 0 ≤ d2167 p :=
  nonnegative_ite (p 138) (nonnegative2166 p) (nonnegative2148 p)
def d2168 (p : Pattern) : Int := if p 163 then d1805 p else d1973 p
theorem agree2168 (p q : Pattern) (h : Agree support p q) : d2168 p = d2168 q := by
  simp only [d2168, h 163 (by decide), agree1805 p q h, agree1973 p q h]
theorem nonnegative2168 (p : Pattern) : 0 ≤ d2168 p :=
  nonnegative_ite (p 163) (nonnegative1805 p) (nonnegative1973 p)
def d2169 (p : Pattern) : Int := if p 162 then d2168 p else d2149 p
theorem agree2169 (p q : Pattern) (h : Agree support p q) : d2169 p = d2169 q := by
  simp only [d2169, h 162 (by decide), agree2168 p q h, agree2149 p q h]
theorem nonnegative2169 (p : Pattern) : 0 ≤ d2169 p :=
  nonnegative_ite (p 162) (nonnegative2168 p) (nonnegative2149 p)
def d2170 (p : Pattern) : Int := if p 163 then d1805 p else d1968 p
theorem agree2170 (p q : Pattern) (h : Agree support p q) : d2170 p = d2170 q := by
  simp only [d2170, h 163 (by decide), agree1805 p q h, agree1968 p q h]
theorem nonnegative2170 (p : Pattern) : 0 ≤ d2170 p :=
  nonnegative_ite (p 163) (nonnegative1805 p) (nonnegative1968 p)
def d2171 (p : Pattern) : Int := if p 162 then d12 p else d2170 p
theorem agree2171 (p q : Pattern) (h : Agree support p q) : d2171 p = d2171 q := by
  simp only [d2171, h 162 (by decide), agree12 p q h, agree2170 p q h]
theorem nonnegative2171 (p : Pattern) : 0 ≤ d2171 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2170 p)
def d2172 (p : Pattern) : Int := if p 161 then d2171 p else d2169 p
theorem agree2172 (p q : Pattern) (h : Agree support p q) : d2172 p = d2172 q := by
  simp only [d2172, h 161 (by decide), agree2171 p q h, agree2169 p q h]
theorem nonnegative2172 (p : Pattern) : 0 ≤ d2172 p :=
  nonnegative_ite (p 161) (nonnegative2171 p) (nonnegative2169 p)
def d2173 (p : Pattern) : Int := if p 163 then d1756 p else d1974 p
theorem agree2173 (p q : Pattern) (h : Agree support p q) : d2173 p = d2173 q := by
  simp only [d2173, h 163 (by decide), agree1756 p q h, agree1974 p q h]
theorem nonnegative2173 (p : Pattern) : 0 ≤ d2173 p :=
  nonnegative_ite (p 163) (nonnegative1756 p) (nonnegative1974 p)
def d2174 (p : Pattern) : Int := if p 162 then d12 p else d2173 p
theorem agree2174 (p q : Pattern) (h : Agree support p q) : d2174 p = d2174 q := by
  simp only [d2174, h 162 (by decide), agree12 p q h, agree2173 p q h]
theorem nonnegative2174 (p : Pattern) : 0 ≤ d2174 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2173 p)
def d2175 (p : Pattern) : Int := if p 161 then d12 p else d2174 p
theorem agree2175 (p q : Pattern) (h : Agree support p q) : d2175 p = d2175 q := by
  simp only [d2175, h 161 (by decide), agree12 p q h, agree2174 p q h]
theorem nonnegative2175 (p : Pattern) : 0 ≤ d2175 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2174 p)
def d2176 (p : Pattern) : Int := if p 160 then d2175 p else d2172 p
theorem agree2176 (p q : Pattern) (h : Agree support p q) : d2176 p = d2176 q := by
  simp only [d2176, h 160 (by decide), agree2175 p q h, agree2172 p q h]
theorem nonnegative2176 (p : Pattern) : 0 ≤ d2176 p :=
  nonnegative_ite (p 160) (nonnegative2175 p) (nonnegative2172 p)
def d2177 (p : Pattern) : Int := if p 141 then d2165 p else d2176 p
theorem agree2177 (p q : Pattern) (h : Agree support p q) : d2177 p = d2177 q := by
  simp only [d2177, h 141 (by decide), agree2165 p q h, agree2176 p q h]
theorem nonnegative2177 (p : Pattern) : 0 ≤ d2177 p :=
  nonnegative_ite (p 141) (nonnegative2165 p) (nonnegative2176 p)
def d2178 (p : Pattern) : Int := if p 138 then d12 p else d2177 p
theorem agree2178 (p q : Pattern) (h : Agree support p q) : d2178 p = d2178 q := by
  simp only [d2178, h 138 (by decide), agree12 p q h, agree2177 p q h]
theorem nonnegative2178 (p : Pattern) : 0 ≤ d2178 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2177 p)
def d2179 (p : Pattern) : Int := if p 116 then d2178 p else d2167 p
theorem agree2179 (p q : Pattern) (h : Agree support p q) : d2179 p = d2179 q := by
  simp only [d2179, h 116 (by decide), agree2178 p q h, agree2167 p q h]
theorem nonnegative2179 (p : Pattern) : 0 ≤ d2179 p :=
  nonnegative_ite (p 116) (nonnegative2178 p) (nonnegative2167 p)
def d2180 (p : Pattern) : Int := if p 115 then d2179 p else d2106 p
theorem agree2180 (p q : Pattern) (h : Agree support p q) : d2180 p = d2180 q := by
  simp only [d2180, h 115 (by decide), agree2179 p q h, agree2106 p q h]
theorem nonnegative2180 (p : Pattern) : 0 ≤ d2180 p :=
  nonnegative_ite (p 115) (nonnegative2179 p) (nonnegative2106 p)
def d2181 (p : Pattern) : Int := if p 71 then d2180 p else d1849 p
theorem agree2181 (p q : Pattern) (h : Agree support p q) : d2181 p = d2181 q := by
  simp only [d2181, h 71 (by decide), agree2180 p q h, agree1849 p q h]
theorem nonnegative2181 (p : Pattern) : 0 ≤ d2181 p :=
  nonnegative_ite (p 71) (nonnegative2180 p) (nonnegative1849 p)
def d2182 (p : Pattern) : Int := if p 49 then d2181 p else d2087 p
theorem agree2182 (p q : Pattern) (h : Agree support p q) : d2182 p = d2182 q := by
  simp only [d2182, h 49 (by decide), agree2181 p q h, agree2087 p q h]
theorem nonnegative2182 (p : Pattern) : 0 ≤ d2182 p :=
  nonnegative_ite (p 49) (nonnegative2181 p) (nonnegative2087 p)
def d2183 (p : Pattern) : Int := if p 48 then d2182 p else d2010 p
theorem agree2183 (p q : Pattern) (h : Agree support p q) : d2183 p = d2183 q := by
  simp only [d2183, h 48 (by decide), agree2182 p q h, agree2010 p q h]
theorem nonnegative2183 (p : Pattern) : 0 ≤ d2183 p :=
  nonnegative_ite (p 48) (nonnegative2182 p) (nonnegative2010 p)
def d2184 (p : Pattern) : Int := if p 224 then d318 p else d14 p
theorem agree2184 (p q : Pattern) (h : Agree support p q) : d2184 p = d2184 q := by
  simp only [d2184, h 224 (by decide), agree318 p q h, agree14 p q h]
theorem nonnegative2184 (p : Pattern) : 0 ≤ d2184 p :=
  nonnegative_ite (p 224) (nonnegative318 p) (nonnegative14 p)
def d2185 (p : Pattern) : Int := if p 224 then d12 p else d14 p
theorem agree2185 (p q : Pattern) (h : Agree support p q) : d2185 p = d2185 q := by
  simp only [d2185, h 224 (by decide), agree12 p q h, agree14 p q h]
theorem nonnegative2185 (p : Pattern) : 0 ≤ d2185 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative14 p)
def d2186 (p : Pattern) : Int := if p 204 then d2185 p else d2184 p
theorem agree2186 (p q : Pattern) (h : Agree support p q) : d2186 p = d2186 q := by
  simp only [d2186, h 204 (by decide), agree2185 p q h, agree2184 p q h]
theorem nonnegative2186 (p : Pattern) : 0 ≤ d2186 p :=
  nonnegative_ite (p 204) (nonnegative2185 p) (nonnegative2184 p)
def d2187 (p : Pattern) : Int := if p 204 then d12 p else d2185 p
theorem agree2187 (p q : Pattern) (h : Agree support p q) : d2187 p = d2187 q := by
  simp only [d2187, h 204 (by decide), agree12 p q h, agree2185 p q h]
theorem nonnegative2187 (p : Pattern) : 0 ≤ d2187 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2185 p)
def d2188 (p : Pattern) : Int := if p 182 then d2187 p else d2186 p
theorem agree2188 (p q : Pattern) (h : Agree support p q) : d2188 p = d2188 q := by
  simp only [d2188, h 182 (by decide), agree2187 p q h, agree2186 p q h]
theorem nonnegative2188 (p : Pattern) : 0 ≤ d2188 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2186 p)
def d2189 (p : Pattern) : Int := if p 224 then d330 p else d14 p
theorem agree2189 (p q : Pattern) (h : Agree support p q) : d2189 p = d2189 q := by
  simp only [d2189, h 224 (by decide), agree330 p q h, agree14 p q h]
theorem nonnegative2189 (p : Pattern) : 0 ≤ d2189 p :=
  nonnegative_ite (p 224) (nonnegative330 p) (nonnegative14 p)
def d2190 (p : Pattern) : Int := if p 204 then d2185 p else d2189 p
theorem agree2190 (p q : Pattern) (h : Agree support p q) : d2190 p = d2190 q := by
  simp only [d2190, h 204 (by decide), agree2185 p q h, agree2189 p q h]
theorem nonnegative2190 (p : Pattern) : 0 ≤ d2190 p :=
  nonnegative_ite (p 204) (nonnegative2185 p) (nonnegative2189 p)
def d2191 (p : Pattern) : Int := if p 182 then d2187 p else d2190 p
theorem agree2191 (p q : Pattern) (h : Agree support p q) : d2191 p = d2191 q := by
  simp only [d2191, h 182 (by decide), agree2187 p q h, agree2190 p q h]
theorem nonnegative2191 (p : Pattern) : 0 ≤ d2191 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2190 p)
def d2192 (p : Pattern) : Int := if p 163 then d2191 p else d2188 p
theorem agree2192 (p q : Pattern) (h : Agree support p q) : d2192 p = d2192 q := by
  simp only [d2192, h 163 (by decide), agree2191 p q h, agree2188 p q h]
theorem nonnegative2192 (p : Pattern) : 0 ≤ d2192 p :=
  nonnegative_ite (p 163) (nonnegative2191 p) (nonnegative2188 p)
def d2193 (p : Pattern) : Int := if p 224 then d332 p else d14 p
theorem agree2193 (p q : Pattern) (h : Agree support p q) : d2193 p = d2193 q := by
  simp only [d2193, h 224 (by decide), agree332 p q h, agree14 p q h]
theorem nonnegative2193 (p : Pattern) : 0 ≤ d2193 p :=
  nonnegative_ite (p 224) (nonnegative332 p) (nonnegative14 p)
def d2194 (p : Pattern) : Int := if p 204 then d2185 p else d2193 p
theorem agree2194 (p q : Pattern) (h : Agree support p q) : d2194 p = d2194 q := by
  simp only [d2194, h 204 (by decide), agree2185 p q h, agree2193 p q h]
theorem nonnegative2194 (p : Pattern) : 0 ≤ d2194 p :=
  nonnegative_ite (p 204) (nonnegative2185 p) (nonnegative2193 p)
def d2195 (p : Pattern) : Int := if p 182 then d2187 p else d2194 p
theorem agree2195 (p q : Pattern) (h : Agree support p q) : d2195 p = d2195 q := by
  simp only [d2195, h 182 (by decide), agree2187 p q h, agree2194 p q h]
theorem nonnegative2195 (p : Pattern) : 0 ≤ d2195 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2194 p)
def d2196 (p : Pattern) : Int := if p 224 then d12 p else d18 p
theorem agree2196 (p q : Pattern) (h : Agree support p q) : d2196 p = d2196 q := by
  simp only [d2196, h 224 (by decide), agree12 p q h, agree18 p q h]
theorem nonnegative2196 (p : Pattern) : 0 ≤ d2196 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative18 p)
def d2197 (p : Pattern) : Int := if p 204 then d12 p else d2196 p
theorem agree2197 (p q : Pattern) (h : Agree support p q) : d2197 p = d2197 q := by
  simp only [d2197, h 204 (by decide), agree12 p q h, agree2196 p q h]
theorem nonnegative2197 (p : Pattern) : 0 ≤ d2197 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2196 p)
def d2198 (p : Pattern) : Int := if p 182 then d2197 p else d2196 p
theorem agree2198 (p q : Pattern) (h : Agree support p q) : d2198 p = d2198 q := by
  simp only [d2198, h 182 (by decide), agree2197 p q h, agree2196 p q h]
theorem nonnegative2198 (p : Pattern) : 0 ≤ d2198 p :=
  nonnegative_ite (p 182) (nonnegative2197 p) (nonnegative2196 p)
def d2199 (p : Pattern) : Int := if p 163 then d2198 p else d2195 p
theorem agree2199 (p q : Pattern) (h : Agree support p q) : d2199 p = d2199 q := by
  simp only [d2199, h 163 (by decide), agree2198 p q h, agree2195 p q h]
theorem nonnegative2199 (p : Pattern) : 0 ≤ d2199 p :=
  nonnegative_ite (p 163) (nonnegative2198 p) (nonnegative2195 p)
def d2200 (p : Pattern) : Int := if p 162 then d2199 p else d2192 p
theorem agree2200 (p q : Pattern) (h : Agree support p q) : d2200 p = d2200 q := by
  simp only [d2200, h 162 (by decide), agree2199 p q h, agree2192 p q h]
theorem nonnegative2200 (p : Pattern) : 0 ≤ d2200 p :=
  nonnegative_ite (p 162) (nonnegative2199 p) (nonnegative2192 p)
def d2201 (p : Pattern) : Int := if p 182 then d2187 p else d2185 p
theorem agree2201 (p q : Pattern) (h : Agree support p q) : d2201 p = d2201 q := by
  simp only [d2201, h 182 (by decide), agree2187 p q h, agree2185 p q h]
theorem nonnegative2201 (p : Pattern) : 0 ≤ d2201 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2185 p)
def d2202 (p : Pattern) : Int := if p 163 then d2198 p else d2201 p
theorem agree2202 (p q : Pattern) (h : Agree support p q) : d2202 p = d2202 q := by
  simp only [d2202, h 163 (by decide), agree2198 p q h, agree2201 p q h]
theorem nonnegative2202 (p : Pattern) : 0 ≤ d2202 p :=
  nonnegative_ite (p 163) (nonnegative2198 p) (nonnegative2201 p)
def d2203 (p : Pattern) : Int := if p 224 then d12 p else d24 p
theorem agree2203 (p q : Pattern) (h : Agree support p q) : d2203 p = d2203 q := by
  simp only [d2203, h 224 (by decide), agree12 p q h, agree24 p q h]
theorem nonnegative2203 (p : Pattern) : 0 ≤ d2203 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative24 p)
def d2204 (p : Pattern) : Int := if p 204 then d12 p else d2203 p
theorem agree2204 (p q : Pattern) (h : Agree support p q) : d2204 p = d2204 q := by
  simp only [d2204, h 204 (by decide), agree12 p q h, agree2203 p q h]
theorem nonnegative2204 (p : Pattern) : 0 ≤ d2204 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2203 p)
def d2205 (p : Pattern) : Int := if p 182 then d2204 p else d2203 p
theorem agree2205 (p q : Pattern) (h : Agree support p q) : d2205 p = d2205 q := by
  simp only [d2205, h 182 (by decide), agree2204 p q h, agree2203 p q h]
theorem nonnegative2205 (p : Pattern) : 0 ≤ d2205 p :=
  nonnegative_ite (p 182) (nonnegative2204 p) (nonnegative2203 p)
def d2206 (p : Pattern) : Int := if p 163 then d12 p else d2205 p
theorem agree2206 (p q : Pattern) (h : Agree support p q) : d2206 p = d2206 q := by
  simp only [d2206, h 163 (by decide), agree12 p q h, agree2205 p q h]
theorem nonnegative2206 (p : Pattern) : 0 ≤ d2206 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2205 p)
def d2207 (p : Pattern) : Int := if p 162 then d2206 p else d2202 p
theorem agree2207 (p q : Pattern) (h : Agree support p q) : d2207 p = d2207 q := by
  simp only [d2207, h 162 (by decide), agree2206 p q h, agree2202 p q h]
theorem nonnegative2207 (p : Pattern) : 0 ≤ d2207 p :=
  nonnegative_ite (p 162) (nonnegative2206 p) (nonnegative2202 p)
def d2208 (p : Pattern) : Int := if p 161 then d2207 p else d2200 p
theorem agree2208 (p q : Pattern) (h : Agree support p q) : d2208 p = d2208 q := by
  simp only [d2208, h 161 (by decide), agree2207 p q h, agree2200 p q h]
theorem nonnegative2208 (p : Pattern) : 0 ≤ d2208 p :=
  nonnegative_ite (p 161) (nonnegative2207 p) (nonnegative2200 p)
def d2209 (p : Pattern) : Int := if p 224 then d12 p else d31 p
theorem agree2209 (p q : Pattern) (h : Agree support p q) : d2209 p = d2209 q := by
  simp only [d2209, h 224 (by decide), agree12 p q h, agree31 p q h]
theorem nonnegative2209 (p : Pattern) : 0 ≤ d2209 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative31 p)
def d2210 (p : Pattern) : Int := if p 204 then d12 p else d2209 p
theorem agree2210 (p q : Pattern) (h : Agree support p q) : d2210 p = d2210 q := by
  simp only [d2210, h 204 (by decide), agree12 p q h, agree2209 p q h]
theorem nonnegative2210 (p : Pattern) : 0 ≤ d2210 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2209 p)
def d2211 (p : Pattern) : Int := if p 182 then d2210 p else d2185 p
theorem agree2211 (p q : Pattern) (h : Agree support p q) : d2211 p = d2211 q := by
  simp only [d2211, h 182 (by decide), agree2210 p q h, agree2185 p q h]
theorem nonnegative2211 (p : Pattern) : 0 ≤ d2211 p :=
  nonnegative_ite (p 182) (nonnegative2210 p) (nonnegative2185 p)
def d2212 (p : Pattern) : Int := if p 224 then d12 p else d35 p
theorem agree2212 (p q : Pattern) (h : Agree support p q) : d2212 p = d2212 q := by
  simp only [d2212, h 224 (by decide), agree12 p q h, agree35 p q h]
theorem nonnegative2212 (p : Pattern) : 0 ≤ d2212 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative35 p)
def d2213 (p : Pattern) : Int := if p 204 then d12 p else d2212 p
theorem agree2213 (p q : Pattern) (h : Agree support p q) : d2213 p = d2213 q := by
  simp only [d2213, h 204 (by decide), agree12 p q h, agree2212 p q h]
theorem nonnegative2213 (p : Pattern) : 0 ≤ d2213 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2212 p)
def d2214 (p : Pattern) : Int := if p 182 then d2213 p else d2185 p
theorem agree2214 (p q : Pattern) (h : Agree support p q) : d2214 p = d2214 q := by
  simp only [d2214, h 182 (by decide), agree2213 p q h, agree2185 p q h]
theorem nonnegative2214 (p : Pattern) : 0 ≤ d2214 p :=
  nonnegative_ite (p 182) (nonnegative2213 p) (nonnegative2185 p)
def d2215 (p : Pattern) : Int := if p 163 then d2214 p else d2211 p
theorem agree2215 (p q : Pattern) (h : Agree support p q) : d2215 p = d2215 q := by
  simp only [d2215, h 163 (by decide), agree2214 p q h, agree2211 p q h]
theorem nonnegative2215 (p : Pattern) : 0 ≤ d2215 p :=
  nonnegative_ite (p 163) (nonnegative2214 p) (nonnegative2211 p)
def d2216 (p : Pattern) : Int := if p 224 then d12 p else d40 p
theorem agree2216 (p q : Pattern) (h : Agree support p q) : d2216 p = d2216 q := by
  simp only [d2216, h 224 (by decide), agree12 p q h, agree40 p q h]
theorem nonnegative2216 (p : Pattern) : 0 ≤ d2216 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative40 p)
def d2217 (p : Pattern) : Int := if p 204 then d12 p else d2216 p
theorem agree2217 (p q : Pattern) (h : Agree support p q) : d2217 p = d2217 q := by
  simp only [d2217, h 204 (by decide), agree12 p q h, agree2216 p q h]
theorem nonnegative2217 (p : Pattern) : 0 ≤ d2217 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2216 p)
def d2218 (p : Pattern) : Int := if p 182 then d2217 p else d2185 p
theorem agree2218 (p q : Pattern) (h : Agree support p q) : d2218 p = d2218 q := by
  simp only [d2218, h 182 (by decide), agree2217 p q h, agree2185 p q h]
theorem nonnegative2218 (p : Pattern) : 0 ≤ d2218 p :=
  nonnegative_ite (p 182) (nonnegative2217 p) (nonnegative2185 p)
def d2219 (p : Pattern) : Int := if p 182 then d12 p else d2196 p
theorem agree2219 (p q : Pattern) (h : Agree support p q) : d2219 p = d2219 q := by
  simp only [d2219, h 182 (by decide), agree12 p q h, agree2196 p q h]
theorem nonnegative2219 (p : Pattern) : 0 ≤ d2219 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2196 p)
def d2220 (p : Pattern) : Int := if p 163 then d2219 p else d2218 p
theorem agree2220 (p q : Pattern) (h : Agree support p q) : d2220 p = d2220 q := by
  simp only [d2220, h 163 (by decide), agree2219 p q h, agree2218 p q h]
theorem nonnegative2220 (p : Pattern) : 0 ≤ d2220 p :=
  nonnegative_ite (p 163) (nonnegative2219 p) (nonnegative2218 p)
def d2221 (p : Pattern) : Int := if p 162 then d2220 p else d2215 p
theorem agree2221 (p q : Pattern) (h : Agree support p q) : d2221 p = d2221 q := by
  simp only [d2221, h 162 (by decide), agree2220 p q h, agree2215 p q h]
theorem nonnegative2221 (p : Pattern) : 0 ≤ d2221 p :=
  nonnegative_ite (p 162) (nonnegative2220 p) (nonnegative2215 p)
def d2222 (p : Pattern) : Int := if p 182 then d12 p else d2185 p
theorem agree2222 (p q : Pattern) (h : Agree support p q) : d2222 p = d2222 q := by
  simp only [d2222, h 182 (by decide), agree12 p q h, agree2185 p q h]
theorem nonnegative2222 (p : Pattern) : 0 ≤ d2222 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2185 p)
def d2223 (p : Pattern) : Int := if p 163 then d2219 p else d2222 p
theorem agree2223 (p q : Pattern) (h : Agree support p q) : d2223 p = d2223 q := by
  simp only [d2223, h 163 (by decide), agree2219 p q h, agree2222 p q h]
theorem nonnegative2223 (p : Pattern) : 0 ≤ d2223 p :=
  nonnegative_ite (p 163) (nonnegative2219 p) (nonnegative2222 p)
def d2224 (p : Pattern) : Int := if p 182 then d12 p else d2203 p
theorem agree2224 (p q : Pattern) (h : Agree support p q) : d2224 p = d2224 q := by
  simp only [d2224, h 182 (by decide), agree12 p q h, agree2203 p q h]
theorem nonnegative2224 (p : Pattern) : 0 ≤ d2224 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2203 p)
def d2225 (p : Pattern) : Int := if p 163 then d12 p else d2224 p
theorem agree2225 (p q : Pattern) (h : Agree support p q) : d2225 p = d2225 q := by
  simp only [d2225, h 163 (by decide), agree12 p q h, agree2224 p q h]
theorem nonnegative2225 (p : Pattern) : 0 ≤ d2225 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2224 p)
def d2226 (p : Pattern) : Int := if p 162 then d2225 p else d2223 p
theorem agree2226 (p q : Pattern) (h : Agree support p q) : d2226 p = d2226 q := by
  simp only [d2226, h 162 (by decide), agree2225 p q h, agree2223 p q h]
theorem nonnegative2226 (p : Pattern) : 0 ≤ d2226 p :=
  nonnegative_ite (p 162) (nonnegative2225 p) (nonnegative2223 p)
def d2227 (p : Pattern) : Int := if p 161 then d2226 p else d2221 p
theorem agree2227 (p q : Pattern) (h : Agree support p q) : d2227 p = d2227 q := by
  simp only [d2227, h 161 (by decide), agree2226 p q h, agree2221 p q h]
theorem nonnegative2227 (p : Pattern) : 0 ≤ d2227 p :=
  nonnegative_ite (p 161) (nonnegative2226 p) (nonnegative2221 p)
def d2228 (p : Pattern) : Int := if p 160 then d2227 p else d2208 p
theorem agree2228 (p q : Pattern) (h : Agree support p q) : d2228 p = d2228 q := by
  simp only [d2228, h 160 (by decide), agree2227 p q h, agree2208 p q h]
theorem nonnegative2228 (p : Pattern) : 0 ≤ d2228 p :=
  nonnegative_ite (p 160) (nonnegative2227 p) (nonnegative2208 p)
def d2229 (p : Pattern) : Int := if p 224 then d357 p else d14 p
theorem agree2229 (p q : Pattern) (h : Agree support p q) : d2229 p = d2229 q := by
  simp only [d2229, h 224 (by decide), agree357 p q h, agree14 p q h]
theorem nonnegative2229 (p : Pattern) : 0 ≤ d2229 p :=
  nonnegative_ite (p 224) (nonnegative357 p) (nonnegative14 p)
def d2230 (p : Pattern) : Int := if p 204 then d2185 p else d2229 p
theorem agree2230 (p q : Pattern) (h : Agree support p q) : d2230 p = d2230 q := by
  simp only [d2230, h 204 (by decide), agree2185 p q h, agree2229 p q h]
theorem nonnegative2230 (p : Pattern) : 0 ≤ d2230 p :=
  nonnegative_ite (p 204) (nonnegative2185 p) (nonnegative2229 p)
def d2231 (p : Pattern) : Int := if p 182 then d2187 p else d2230 p
theorem agree2231 (p q : Pattern) (h : Agree support p q) : d2231 p = d2231 q := by
  simp only [d2231, h 182 (by decide), agree2187 p q h, agree2230 p q h]
theorem nonnegative2231 (p : Pattern) : 0 ≤ d2231 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2230 p)
def d2232 (p : Pattern) : Int := if p 182 then d2210 p else d2209 p
theorem agree2232 (p q : Pattern) (h : Agree support p q) : d2232 p = d2232 q := by
  simp only [d2232, h 182 (by decide), agree2210 p q h, agree2209 p q h]
theorem nonnegative2232 (p : Pattern) : 0 ≤ d2232 p :=
  nonnegative_ite (p 182) (nonnegative2210 p) (nonnegative2209 p)
def d2233 (p : Pattern) : Int := if p 163 then d2232 p else d2231 p
theorem agree2233 (p q : Pattern) (h : Agree support p q) : d2233 p = d2233 q := by
  simp only [d2233, h 163 (by decide), agree2232 p q h, agree2231 p q h]
theorem nonnegative2233 (p : Pattern) : 0 ≤ d2233 p :=
  nonnegative_ite (p 163) (nonnegative2232 p) (nonnegative2231 p)
def d2234 (p : Pattern) : Int := if p 163 then d2205 p else d2198 p
theorem agree2234 (p q : Pattern) (h : Agree support p q) : d2234 p = d2234 q := by
  simp only [d2234, h 163 (by decide), agree2205 p q h, agree2198 p q h]
theorem nonnegative2234 (p : Pattern) : 0 ≤ d2234 p :=
  nonnegative_ite (p 163) (nonnegative2205 p) (nonnegative2198 p)
def d2235 (p : Pattern) : Int := if p 162 then d2234 p else d2233 p
theorem agree2235 (p q : Pattern) (h : Agree support p q) : d2235 p = d2235 q := by
  simp only [d2235, h 162 (by decide), agree2234 p q h, agree2233 p q h]
theorem nonnegative2235 (p : Pattern) : 0 ≤ d2235 p :=
  nonnegative_ite (p 162) (nonnegative2234 p) (nonnegative2233 p)
def d2236 (p : Pattern) : Int := if p 224 then d12 p else d58 p
theorem agree2236 (p q : Pattern) (h : Agree support p q) : d2236 p = d2236 q := by
  simp only [d2236, h 224 (by decide), agree12 p q h, agree58 p q h]
theorem nonnegative2236 (p : Pattern) : 0 ≤ d2236 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative58 p)
def d2237 (p : Pattern) : Int := if p 204 then d12 p else d2236 p
theorem agree2237 (p q : Pattern) (h : Agree support p q) : d2237 p = d2237 q := by
  simp only [d2237, h 204 (by decide), agree12 p q h, agree2236 p q h]
theorem nonnegative2237 (p : Pattern) : 0 ≤ d2237 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2236 p)
def d2238 (p : Pattern) : Int := if p 182 then d2237 p else d2236 p
theorem agree2238 (p q : Pattern) (h : Agree support p q) : d2238 p = d2238 q := by
  simp only [d2238, h 182 (by decide), agree2237 p q h, agree2236 p q h]
theorem nonnegative2238 (p : Pattern) : 0 ≤ d2238 p :=
  nonnegative_ite (p 182) (nonnegative2237 p) (nonnegative2236 p)
def d2239 (p : Pattern) : Int := if p 163 then d2238 p else d2198 p
theorem agree2239 (p q : Pattern) (h : Agree support p q) : d2239 p = d2239 q := by
  simp only [d2239, h 163 (by decide), agree2238 p q h, agree2198 p q h]
theorem nonnegative2239 (p : Pattern) : 0 ≤ d2239 p :=
  nonnegative_ite (p 163) (nonnegative2238 p) (nonnegative2198 p)
def d2240 (p : Pattern) : Int := if p 182 then d2217 p else d2216 p
theorem agree2240 (p q : Pattern) (h : Agree support p q) : d2240 p = d2240 q := by
  simp only [d2240, h 182 (by decide), agree2217 p q h, agree2216 p q h]
theorem nonnegative2240 (p : Pattern) : 0 ≤ d2240 p :=
  nonnegative_ite (p 182) (nonnegative2217 p) (nonnegative2216 p)
def d2241 (p : Pattern) : Int := if p 163 then d12 p else d2240 p
theorem agree2241 (p q : Pattern) (h : Agree support p q) : d2241 p = d2241 q := by
  simp only [d2241, h 163 (by decide), agree12 p q h, agree2240 p q h]
theorem nonnegative2241 (p : Pattern) : 0 ≤ d2241 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2240 p)
def d2242 (p : Pattern) : Int := if p 162 then d2241 p else d2239 p
theorem agree2242 (p q : Pattern) (h : Agree support p q) : d2242 p = d2242 q := by
  simp only [d2242, h 162 (by decide), agree2241 p q h, agree2239 p q h]
theorem nonnegative2242 (p : Pattern) : 0 ≤ d2242 p :=
  nonnegative_ite (p 162) (nonnegative2241 p) (nonnegative2239 p)
def d2243 (p : Pattern) : Int := if p 161 then d2242 p else d2235 p
theorem agree2243 (p q : Pattern) (h : Agree support p q) : d2243 p = d2243 q := by
  simp only [d2243, h 161 (by decide), agree2242 p q h, agree2235 p q h]
theorem nonnegative2243 (p : Pattern) : 0 ≤ d2243 p :=
  nonnegative_ite (p 161) (nonnegative2242 p) (nonnegative2235 p)
def d2244 (p : Pattern) : Int := if p 182 then d12 p else d2209 p
theorem agree2244 (p q : Pattern) (h : Agree support p q) : d2244 p = d2244 q := by
  simp only [d2244, h 182 (by decide), agree12 p q h, agree2209 p q h]
theorem nonnegative2244 (p : Pattern) : 0 ≤ d2244 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2209 p)
def d2245 (p : Pattern) : Int := if p 163 then d2244 p else d2214 p
theorem agree2245 (p q : Pattern) (h : Agree support p q) : d2245 p = d2245 q := by
  simp only [d2245, h 163 (by decide), agree2244 p q h, agree2214 p q h]
theorem nonnegative2245 (p : Pattern) : 0 ≤ d2245 p :=
  nonnegative_ite (p 163) (nonnegative2244 p) (nonnegative2214 p)
def d2246 (p : Pattern) : Int := if p 163 then d2224 p else d2219 p
theorem agree2246 (p q : Pattern) (h : Agree support p q) : d2246 p = d2246 q := by
  simp only [d2246, h 163 (by decide), agree2224 p q h, agree2219 p q h]
theorem nonnegative2246 (p : Pattern) : 0 ≤ d2246 p :=
  nonnegative_ite (p 163) (nonnegative2224 p) (nonnegative2219 p)
def d2247 (p : Pattern) : Int := if p 162 then d2246 p else d2245 p
theorem agree2247 (p q : Pattern) (h : Agree support p q) : d2247 p = d2247 q := by
  simp only [d2247, h 162 (by decide), agree2246 p q h, agree2245 p q h]
theorem nonnegative2247 (p : Pattern) : 0 ≤ d2247 p :=
  nonnegative_ite (p 162) (nonnegative2246 p) (nonnegative2245 p)
def d2248 (p : Pattern) : Int := if p 182 then d12 p else d2236 p
theorem agree2248 (p q : Pattern) (h : Agree support p q) : d2248 p = d2248 q := by
  simp only [d2248, h 182 (by decide), agree12 p q h, agree2236 p q h]
theorem nonnegative2248 (p : Pattern) : 0 ≤ d2248 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2236 p)
def d2249 (p : Pattern) : Int := if p 163 then d2248 p else d2219 p
theorem agree2249 (p q : Pattern) (h : Agree support p q) : d2249 p = d2249 q := by
  simp only [d2249, h 163 (by decide), agree2248 p q h, agree2219 p q h]
theorem nonnegative2249 (p : Pattern) : 0 ≤ d2249 p :=
  nonnegative_ite (p 163) (nonnegative2248 p) (nonnegative2219 p)
def d2250 (p : Pattern) : Int := if p 182 then d12 p else d2216 p
theorem agree2250 (p q : Pattern) (h : Agree support p q) : d2250 p = d2250 q := by
  simp only [d2250, h 182 (by decide), agree12 p q h, agree2216 p q h]
theorem nonnegative2250 (p : Pattern) : 0 ≤ d2250 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2216 p)
def d2251 (p : Pattern) : Int := if p 163 then d12 p else d2250 p
theorem agree2251 (p q : Pattern) (h : Agree support p q) : d2251 p = d2251 q := by
  simp only [d2251, h 163 (by decide), agree12 p q h, agree2250 p q h]
theorem nonnegative2251 (p : Pattern) : 0 ≤ d2251 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2250 p)
def d2252 (p : Pattern) : Int := if p 162 then d2251 p else d2249 p
theorem agree2252 (p q : Pattern) (h : Agree support p q) : d2252 p = d2252 q := by
  simp only [d2252, h 162 (by decide), agree2251 p q h, agree2249 p q h]
theorem nonnegative2252 (p : Pattern) : 0 ≤ d2252 p :=
  nonnegative_ite (p 162) (nonnegative2251 p) (nonnegative2249 p)
def d2253 (p : Pattern) : Int := if p 161 then d2252 p else d2247 p
theorem agree2253 (p q : Pattern) (h : Agree support p q) : d2253 p = d2253 q := by
  simp only [d2253, h 161 (by decide), agree2252 p q h, agree2247 p q h]
theorem nonnegative2253 (p : Pattern) : 0 ≤ d2253 p :=
  nonnegative_ite (p 161) (nonnegative2252 p) (nonnegative2247 p)
def d2254 (p : Pattern) : Int := if p 160 then d2253 p else d2243 p
theorem agree2254 (p q : Pattern) (h : Agree support p q) : d2254 p = d2254 q := by
  simp only [d2254, h 160 (by decide), agree2253 p q h, agree2243 p q h]
theorem nonnegative2254 (p : Pattern) : 0 ≤ d2254 p :=
  nonnegative_ite (p 160) (nonnegative2253 p) (nonnegative2243 p)
def d2255 (p : Pattern) : Int := if p 141 then d2254 p else d2228 p
theorem agree2255 (p q : Pattern) (h : Agree support p q) : d2255 p = d2255 q := by
  simp only [d2255, h 141 (by decide), agree2254 p q h, agree2228 p q h]
theorem nonnegative2255 (p : Pattern) : 0 ≤ d2255 p :=
  nonnegative_ite (p 141) (nonnegative2254 p) (nonnegative2228 p)
def d2256 (p : Pattern) : Int := if p 162 then d2202 p else d2201 p
theorem agree2256 (p q : Pattern) (h : Agree support p q) : d2256 p = d2256 q := by
  simp only [d2256, h 162 (by decide), agree2202 p q h, agree2201 p q h]
theorem nonnegative2256 (p : Pattern) : 0 ≤ d2256 p :=
  nonnegative_ite (p 162) (nonnegative2202 p) (nonnegative2201 p)
def d2257 (p : Pattern) : Int := if p 161 then d2207 p else d2256 p
theorem agree2257 (p q : Pattern) (h : Agree support p q) : d2257 p = d2257 q := by
  simp only [d2257, h 161 (by decide), agree2207 p q h, agree2256 p q h]
theorem nonnegative2257 (p : Pattern) : 0 ≤ d2257 p :=
  nonnegative_ite (p 161) (nonnegative2207 p) (nonnegative2256 p)
def d2258 (p : Pattern) : Int := if p 182 then d2213 p else d2212 p
theorem agree2258 (p q : Pattern) (h : Agree support p q) : d2258 p = d2258 q := by
  simp only [d2258, h 182 (by decide), agree2213 p q h, agree2212 p q h]
theorem nonnegative2258 (p : Pattern) : 0 ≤ d2258 p :=
  nonnegative_ite (p 182) (nonnegative2213 p) (nonnegative2212 p)
def d2259 (p : Pattern) : Int := if p 163 then d2258 p else d2232 p
theorem agree2259 (p q : Pattern) (h : Agree support p q) : d2259 p = d2259 q := by
  simp only [d2259, h 163 (by decide), agree2258 p q h, agree2232 p q h]
theorem nonnegative2259 (p : Pattern) : 0 ≤ d2259 p :=
  nonnegative_ite (p 163) (nonnegative2258 p) (nonnegative2232 p)
def d2260 (p : Pattern) : Int := if p 162 then d2241 p else d2259 p
theorem agree2260 (p q : Pattern) (h : Agree support p q) : d2260 p = d2260 q := by
  simp only [d2260, h 162 (by decide), agree2241 p q h, agree2259 p q h]
theorem nonnegative2260 (p : Pattern) : 0 ≤ d2260 p :=
  nonnegative_ite (p 162) (nonnegative2241 p) (nonnegative2259 p)
def d2261 (p : Pattern) : Int := if p 161 then d12 p else d2260 p
theorem agree2261 (p q : Pattern) (h : Agree support p q) : d2261 p = d2261 q := by
  simp only [d2261, h 161 (by decide), agree12 p q h, agree2260 p q h]
theorem nonnegative2261 (p : Pattern) : 0 ≤ d2261 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2260 p)
def d2262 (p : Pattern) : Int := if p 160 then d2261 p else d2257 p
theorem agree2262 (p q : Pattern) (h : Agree support p q) : d2262 p = d2262 q := by
  simp only [d2262, h 160 (by decide), agree2261 p q h, agree2257 p q h]
theorem nonnegative2262 (p : Pattern) : 0 ≤ d2262 p :=
  nonnegative_ite (p 160) (nonnegative2261 p) (nonnegative2257 p)
def d2263 (p : Pattern) : Int := if p 163 then d2232 p else d2201 p
theorem agree2263 (p q : Pattern) (h : Agree support p q) : d2263 p = d2263 q := by
  simp only [d2263, h 163 (by decide), agree2232 p q h, agree2201 p q h]
theorem nonnegative2263 (p : Pattern) : 0 ≤ d2263 p :=
  nonnegative_ite (p 163) (nonnegative2232 p) (nonnegative2201 p)
def d2264 (p : Pattern) : Int := if p 162 then d2234 p else d2263 p
theorem agree2264 (p q : Pattern) (h : Agree support p q) : d2264 p = d2264 q := by
  simp only [d2264, h 162 (by decide), agree2234 p q h, agree2263 p q h]
theorem nonnegative2264 (p : Pattern) : 0 ≤ d2264 p :=
  nonnegative_ite (p 162) (nonnegative2234 p) (nonnegative2263 p)
def d2265 (p : Pattern) : Int := if p 161 then d2242 p else d2264 p
theorem agree2265 (p q : Pattern) (h : Agree support p q) : d2265 p = d2265 q := by
  simp only [d2265, h 161 (by decide), agree2242 p q h, agree2264 p q h]
theorem nonnegative2265 (p : Pattern) : 0 ≤ d2265 p :=
  nonnegative_ite (p 161) (nonnegative2242 p) (nonnegative2264 p)
def d2266 (p : Pattern) : Int := if p 163 then d12 p else d2258 p
theorem agree2266 (p q : Pattern) (h : Agree support p q) : d2266 p = d2266 q := by
  simp only [d2266, h 163 (by decide), agree12 p q h, agree2258 p q h]
theorem nonnegative2266 (p : Pattern) : 0 ≤ d2266 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2258 p)
def d2267 (p : Pattern) : Int := if p 162 then d12 p else d2266 p
theorem agree2267 (p q : Pattern) (h : Agree support p q) : d2267 p = d2267 q := by
  simp only [d2267, h 162 (by decide), agree12 p q h, agree2266 p q h]
theorem nonnegative2267 (p : Pattern) : 0 ≤ d2267 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2266 p)
def d2268 (p : Pattern) : Int := if p 161 then d12 p else d2267 p
theorem agree2268 (p q : Pattern) (h : Agree support p q) : d2268 p = d2268 q := by
  simp only [d2268, h 161 (by decide), agree12 p q h, agree2267 p q h]
theorem nonnegative2268 (p : Pattern) : 0 ≤ d2268 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2267 p)
def d2269 (p : Pattern) : Int := if p 160 then d2268 p else d2265 p
theorem agree2269 (p q : Pattern) (h : Agree support p q) : d2269 p = d2269 q := by
  simp only [d2269, h 160 (by decide), agree2268 p q h, agree2265 p q h]
theorem nonnegative2269 (p : Pattern) : 0 ≤ d2269 p :=
  nonnegative_ite (p 160) (nonnegative2268 p) (nonnegative2265 p)
def d2270 (p : Pattern) : Int := if p 141 then d2269 p else d2262 p
theorem agree2270 (p q : Pattern) (h : Agree support p q) : d2270 p = d2270 q := by
  simp only [d2270, h 141 (by decide), agree2269 p q h, agree2262 p q h]
theorem nonnegative2270 (p : Pattern) : 0 ≤ d2270 p :=
  nonnegative_ite (p 141) (nonnegative2269 p) (nonnegative2262 p)
def d2271 (p : Pattern) : Int := if p 138 then d2270 p else d2255 p
theorem agree2271 (p q : Pattern) (h : Agree support p q) : d2271 p = d2271 q := by
  simp only [d2271, h 138 (by decide), agree2270 p q h, agree2255 p q h]
theorem nonnegative2271 (p : Pattern) : 0 ≤ d2271 p :=
  nonnegative_ite (p 138) (nonnegative2270 p) (nonnegative2255 p)
def d2272 (p : Pattern) : Int := if p 163 then d2201 p else d2195 p
theorem agree2272 (p q : Pattern) (h : Agree support p q) : d2272 p = d2272 q := by
  simp only [d2272, h 163 (by decide), agree2201 p q h, agree2195 p q h]
theorem nonnegative2272 (p : Pattern) : 0 ≤ d2272 p :=
  nonnegative_ite (p 163) (nonnegative2201 p) (nonnegative2195 p)
def d2273 (p : Pattern) : Int := if p 162 then d2202 p else d2272 p
theorem agree2273 (p q : Pattern) (h : Agree support p q) : d2273 p = d2273 q := by
  simp only [d2273, h 162 (by decide), agree2202 p q h, agree2272 p q h]
theorem nonnegative2273 (p : Pattern) : 0 ≤ d2273 p :=
  nonnegative_ite (p 162) (nonnegative2202 p) (nonnegative2272 p)
def d2274 (p : Pattern) : Int := if p 161 then d2207 p else d2273 p
theorem agree2274 (p q : Pattern) (h : Agree support p q) : d2274 p = d2274 q := by
  simp only [d2274, h 161 (by decide), agree2207 p q h, agree2273 p q h]
theorem nonnegative2274 (p : Pattern) : 0 ≤ d2274 p :=
  nonnegative_ite (p 161) (nonnegative2207 p) (nonnegative2273 p)
def d2275 (p : Pattern) : Int := if p 160 then d2261 p else d2274 p
theorem agree2275 (p q : Pattern) (h : Agree support p q) : d2275 p = d2275 q := by
  simp only [d2275, h 160 (by decide), agree2261 p q h, agree2274 p q h]
theorem nonnegative2275 (p : Pattern) : 0 ≤ d2275 p :=
  nonnegative_ite (p 160) (nonnegative2261 p) (nonnegative2274 p)
def d2276 (p : Pattern) : Int := if p 141 then d2269 p else d2275 p
theorem agree2276 (p q : Pattern) (h : Agree support p q) : d2276 p = d2276 q := by
  simp only [d2276, h 141 (by decide), agree2269 p q h, agree2275 p q h]
theorem nonnegative2276 (p : Pattern) : 0 ≤ d2276 p :=
  nonnegative_ite (p 141) (nonnegative2269 p) (nonnegative2275 p)
def d2277 (p : Pattern) : Int := if p 163 then d2240 p else d2205 p
theorem agree2277 (p q : Pattern) (h : Agree support p q) : d2277 p = d2277 q := by
  simp only [d2277, h 163 (by decide), agree2240 p q h, agree2205 p q h]
theorem nonnegative2277 (p : Pattern) : 0 ≤ d2277 p :=
  nonnegative_ite (p 163) (nonnegative2240 p) (nonnegative2205 p)
def d2278 (p : Pattern) : Int := if p 162 then d2241 p else d2277 p
theorem agree2278 (p q : Pattern) (h : Agree support p q) : d2278 p = d2278 q := by
  simp only [d2278, h 162 (by decide), agree2241 p q h, agree2277 p q h]
theorem nonnegative2278 (p : Pattern) : 0 ≤ d2278 p :=
  nonnegative_ite (p 162) (nonnegative2241 p) (nonnegative2277 p)
def d2279 (p : Pattern) : Int := if p 162 then d12 p else d2241 p
theorem agree2279 (p q : Pattern) (h : Agree support p q) : d2279 p = d2279 q := by
  simp only [d2279, h 162 (by decide), agree12 p q h, agree2241 p q h]
theorem nonnegative2279 (p : Pattern) : 0 ≤ d2279 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2241 p)
end NetHack.Sokoban22Refined85
