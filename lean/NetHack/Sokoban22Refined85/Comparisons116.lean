/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons115
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16240 (p : Pattern) (guard : d1 p = 1) : d1962 p ≤ (2 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16237 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16239 p hg
    simpa only [d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16241 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16242 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d23 p := by
  omega
theorem compare16243 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16241 p hg
    simpa only [d1964, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16242 p hg
    simpa only [d1964, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16244 (p : Pattern) (guard : d1 p = 1) : d2135 p ≤ (2 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16243 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16239 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16245 (p : Pattern) (guard : d1 p = 1) : d2136 p ≤ (2 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16240 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16244 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16246 (p : Pattern) (guard : d4474 p = 1) : d2137 p ≤ (2 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16245 p hg
    simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d4474, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16247 (p : Pattern) (guard : d4475 p = 1) : d2138 p ≤ (2 : Int) + d24 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16234 p hg
    simpa only [d4475, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16246 p hg
    simpa only [d4475, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16248 (p : Pattern) (guard : d4475 p = 1) : d2139 p ≤ (2 : Int) + d4479 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2139, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16247 p hg
    simpa only [d2139, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2139, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2139, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16249 (p : Pattern) (guard : d4475 p = 1) : d2140 p ≤ (2 : Int) + d4588 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2140, d4588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16248 p hg
    simpa only [d2140, d4588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2140, d4588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2140, d4588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16250 (p : Pattern) (guard : d4475 p = 1) : d2141 p ≤ (2 : Int) + d4589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2141, d4589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16233 p hg
    simpa only [d2141, d4589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2141, d4589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16249 p hg
    simpa only [d2141, d4589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16251 (p : Pattern) (guard : d0 p = 1) : d2146 p ≤ (2 : Int) + d4589 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16252 (p : Pattern) (guard : d4476 p = 1) : d2147 p ≤ (2 : Int) + d4589 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16250 p hg
    simpa only [d4476, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16251 p hg
    simpa only [d4476, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16253 (p : Pattern) (guard : d4476 p = 1) : d2148 p ≤ (2 : Int) + d5527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2148, d5527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16215 p hg
    simpa only [d2148, d5527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2148, d5527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16252 p hg
    simpa only [d2148, d5527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16254 (p : Pattern) (guard : d4475 p = 1) : d2149 p ≤ (2 : Int) + d4529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2149, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d2149, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2149, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16009 p hg
    simpa only [d2149, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16255 (p : Pattern) (guard : d4475 p = 1) : d2150 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16038 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16256 (p : Pattern) (guard : d4475 p = 1) : d2151 p ≤ (2 : Int) + d4530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2151, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16254 p hg
    simpa only [d2151, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2151, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16255 p hg
    simpa only [d2151, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16257 (p : Pattern) (guard : d4475 p = 1) : d2152 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2152, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16256 p hg
    simpa only [d2152, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2152, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16043 p hg
    simpa only [d2152, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16258 (p : Pattern) (guard : d4476 p = 1) : d2153 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16257 p hg
    simpa only [d4476, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16045 p hg
    simpa only [d4476, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16259 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (2 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16260 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d9 p := by
  change (3 : Int) ≤ (2 : Int) + 9
  decide
theorem compare16261 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16262 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16261 p hg
    simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16263 (p : Pattern) (guard : d1 p = 1) : d1891 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16264 (p : Pattern) (guard : d1 p = 1) : d1892 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1892, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16263 p hg
    simpa only [d1892, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1892, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16242 p hg
    simpa only [d1892, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16265 (p : Pattern) (guard : d1 p = 1) : d1893 p ≤ (2 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16262 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16264 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16266 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d9 p := by
  change (7 : Int) ≤ (2 : Int) + 9
  decide
theorem compare16267 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16266 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16268 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16266 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d119, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16269 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16267 p hg
    simpa only [d1895, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16268 p hg
    simpa only [d1895, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16270 (p : Pattern) (guard : d1 p = 1) : d2154 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16260 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16271 (p : Pattern) (guard : d1 p = 1) : d2155 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2155, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16270 p hg
    simpa only [d2155, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2155, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d2155, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16272 (p : Pattern) (guard : d1 p = 1) : d2156 p ≤ (2 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16269 p hg
    simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16271 p hg
    simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16273 (p : Pattern) (guard : d1 p = 1) : d2157 p ≤ (2 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16265 p hg
    simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16272 p hg
    simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16274 (p : Pattern) (guard : d4474 p = 1) : d2158 p ≤ (2 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16273 p hg
    simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16275 (p : Pattern) (guard : d4475 p = 1) : d2159 p ≤ (2 : Int) + d24 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16259 p hg
    simpa only [d4475, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16274 p hg
    simpa only [d4475, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16276 (p : Pattern) (guard : d4475 p = 1) : d2160 p ≤ (2 : Int) + d4479 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2160, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16275 p hg
    simpa only [d2160, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2160, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16038 p hg
    simpa only [d2160, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16277 (p : Pattern) (guard : d4475 p = 1) : d2161 p ≤ (2 : Int) + d4588 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2161, d4588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16276 p hg
    simpa only [d2161, d4588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2161, d4588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16189 p hg
    simpa only [d2161, d4588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16278 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16279 (p : Pattern) (guard : d1 p = 1) : d317 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16280 (p : Pattern) (guard : d1 p = 1) : d1901 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16279 p hg
    simpa only [d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16281 (p : Pattern) (guard : d1 p = 1) : d1902 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16282 (p : Pattern) (guard : d1 p = 1) : d1903 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16281 p hg
    simpa only [d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16283 (p : Pattern) (guard : d1 p = 1) : d1904 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16282 p hg
    simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16279 p hg
    simpa only [d1904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16284 (p : Pattern) (guard : d1 p = 1) : d1905 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16280 p hg
    simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16283 p hg
    simpa only [d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16285 (p : Pattern) (guard : d4474 p = 1) : d1906 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16284 p hg
    simpa only [d4474, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16286 (p : Pattern) (guard : d4475 p = 1) : d1974 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16278 p hg
    simpa only [d4475, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16285 p hg
    simpa only [d4475, d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16287 (p : Pattern) (guard : d4475 p = 1) : d1985 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16286 p hg
    simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16288 (p : Pattern) (guard : d4475 p = 1) : d1986 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16287 p hg
    simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16289 (p : Pattern) (guard : d4475 p = 1) : d2162 p ≤ (2 : Int) + d4596 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2162, d4596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16277 p hg
    simpa only [d2162, d4596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2162, d4596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16288 p hg
    simpa only [d2162, d4596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16290 (p : Pattern) (guard : d0 p = 1) : d2164 p ≤ (2 : Int) + d4596 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16291 (p : Pattern) (guard : d4476 p = 1) : d2165 p ≤ (2 : Int) + d4596 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16289 p hg
    simpa only [d4476, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16290 p hg
    simpa only [d4476, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16292 (p : Pattern) (guard : d4476 p = 1) : d2166 p ≤ (2 : Int) + d5528 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2166, d5528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16258 p hg
    simpa only [d2166, d5528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2166, d5528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16291 p hg
    simpa only [d2166, d5528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16293 (p : Pattern) (guard : d4476 p = 1) : d2167 p ≤ (2 : Int) + d5529 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2167, d5529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16253 p hg
    simpa only [d2167, d5529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2167, d5529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16292 p hg
    simpa only [d2167, d5529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16294 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16295 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d11 p := by
  change (1 : Int) ≤ (2 : Int) + 11
  decide
theorem compare16296 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16297 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16296 p hg
    simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16298 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d11 p := by
  change (7 : Int) ≤ (2 : Int) + 11
  decide
theorem compare16299 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16300 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16298 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d119, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16301 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16299 p hg
    simpa only [d1946, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16300 p hg
    simpa only [d1946, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16302 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16297 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16301 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16303 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d11 p := by
  change (5 : Int) ≤ (2 : Int) + 11
  decide
theorem compare16304 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16305 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16303 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16306 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16304 p hg
    simpa only [d1940, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16305 p hg
    simpa only [d1940, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16307 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16295 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16308 (p : Pattern) (guard : d1 p = 1) : d1955 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1955, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16307 p hg
    simpa only [d1955, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1955, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1775 p hg
    simpa only [d1955, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16309 (p : Pattern) (guard : d1 p = 1) : d1956 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16306 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16308 p hg
    simpa only [d1956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16310 (p : Pattern) (guard : d1 p = 1) : d1957 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16302 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16309 p hg
    simpa only [d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16311 (p : Pattern) (guard : d4474 p = 1) : d1958 p ≤ (2 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16310 p hg
    simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d4474, d1958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16312 (p : Pattern) (guard : d4475 p = 1) : d1959 p ≤ (2 : Int) + d40 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16294 p hg
    simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16311 p hg
    simpa only [d4475, d1959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16313 (p : Pattern) (guard : d4475 p = 1) : d2149 p ≤ (2 : Int) + d4605 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2149, d4605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d2149, d4605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2149, d4605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16312 p hg
    simpa only [d2149, d4605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16314 (p : Pattern) (guard : d4475 p = 1) : d2168 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16038 p hg
    simpa only [d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16315 (p : Pattern) (guard : d4475 p = 1) : d2169 p ≤ (2 : Int) + d4606 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2169, d4606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16313 p hg
    simpa only [d2169, d4606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2169, d4606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16314 p hg
    simpa only [d2169, d4606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16316 (p : Pattern) (guard : d4475 p = 1) : d2170 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15826 p hg
    simpa only [d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16317 (p : Pattern) (guard : d4475 p = 1) : d2171 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16316 p hg
    simpa only [d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16318 (p : Pattern) (guard : d4475 p = 1) : d2172 p ≤ (2 : Int) + d4607 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2172, d4607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16315 p hg
    simpa only [d2172, d4607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2172, d4607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16317 p hg
    simpa only [d2172, d4607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16319 (p : Pattern) (guard : d0 p = 1) : d2175 p ≤ (2 : Int) + d4607 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16320 (p : Pattern) (guard : d4476 p = 1) : d2176 p ≤ (2 : Int) + d4607 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16318 p hg
    simpa only [d4476, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16319 p hg
    simpa only [d4476, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16321 (p : Pattern) (guard : d4476 p = 1) : d2177 p ≤ (2 : Int) + d5530 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2177, d5530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16320 p hg
    simpa only [d2177, d5530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2177, d5530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16291 p hg
    simpa only [d2177, d5530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16322 (p : Pattern) (guard : d4476 p = 1) : d2178 p ≤ (2 : Int) + d5531 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2178, d5531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16321 p hg
    simpa only [d2178, d5531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2178, d5531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d2178, d5531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16323 (p : Pattern) (guard : d4476 p = 1) : d2179 p ≤ (2 : Int) + d5532 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2179, d5532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16293 p hg
    simpa only [d2179, d5532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2179, d5532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16322 p hg
    simpa only [d2179, d5532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16324 (p : Pattern) (guard : d4476 p = 1) : d2180 p ≤ (2 : Int) + d5533 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2180, d5533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16197 p hg
    simpa only [d2180, d5533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2180, d5533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16323 p hg
    simpa only [d2180, d5533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16325 (p : Pattern) (guard : d4476 p = 1) : d2181 p ≤ (2 : Int) + d5534 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2181, d5534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15898 p hg
    simpa only [d2181, d5534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2181, d5534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16324 p hg
    simpa only [d2181, d5534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16326 (p : Pattern) (guard : d4476 p = 1) : d2182 p ≤ (2 : Int) + d5535 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2182, d5535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16181 p hg
    simpa only [d2182, d5535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2182, d5535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16325 p hg
    simpa only [d2182, d5535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16327 (p : Pattern) (guard : d4476 p = 1) : d2183 p ≤ (2 : Int) + d5536 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2183, d5536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16068 p hg
    simpa only [d2183, d5536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2183, d5536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16326 p hg
    simpa only [d2183, d5536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16328 (p : Pattern) (guard : d0 p = 1) : d321 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16329 (p : Pattern) (guard : d4474 p = 1) : d1682 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1682, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1682, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1682, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16328 p hg
    simpa only [d4474, d1682, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16330 (p : Pattern) (guard : d4474 p = 1) : d1687 p ≤ (0 : Int) + d1687 p := by
  omega
theorem compare16331 (p : Pattern) (guard : d4474 p = 1) : d1688 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1688, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16329 p hg
    simpa only [d1688, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1688, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d1688, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16332 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16333 (p : Pattern) (guard : d4474 p = 1) : d1689 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1689, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1689, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1689, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16332 p hg
    simpa only [d4474, d1689, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16334 (p : Pattern) (guard : d4474 p = 1) : d1690 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1690, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16333 p hg
    simpa only [d1690, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1690, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d1690, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16335 (p : Pattern) (guard : d4474 p = 1) : d1691 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16331 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16334 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16336 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12770 p hg
    simpa only [d4474, d15, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16337 (p : Pattern) (guard : d4474 p = 1) : d1692 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1692, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16336 p hg
    simpa only [d1692, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1692, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d1692, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16338 (p : Pattern) (guard : d4474 p = 1) : d19 p ≤ (0 : Int) + d2897 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d19, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d19, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d19, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12957 p hg
    simpa only [d4474, d19, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16339 (p : Pattern) (guard : d4474 p = 1) : d1697 p ≤ (0 : Int) + d1697 p := by
  omega
theorem compare16340 (p : Pattern) (guard : d4474 p = 1) : d1698 p ≤ (0 : Int) + d2898 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1698, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16338 p hg
    simpa only [d1698, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1698, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16339 p hg
    simpa only [d1698, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16341 (p : Pattern) (guard : d4474 p = 1) : d1699 p ≤ (0 : Int) + d2899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1699, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16337 p hg
    simpa only [d1699, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1699, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16340 p hg
    simpa only [d1699, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16342 (p : Pattern) (guard : d4474 p = 1) : d1700 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1700, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16335 p hg
    simpa only [d1700, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1700, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d1700, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16343 (p : Pattern) (guard : d4474 p = 1) : d25 p ≤ (0 : Int) + d2901 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d25, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4474, d25, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d25, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12781 p hg
    simpa only [d4474, d25, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16344 (p : Pattern) (guard : d4474 p = 1) : d1705 p ≤ (0 : Int) + d1705 p := by
  omega
theorem compare16345 (p : Pattern) (guard : d4474 p = 1) : d1706 p ≤ (0 : Int) + d2902 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1706, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16343 p hg
    simpa only [d1706, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1706, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16344 p hg
    simpa only [d1706, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16346 (p : Pattern) (guard : d4474 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare16347 (p : Pattern) (guard : d4474 p = 1) : d1707 p ≤ (0 : Int) + d2903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1707, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16345 p hg
    simpa only [d1707, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1707, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1707, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16348 (p : Pattern) (guard : d4474 p = 1) : d1708 p ≤ (0 : Int) + d2904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1708, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16341 p hg
    simpa only [d1708, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1708, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16347 p hg
    simpa only [d1708, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16349 (p : Pattern) (guard : d4474 p = 1) : d1709 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1709, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16342 p hg
    simpa only [d1709, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1709, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16348 p hg
    simpa only [d1709, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16350 (p : Pattern) (guard : d4474 p = 1) : d15 p ≤ (0 : Int) + d2906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d15, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d15, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d15, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12775 p hg
    simpa only [d4474, d15, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16351 (p : Pattern) (guard : d4474 p = 1) : d1718 p ≤ (0 : Int) + d1718 p := by
  omega
theorem compare16352 (p : Pattern) (guard : d4474 p = 1) : d1719 p ≤ (0 : Int) + d2907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1719, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d1719, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1719, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16351 p hg
    simpa only [d1719, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16353 (p : Pattern) (guard : d4474 p = 1) : d1725 p ≤ (0 : Int) + d1725 p := by
  omega
theorem compare16354 (p : Pattern) (guard : d4474 p = 1) : d1726 p ≤ (0 : Int) + d2908 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1726, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d1726, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1726, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d1726, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16355 (p : Pattern) (guard : d4474 p = 1) : d1727 p ≤ (0 : Int) + d2909 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1727, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16352 p hg
    simpa only [d1727, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1727, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16354 p hg
    simpa only [d1727, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16356 (p : Pattern) (guard : d4474 p = 1) : d1730 p ≤ (0 : Int) + d1730 p := by
  omega
theorem compare16357 (p : Pattern) (guard : d4474 p = 1) : d1731 p ≤ (0 : Int) + d2910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1731, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d1731, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1731, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d1731, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16358 (p : Pattern) (guard : d4474 p = 1) : d19 p ≤ (0 : Int) + d2911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d19, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d19, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d19, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12777 p hg
    simpa only [d4474, d19, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16359 (p : Pattern) (guard : d4474 p = 1) : d1732 p ≤ (0 : Int) + d2912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1732, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16358 p hg
    simpa only [d1732, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1732, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1732, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16360 (p : Pattern) (guard : d4474 p = 1) : d1733 p ≤ (0 : Int) + d2913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1733, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16357 p hg
    simpa only [d1733, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1733, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d1733, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16361 (p : Pattern) (guard : d4474 p = 1) : d1734 p ≤ (0 : Int) + d2914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1734, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16355 p hg
    simpa only [d1734, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1734, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16360 p hg
    simpa only [d1734, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16362 (p : Pattern) (guard : d4474 p = 1) : d1735 p ≤ (0 : Int) + d2915 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1735, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16350 p hg
    simpa only [d1735, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1735, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d1735, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16363 (p : Pattern) (guard : d4474 p = 1) : d1736 p ≤ (0 : Int) + d2916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1736, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16362 p hg
    simpa only [d1736, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1736, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16359 p hg
    simpa only [d1736, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16364 (p : Pattern) (guard : d4474 p = 1) : d527 p ≤ (0 : Int) + d2917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d527, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16343 p hg
    simpa only [d527, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d527, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d527, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16365 (p : Pattern) (guard : d4474 p = 1) : d528 p ≤ (0 : Int) + d2918 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d528, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16364 p hg
    simpa only [d528, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d528, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d528, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16366 (p : Pattern) (guard : d4474 p = 1) : d1737 p ≤ (0 : Int) + d2919 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1737, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16363 p hg
    simpa only [d1737, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1737, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16365 p hg
    simpa only [d1737, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16367 (p : Pattern) (guard : d4474 p = 1) : d1738 p ≤ (0 : Int) + d2920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1738, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16361 p hg
    simpa only [d1738, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1738, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16366 p hg
    simpa only [d1738, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16368 (p : Pattern) (guard : d4474 p = 1) : d1739 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1739, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16349 p hg
    simpa only [d1739, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1739, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16367 p hg
    simpa only [d1739, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16369 (p : Pattern) (guard : d0 p = 1) : d335 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16370 (p : Pattern) (guard : d4474 p = 1) : d1740 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1740, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1740, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1740, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16369 p hg
    simpa only [d4474, d1740, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16371 (p : Pattern) (guard : d4474 p = 1) : d1741 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1741, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16370 p hg
    simpa only [d1741, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1741, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d1741, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16372 (p : Pattern) (guard : d4474 p = 1) : d32 p ≤ (0 : Int) + d2922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d32, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d32, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d32, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12972 p hg
    simpa only [d4474, d32, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16373 (p : Pattern) (guard : d4474 p = 1) : d1746 p ≤ (0 : Int) + d1746 p := by
  omega
theorem compare16374 (p : Pattern) (guard : d4474 p = 1) : d1747 p ≤ (0 : Int) + d2923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1747, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16372 p hg
    simpa only [d1747, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1747, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16373 p hg
    simpa only [d1747, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16375 (p : Pattern) (guard : d4474 p = 1) : d1748 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1748, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16371 p hg
    simpa only [d1748, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1748, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16374 p hg
    simpa only [d1748, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16376 (p : Pattern) (guard : d4474 p = 1) : d1749 p ≤ (0 : Int) + d2925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1749, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16340 p hg
    simpa only [d1749, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1749, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16345 p hg
    simpa only [d1749, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16377 (p : Pattern) (guard : d4474 p = 1) : d1750 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1750, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16375 p hg
    simpa only [d1750, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1750, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16376 p hg
    simpa only [d1750, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16378 (p : Pattern) (guard : d4474 p = 1) : d59 p ≤ (0 : Int) + d2927 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d59, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4474, d59, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d59, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12754 p hg
    simpa only [d4474, d59, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16379 (p : Pattern) (guard : d4474 p = 1) : d1753 p ≤ (0 : Int) + d1753 p := by
  omega
end NetHack.Sokoban22Refined85
