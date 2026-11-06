import NetHack.Soko22Hazard87.Compare028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7250 (p : Pattern) (guard : d2078 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7249 p hg
    simpa only [d2078, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d2078, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7251 (p : Pattern) (guard : d2079 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7250 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7252 (p : Pattern) (guard : d2080 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7251 p hg
    simpa only [d2080, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d2080, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7253 (p : Pattern) (guard : d2081 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7252 p hg
    simpa only [d2081, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2081, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7254 (p : Pattern) (guard : d2082 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2082, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d2082, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2082, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7253 p hg
    simpa only [d2082, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7255 (p : Pattern) (guard : d2083 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2082 p = 1 := by simpa only [d2083, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7254 p hg
    simpa only [d2083, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2083, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d2083, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7256 (p : Pattern) (guard : d2084 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2083 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7255 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7257 (p : Pattern) (guard : d2085 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7243 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2084 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7256 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7258 (p : Pattern) (guard : d2086 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2072 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7244 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2085 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7257 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7259 (p : Pattern) (guard : d2087 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2087, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d2087, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2086 p = 1 := by simpa only [d2087, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7258 p hg
    simpa only [d2087, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7260 (p : Pattern) (guard : d2088 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2088, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d2088, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2087 p = 1 := by simpa only [d2088, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7259 p hg
    simpa only [d2088, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7261 (p : Pattern) (guard : d2089 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2088 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7260 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7262 (p : Pattern) (guard : d2090 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2088 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7260 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7263 (p : Pattern) (guard : d2091 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2090 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7262 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7264 (p : Pattern) (guard : d2092 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2091 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7263 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7265 (p : Pattern) (guard : d2093 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2092 p = 1 := by simpa only [d2093, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7264 p hg
    simpa only [d2093, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2093, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d2093, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7266 (p : Pattern) (guard : d2094 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2094, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2094, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2093 p = 1 := by simpa only [d2094, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d2094, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7267 (p : Pattern) (guard : d2095 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2090 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7262 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7268 (p : Pattern) (guard : d2096 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2095 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7269 (p : Pattern) (guard : d2097 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2096 p = 1 := by simpa only [d2097, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d2097, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2097, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d2097, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7270 (p : Pattern) (guard : d2098 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2098, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2098, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2097 p = 1 := by simpa only [d2098, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d2098, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7271 (p : Pattern) (guard : d2099 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7272 (p : Pattern) (guard : d2100 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2099 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7271 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7273 (p : Pattern) (guard : d2101 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2100 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7274 (p : Pattern) (guard : d2102 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2101 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7275 (p : Pattern) (guard : d2103 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2098 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7276 (p : Pattern) (guard : d2104 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2103 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7277 (p : Pattern) (guard : d2105 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2104 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7278 (p : Pattern) (guard : d2106 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2105 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7279 (p : Pattern) (guard : d2107 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2102 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7274 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2106 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7280 (p : Pattern) (guard : d2108 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2107 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7281 (p : Pattern) (guard : d2109 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2108 p = 1 := by simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7280 p hg
    simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7282 (p : Pattern) (guard : d2110 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2109 p = 1 := by simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7283 (p : Pattern) (guard : d2111 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2110 p = 1 := by simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7284 (p : Pattern) (guard : d2112 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2111 p = 1 := by simpa only [d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7283 p hg
    simpa only [d2112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7285 (p : Pattern) (guard : d2113 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2112 p = 1 := by simpa only [d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7284 p hg
    simpa only [d2113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7286 (p : Pattern) (guard : d2114 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2113 p = 1 := by simpa only [d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7285 p hg
    simpa only [d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7287 (p : Pattern) (guard : d2115 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2101 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7288 (p : Pattern) (guard : d2116 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2105 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7289 (p : Pattern) (guard : d2117 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2115 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7287 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2116 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7288 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7290 (p : Pattern) (guard : d2118 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2117 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7289 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7291 (p : Pattern) (guard : d2119 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2118 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7290 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7292 (p : Pattern) (guard : d2120 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2119 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7291 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7293 (p : Pattern) (guard : d2121 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2120 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7294 (p : Pattern) (guard : d2122 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2111 p = 1 := by simpa only [d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7283 p hg
    simpa only [d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2121 p = 1 := by simpa only [d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7293 p hg
    simpa only [d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7295 (p : Pattern) (guard : d2123 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d2112 p = 1 := by simpa only [d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7284 p hg
    simpa only [d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2122 p = 1 := by simpa only [d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7294 p hg
    simpa only [d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7296 (p : Pattern) (guard : d2124 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2123 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7295 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7297 (p : Pattern) (guard : d2125 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2114 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7286 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2124 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7296 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7298 (p : Pattern) (guard : d2126 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2100 p = 1 := by simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7299 (p : Pattern) (guard : d2127 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2126 p = 1 := by simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7300 (p : Pattern) (guard : d2128 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2104 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7301 (p : Pattern) (guard : d2129 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2128 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7300 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7302 (p : Pattern) (guard : d2130 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2127 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7299 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2129 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7301 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7303 (p : Pattern) (guard : d2131 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2130 p = 1 := by simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7302 p hg
    simpa only [d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7304 (p : Pattern) (guard : d2132 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2131 p = 1 := by simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7303 p hg
    simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7305 (p : Pattern) (guard : d2133 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2132 p = 1 := by simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7304 p hg
    simpa only [d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7306 (p : Pattern) (guard : d2134 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2099 p = 1 := by simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7271 p hg
    simpa only [d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7307 (p : Pattern) (guard : d2135 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2134 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7308 (p : Pattern) (guard : d2136 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2135 p = 1 := by simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7307 p hg
    simpa only [d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7309 (p : Pattern) (guard : d2137 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2103 p = 1 := by simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7310 (p : Pattern) (guard : d2138 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2137 p = 1 := by simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7309 p hg
    simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7311 (p : Pattern) (guard : d2139 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2138 p = 1 := by simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7312 (p : Pattern) (guard : d2140 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2136 p = 1 := by simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7308 p hg
    simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2139 p = 1 := by simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7311 p hg
    simpa only [d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7313 (p : Pattern) (guard : d2141 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2140 p = 1 := by simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7312 p hg
    simpa only [d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7314 (p : Pattern) (guard : d2142 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2141 p = 1 := by simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7313 p hg
    simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7315 (p : Pattern) (guard : d2143 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7316 (p : Pattern) (guard : d2144 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7315 p hg
    simpa only [d2144, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d2144, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7317 (p : Pattern) (guard : d2145 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2145, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7318 (p : Pattern) (guard : d2146 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d2146, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7317 p hg
    simpa only [d2146, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7319 (p : Pattern) (guard : d2147 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7318 p hg
    simpa only [d2147, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d2147, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7320 (p : Pattern) (guard : d2148 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7319 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2038 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7321 (p : Pattern) (guard : d2149 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2148 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7320 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2057 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7229 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7322 (p : Pattern) (guard : d2150 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2149 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7321 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2070 p = 1 := by simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7323 (p : Pattern) (guard : d2151 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2151, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d2151, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2150 p = 1 := by simpa only [d2151, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7322 p hg
    simpa only [d2151, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7324 (p : Pattern) (guard : d2152 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2152, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d2152, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2151 p = 1 := by simpa only [d2152, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7323 p hg
    simpa only [d2152, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7325 (p : Pattern) (guard : d2153 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2152 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7324 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2075 p = 1 := by simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7326 (p : Pattern) (guard : d2154 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2153 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7325 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2089 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7327 (p : Pattern) (guard : d2155 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2154 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7326 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7328 (p : Pattern) (guard : d2156 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2155 p = 1 := by simpa only [d2156, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7327 p hg
    simpa only [d2156, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2156, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d2156, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7329 (p : Pattern) (guard : d2157 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2157, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d2157, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2156 p = 1 := by simpa only [d2157, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d2157, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7330 (p : Pattern) (guard : d7115 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d7115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7331 (p : Pattern) (guard : d5237 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7332 (p : Pattern) (guard : d5238 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7333 (p : Pattern) (guard : d5239 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7332 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7334 (p : Pattern) (guard : d5240 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7333 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7335 (p : Pattern) (guard : d5241 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7334 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7336 (p : Pattern) (guard : d5242 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7335 p hg
    simpa only [d5242, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5242, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7337 (p : Pattern) (guard : d5243 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7333 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7338 (p : Pattern) (guard : d5244 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7337 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7339 (p : Pattern) (guard : d5245 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7338 p hg
    simpa only [d5245, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5245, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7340 (p : Pattern) (guard : d5246 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7336 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7339 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7341 (p : Pattern) (guard : d5247 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d5247, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d5247, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7342 (p : Pattern) (guard : d5248 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7341 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7343 (p : Pattern) (guard : d5249 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d5249, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7342 p hg
    simpa only [d5249, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7344 (p : Pattern) (guard : d5250 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7343 p hg
    simpa only [d5250, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d5250, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7345 (p : Pattern) (guard : d5251 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7344 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7346 (p : Pattern) (guard : d5252 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7345 p hg
    simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7347 (p : Pattern) (guard : d5253 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d5237 p = 1 := by simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5252 p = 1 := by simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7346 p hg
    simpa only [d5253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7348 (p : Pattern) (guard : d5254 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5254, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d5254, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5253 p = 1 := by simpa only [d5254, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7347 p hg
    simpa only [d5254, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7349 (p : Pattern) (guard : d5255 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5255, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d5255, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5254 p = 1 := by simpa only [d5255, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7348 p hg
    simpa only [d5255, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7350 (p : Pattern) (guard : d5256 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d5255 p = 1 := by simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7349 p hg
    simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7351 (p : Pattern) (guard : d7116 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7115 p = 1 := by simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5256 p = 1 := by simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7350 p hg
    simpa only [d7116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7352 (p : Pattern) (guard : d7117 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7116 p = 1 := by simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7351 p hg
    simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d7117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7353 (p : Pattern) (guard : d7118 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7117 p = 1 := by simpa only [d7118, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7352 p hg
    simpa only [d7118, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7118, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d7118, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7354 (p : Pattern) (guard : d7119 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7119, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d7119, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7118 p = 1 := by simpa only [d7119, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7353 p hg
    simpa only [d7119, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7355 (p : Pattern) (guard : d7120 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2157 p = 1 := by simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7329 p hg
    simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7119 p = 1 := by simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7354 p hg
    simpa only [d7120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7356 (p : Pattern) (guard : d7121 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7120 p = 1 := by simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7355 p hg
    simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7357 (p : Pattern) (guard : d7122 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7121 p = 1 := by simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7356 p hg
    simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7358 (p : Pattern) (guard : d7123 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7122 p = 1 := by simpa only [d7123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7357 p hg
    simpa only [d7123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7359 (p : Pattern) (guard : d5257 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5256 p = 1 := by simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7350 p hg
    simpa only [d5257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7360 (p : Pattern) (guard : d5258 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d5257 p = 1 := by simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7359 p hg
    simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7361 (p : Pattern) (guard : d5259 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5258 p = 1 := by simpa only [d5259, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7360 p hg
    simpa only [d5259, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5259, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d5259, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7362 (p : Pattern) (guard : d5260 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5260, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d5260, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5259 p = 1 := by simpa only [d5260, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7361 p hg
    simpa only [d5260, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7363 (p : Pattern) (guard : d7124 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d5260 p = 1 := by simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7362 p hg
    simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d7124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7364 (p : Pattern) (guard : d7125 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7124 p = 1 := by simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7363 p hg
    simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7365 (p : Pattern) (guard : d7126 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7125 p = 1 := by simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7364 p hg
    simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7366 (p : Pattern) (guard : d7127 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7126 p = 1 := by simpa only [d7127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7365 p hg
    simpa only [d7127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7367 (p : Pattern) (guard : d7128 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7123 p = 1 := by simpa only [d7128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7358 p hg
    simpa only [d7128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7127 p = 1 := by simpa only [d7128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7366 p hg
    simpa only [d7128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7368 (p : Pattern) (guard : d82233 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7128 p = 1 := by simpa only [d82233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7367 p hg
    simpa only [d82233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7369 (p : Pattern) (guard : d6547 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7370 (p : Pattern) (guard : d6548 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6547 p = 1 := by simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7369 p hg
    simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7371 (p : Pattern) (guard : d6549 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6548 p = 1 := by simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7370 p hg
    simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7372 (p : Pattern) (guard : d6550 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6549 p = 1 := by simpa only [d6550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7371 p hg
    simpa only [d6550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7373 (p : Pattern) (guard : d6592 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6550 p = 1 := by simpa only [d6592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7372 p hg
    simpa only [d6592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7374 (p : Pattern) (guard : d6593 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6592 p = 1 := by simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7373 p hg
    simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7375 (p : Pattern) (guard : d82234 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82233 p = 1 := by simpa only [d82234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7368 p hg
    simpa only [d82234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6593 p = 1 := by simpa only [d82234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7374 p hg
    simpa only [d82234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7376 (p : Pattern) (guard : d82235 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d2142 p = 1 := by simpa only [d82235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7314 p hg
    simpa only [d82235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82234 p = 1 := by simpa only [d82235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7375 p hg
    simpa only [d82235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7377 (p : Pattern) (guard : d82236 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d2133 p = 1 := by simpa only [d82236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7305 p hg
    simpa only [d82236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82235 p = 1 := by simpa only [d82236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7376 p hg
    simpa only [d82236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7378 (p : Pattern) (guard : d82237 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82236 p = 1 := by simpa only [d82237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7377 p hg
    simpa only [d82237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7379 (p : Pattern) (guard : d2281 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2126 p = 1 := by simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7380 (p : Pattern) (guard : d2282 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2128 p = 1 := by simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7300 p hg
    simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7381 (p : Pattern) (guard : d2283 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2281 p = 1 := by simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7379 p hg
    simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2282 p = 1 := by simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7380 p hg
    simpa only [d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7382 (p : Pattern) (guard : d2284 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2283 p = 1 := by simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7381 p hg
    simpa only [d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7383 (p : Pattern) (guard : d2285 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2284 p = 1 := by simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7382 p hg
    simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7384 (p : Pattern) (guard : d2286 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2285 p = 1 := by simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7383 p hg
    simpa only [d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7385 (p : Pattern) (guard : d2287 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2135 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7307 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7386 (p : Pattern) (guard : d2288 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2138 p = 1 := by simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7387 (p : Pattern) (guard : d2289 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2287 p = 1 := by simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7385 p hg
    simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2288 p = 1 := by simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7388 (p : Pattern) (guard : d2290 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2289 p = 1 := by simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7387 p hg
    simpa only [d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7389 (p : Pattern) (guard : d2291 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2290 p = 1 := by simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7388 p hg
    simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7390 (p : Pattern) (guard : d7134 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7122 p = 1 := by simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7357 p hg
    simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7391 (p : Pattern) (guard : d7135 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7126 p = 1 := by simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7365 p hg
    simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7392 (p : Pattern) (guard : d7136 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7134 p = 1 := by simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7390 p hg
    simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7135 p = 1 := by simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d7136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7393 (p : Pattern) (guard : d82238 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7136 p = 1 := by simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7392 p hg
    simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7394 (p : Pattern) (guard : d6559 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6549 p = 1 := by simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7371 p hg
    simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7395 (p : Pattern) (guard : d6613 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6559 p = 1 := by simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7394 p hg
    simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7396 (p : Pattern) (guard : d6614 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6613 p = 1 := by simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7395 p hg
    simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7397 (p : Pattern) (guard : d82239 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82238 p = 1 := by simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7393 p hg
    simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6614 p = 1 := by simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d82239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7398 (p : Pattern) (guard : d82240 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d2291 p = 1 := by simpa only [d82240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7389 p hg
    simpa only [d82240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82239 p = 1 := by simpa only [d82240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7397 p hg
    simpa only [d82240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7399 (p : Pattern) (guard : d82241 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d2286 p = 1 := by simpa only [d82241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7384 p hg
    simpa only [d82241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82240 p = 1 := by simpa only [d82241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7398 p hg
    simpa only [d82241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7400 (p : Pattern) (guard : d82242 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82236 p = 1 := by simpa only [d82242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7377 p hg
    simpa only [d82242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82241 p = 1 := by simpa only [d82242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7399 p hg
    simpa only [d82242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7401 (p : Pattern) (guard : d82243 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82237 p = 1 := by simpa only [d82243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7378 p hg
    simpa only [d82243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82242 p = 1 := by simpa only [d82243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d82243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7402 (p : Pattern) (guard : d7143 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7127 p = 1 := by simpa only [d7143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7366 p hg
    simpa only [d7143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2106 p = 1 := by simpa only [d7143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d7143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7403 (p : Pattern) (guard : d7144 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7143 p = 1 := by simpa only [d7144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7402 p hg
    simpa only [d7144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7404 (p : Pattern) (guard : d7145 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d7144 p = 1 := by simpa only [d7145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d7145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7405 (p : Pattern) (guard : d7146 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7145 p = 1 := by simpa only [d7146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7404 p hg
    simpa only [d7146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7406 (p : Pattern) (guard : d7147 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d7147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7146 p = 1 := by simpa only [d7147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7405 p hg
    simpa only [d7147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7407 (p : Pattern) (guard : d2305 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2106 p = 1 := by simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7408 (p : Pattern) (guard : d2306 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2305 p = 1 := by simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7407 p hg
    simpa only [d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7409 (p : Pattern) (guard : d2307 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2306 p = 1 := by simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7410 (p : Pattern) (guard : d2308 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2307 p = 1 := by simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7409 p hg
    simpa only [d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7411 (p : Pattern) (guard : d2309 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2308 p = 1 := by simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7410 p hg
    simpa only [d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7412 (p : Pattern) (guard : d7148 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d7147 p = 1 := by simpa only [d7148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7406 p hg
    simpa only [d7148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2309 p = 1 := by simpa only [d7148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7411 p hg
    simpa only [d7148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7413 (p : Pattern) (guard : d2311 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2116 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7288 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7414 (p : Pattern) (guard : d2312 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2311 p = 1 := by simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7413 p hg
    simpa only [d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7415 (p : Pattern) (guard : d2313 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2312 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7416 (p : Pattern) (guard : d2314 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2313 p = 1 := by simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7415 p hg
    simpa only [d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7417 (p : Pattern) (guard : d2315 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2314 p = 1 := by simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7416 p hg
    simpa only [d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7418 (p : Pattern) (guard : d2316 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2309 p = 1 := by simpa only [d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7411 p hg
    simpa only [d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2315 p = 1 := by simpa only [d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7417 p hg
    simpa only [d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7419 (p : Pattern) (guard : d7149 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d7148 p = 1 := by simpa only [d7149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7412 p hg
    simpa only [d7149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2316 p = 1 := by simpa only [d7149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7418 p hg
    simpa only [d7149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7420 (p : Pattern) (guard : d82244 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82243 p = 1 := by simpa only [d82244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7401 p hg
    simpa only [d82244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7149 p = 1 := by simpa only [d82244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d82244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7421 (p : Pattern) (guard : d82245 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82244 p = 1 := by simpa only [d82245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7420 p hg
    simpa only [d82245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7422 (p : Pattern) (guard : d82246 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d2125 p = 1 := by simpa only [d82246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7297 p hg
    simpa only [d82246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82245 p = 1 := by simpa only [d82246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7421 p hg
    simpa only [d82246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7423 (p : Pattern) (guard : d1997 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7424 (p : Pattern) (guard : d1998 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7423 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7425 (p : Pattern) (guard : d1999 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7426 (p : Pattern) (guard : d2000 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7425 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7427 (p : Pattern) (guard : d2001 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7428 (p : Pattern) (guard : d2002 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7427 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7429 (p : Pattern) (guard : d2003 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7428 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7430 (p : Pattern) (guard : d2004 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7426 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7431 (p : Pattern) (guard : d2005 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7432 (p : Pattern) (guard : d2006 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7431 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7433 (p : Pattern) (guard : d2007 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7432 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7434 (p : Pattern) (guard : d2008 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7433 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7435 (p : Pattern) (guard : d2009 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7430 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7434 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7436 (p : Pattern) (guard : d2010 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7435 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7437 (p : Pattern) (guard : d2011 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7438 (p : Pattern) (guard : d2012 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d2012, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d2012, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7439 (p : Pattern) (guard : d2143 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7438 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7440 (p : Pattern) (guard : d2144 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d2144, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2144, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7441 (p : Pattern) (guard : d2145 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2145, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7442 (p : Pattern) (guard : d2146 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7441 p hg
    simpa only [d2146, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7443 (p : Pattern) (guard : d2147 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d2147, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d2147, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7444 (p : Pattern) (guard : d2013 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7423 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7445 (p : Pattern) (guard : d2014 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7444 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7446 (p : Pattern) (guard : d2015 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7425 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7445 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7447 (p : Pattern) (guard : d2016 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d2016, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d2016, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7448 (p : Pattern) (guard : d2017 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7423 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7447 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7449 (p : Pattern) (guard : d2018 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7448 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7450 (p : Pattern) (guard : d2019 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7428 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7449 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7451 (p : Pattern) (guard : d2020 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7446 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7450 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7452 (p : Pattern) (guard : d2021 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7447 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7453 (p : Pattern) (guard : d2022 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7452 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7454 (p : Pattern) (guard : d2023 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7432 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7455 (p : Pattern) (guard : d2024 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7454 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7456 (p : Pattern) (guard : d2025 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7455 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7457 (p : Pattern) (guard : d2026 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7435 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7458 (p : Pattern) (guard : d2027 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7444 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7459 (p : Pattern) (guard : d2028 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7458 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7460 (p : Pattern) (guard : d2029 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7459 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7461 (p : Pattern) (guard : d2030 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7460 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7462 (p : Pattern) (guard : d2031 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7463 (p : Pattern) (guard : d2032 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7457 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7462 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7464 (p : Pattern) (guard : d2033 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7463 p hg
    simpa only [d2033, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d2033, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7465 (p : Pattern) (guard : d2034 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7438 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7464 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7466 (p : Pattern) (guard : d2035 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7465 p hg
    simpa only [d2035, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2035, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7467 (p : Pattern) (guard : d2036 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7466 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7468 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7467 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7469 (p : Pattern) (guard : d2038 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7468 p hg
    simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d2038, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7470 (p : Pattern) (guard : d2148 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7443 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2038 p = 1 := by simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7469 p hg
    simpa only [d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7471 (p : Pattern) (guard : d2039 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7445 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7458 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7472 (p : Pattern) (guard : d2040 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7449 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7473 (p : Pattern) (guard : d2041 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7471 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7472 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7474 (p : Pattern) (guard : d2042 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7475 (p : Pattern) (guard : d2043 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7476 (p : Pattern) (guard : d2044 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7473 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7475 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7477 (p : Pattern) (guard : d2045 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7476 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7478 (p : Pattern) (guard : d2046 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7458 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7479 (p : Pattern) (guard : d2047 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7478 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7480 (p : Pattern) (guard : d2048 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7479 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7481 (p : Pattern) (guard : d2049 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7482 (p : Pattern) (guard : d2050 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7477 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7481 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7483 (p : Pattern) (guard : d2051 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7482 p hg
    simpa only [d2051, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d2051, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7484 (p : Pattern) (guard : d2052 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7464 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7483 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7485 (p : Pattern) (guard : d2053 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7484 p hg
    simpa only [d2053, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2053, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7486 (p : Pattern) (guard : d2054 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7485 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7487 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7486 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7488 (p : Pattern) (guard : d2056 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7487 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7489 (p : Pattern) (guard : d2057 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7469 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7488 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7490 (p : Pattern) (guard : d2149 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2148 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2057 p = 1 := by simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7489 p hg
    simpa only [d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7491 (p : Pattern) (guard : d2058 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7472 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7492 (p : Pattern) (guard : d2059 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7491 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7475 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7493 (p : Pattern) (guard : d2060 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7494 (p : Pattern) (guard : d2061 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7495 (p : Pattern) (guard : d2062 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7494 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7496 (p : Pattern) (guard : d2063 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d2063, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d2063, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7497 (p : Pattern) (guard : d2064 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7483 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7496 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7498 (p : Pattern) (guard : d2065 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d2065, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d2065, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7499 (p : Pattern) (guard : d2066 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7498 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
