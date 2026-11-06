/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons284
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39900 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35836 p hg
    simpa only [d8105, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39901 (p : Pattern) (guard : d8111 p = 1) : d2110 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2110, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39900 p hg
    simpa only [d8111, d2110, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2110, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d8111, d2110, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39902 (p : Pattern) (guard : d0 p = 1) : d2127 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39903 (p : Pattern) (guard : d8117 p = 1) : d2128 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2128, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39901 p hg
    simpa only [d8117, d2128, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2128, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39902 p hg
    simpa only [d8117, d2128, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39904 (p : Pattern) (guard : d0 p = 1) : d2133 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39905 (p : Pattern) (guard : d8123 p = 1) : d2134 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2134, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39903 p hg
    simpa only [d8123, d2134, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2134, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39904 p hg
    simpa only [d8123, d2134, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39906 (p : Pattern) (guard : d0 p = 1) : d2140 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39907 (p : Pattern) (guard : d8129 p = 1) : d2141 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2141, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39905 p hg
    simpa only [d8129, d2141, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2141, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39906 p hg
    simpa only [d8129, d2141, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39908 (p : Pattern) (guard : d0 p = 1) : d2146 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39909 (p : Pattern) (guard : d8135 p = 1) : d2147 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2147, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39907 p hg
    simpa only [d8135, d2147, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2147, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39908 p hg
    simpa only [d8135, d2147, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39910 (p : Pattern) (guard : d8136 p = 1) : d2148 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2148, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39899 p hg
    simpa only [d8136, d2148, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2148, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39909 p hg
    simpa only [d8136, d2148, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39911 (p : Pattern) (guard : d0 p = 1) : d1959 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39912 (p : Pattern) (guard : d8117 p = 1) : d2149 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2149, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39834 p hg
    simpa only [d8117, d2149, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2149, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39911 p hg
    simpa only [d8117, d2149, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39913 (p : Pattern) (guard : d0 p = 1) : d2150 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39914 (p : Pattern) (guard : d8123 p = 1) : d2151 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2151, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39912 p hg
    simpa only [d8123, d2151, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2151, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39913 p hg
    simpa only [d8123, d2151, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39915 (p : Pattern) (guard : d8129 p = 1) : d2152 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2152, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39914 p hg
    simpa only [d8129, d2152, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2152, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39387 p hg
    simpa only [d8129, d2152, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39916 (p : Pattern) (guard : d8135 p = 1) : d2153 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2153, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39915 p hg
    simpa only [d8135, d2153, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2153, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d8135, d2153, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39917 (p : Pattern) (guard : d0 p = 1) : d2165 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39918 (p : Pattern) (guard : d8141 p = 1) : d2166 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2166, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39916 p hg
    simpa only [d8141, d2166, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2166, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39917 p hg
    simpa only [d8141, d2166, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39919 (p : Pattern) (guard : d8142 p = 1) : d2167 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2167, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39910 p hg
    simpa only [d8142, d2167, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2167, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39918 p hg
    simpa only [d8142, d2167, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39920 (p : Pattern) (guard : d0 p = 1) : d1959 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39921 (p : Pattern) (guard : d8117 p = 1) : d2149 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2149, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39845 p hg
    simpa only [d8117, d2149, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2149, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39920 p hg
    simpa only [d8117, d2149, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39922 (p : Pattern) (guard : d0 p = 1) : d2168 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39923 (p : Pattern) (guard : d8123 p = 1) : d2169 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2169, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39921 p hg
    simpa only [d8123, d2169, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2169, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39922 p hg
    simpa only [d8123, d2169, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39924 (p : Pattern) (guard : d0 p = 1) : d2171 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39925 (p : Pattern) (guard : d8129 p = 1) : d2172 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2172, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39923 p hg
    simpa only [d8129, d2172, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2172, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39924 p hg
    simpa only [d8129, d2172, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39926 (p : Pattern) (guard : d0 p = 1) : d2175 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39927 (p : Pattern) (guard : d8135 p = 1) : d2176 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2176, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39925 p hg
    simpa only [d8135, d2176, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2176, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39926 p hg
    simpa only [d8135, d2176, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39928 (p : Pattern) (guard : d0 p = 1) : d2165 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39929 (p : Pattern) (guard : d8141 p = 1) : d2177 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2177, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39927 p hg
    simpa only [d8141, d2177, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2177, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39928 p hg
    simpa only [d8141, d2177, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39930 (p : Pattern) (guard : d8147 p = 1) : d2178 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d2178, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39929 p hg
    simpa only [d8147, d2178, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d2178, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d2178, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39931 (p : Pattern) (guard : d8148 p = 1) : d2179 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d2179, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39919 p hg
    simpa only [d8148, d2179, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d2179, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39930 p hg
    simpa only [d8148, d2179, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39932 (p : Pattern) (guard : d8149 p = 1) : d2180 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d2180, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39880 p hg
    simpa only [d8149, d2180, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d2180, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39931 p hg
    simpa only [d8149, d2180, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39933 (p : Pattern) (guard : d8150 p = 1) : d2181 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d2181, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39775 p hg
    simpa only [d8150, d2181, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d2181, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39932 p hg
    simpa only [d8150, d2181, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39934 (p : Pattern) (guard : d8151 p = 1) : d2182 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39604 p hg
    simpa only [d8151, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39933 p hg
    simpa only [d8151, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39935 (p : Pattern) (guard : d8152 p = 1) : d2183 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39408 p hg
    simpa only [d8152, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39934 p hg
    simpa only [d8152, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39936 (p : Pattern) (guard : d1 p = 1) : d318 p ≤ (0 : Int) + d318 p := by
  omega
theorem compare39937 (p : Pattern) (guard : d1 p = 1) : d2184 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34320 p hg
    simpa only [d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39938 (p : Pattern) (guard : d1 p = 1) : d2185 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2185, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39939 (p : Pattern) (guard : d1 p = 1) : d2186 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39940 (p : Pattern) (guard : d1 p = 1) : d2185 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2185, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39941 (p : Pattern) (guard : d8087 p = 1) : d2187 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d8087, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39942 (p : Pattern) (guard : d8088 p = 1) : d2188 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d8088, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d8088, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39943 (p : Pattern) (guard : d1 p = 1) : d330 p ≤ (0 : Int) + d330 p := by
  omega
theorem compare39944 (p : Pattern) (guard : d1 p = 1) : d2189 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34333 p hg
    simpa only [d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39943 p hg
    simpa only [d2189, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39945 (p : Pattern) (guard : d8085 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare39946 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34337 p hg
    simpa only [d8086, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39947 (p : Pattern) (guard : d8087 p = 1) : d2190 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39944 p hg
    simpa only [d8087, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d8087, d2190, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39948 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34335 p hg
    simpa only [d8086, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39949 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39948 p hg
    simpa only [d8091, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39950 (p : Pattern) (guard : d8092 p = 1) : d2191 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39947 p hg
    simpa only [d8092, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39949 p hg
    simpa only [d8092, d2191, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39951 (p : Pattern) (guard : d8093 p = 1) : d2192 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d8093, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39950 p hg
    simpa only [d8093, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39952 (p : Pattern) (guard : d1 p = 1) : d332 p ≤ (0 : Int) + d332 p := by
  omega
theorem compare39953 (p : Pattern) (guard : d1 p = 1) : d2193 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34349 p hg
    simpa only [d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39952 p hg
    simpa only [d2193, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39954 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8086, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39955 (p : Pattern) (guard : d8087 p = 1) : d2194 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39953 p hg
    simpa only [d8087, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39954 p hg
    simpa only [d8087, d2194, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39956 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d8091, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39957 (p : Pattern) (guard : d8092 p = 1) : d2195 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d8092, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39956 p hg
    simpa only [d8092, d2195, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39958 (p : Pattern) (guard : d8086 p = 1) : d2196 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34357 p hg
    simpa only [d8086, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2196, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39959 (p : Pattern) (guard : d8089 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare39960 (p : Pattern) (guard : d8090 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d8090, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39961 (p : Pattern) (guard : d8091 p = 1) : d2196 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39958 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39962 (p : Pattern) (guard : d8095 p = 1) : d2197 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d8095, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39963 (p : Pattern) (guard : d8096 p = 1) : d2198 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39961 p hg
    simpa only [d8096, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d8096, d2198, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39964 (p : Pattern) (guard : d8097 p = 1) : d2199 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39957 p hg
    simpa only [d8097, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39963 p hg
    simpa only [d8097, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39965 (p : Pattern) (guard : d8098 p = 1) : d2200 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39951 p hg
    simpa only [d8098, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39964 p hg
    simpa only [d8098, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39966 (p : Pattern) (guard : d1 p = 1) : d2185 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34373 p hg
    simpa only [d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2185, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39967 (p : Pattern) (guard : d8087 p = 1) : d2185 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39966 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39954 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39968 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39954 p hg
    simpa only [d8091, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39969 (p : Pattern) (guard : d8092 p = 1) : d2201 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39967 p hg
    simpa only [d8092, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d8092, d2201, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39970 (p : Pattern) (guard : d8086 p = 1) : d2196 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34381 p hg
    simpa only [d8086, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2196, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39971 (p : Pattern) (guard : d8091 p = 1) : d2196 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39970 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39972 (p : Pattern) (guard : d8096 p = 1) : d2198 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39971 p hg
    simpa only [d8096, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d8096, d2198, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39973 (p : Pattern) (guard : d8097 p = 1) : d2202 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39969 p hg
    simpa only [d8097, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39972 p hg
    simpa only [d8097, d2202, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39974 (p : Pattern) (guard : d8086 p = 1) : d2203 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34387 p hg
    simpa only [d8086, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39975 (p : Pattern) (guard : d8090 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34390 p hg
    simpa only [d8090, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39976 (p : Pattern) (guard : d8091 p = 1) : d2203 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39974 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39975 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39977 (p : Pattern) (guard : d8095 p = 1) : d2204 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39975 p hg
    simpa only [d8095, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39978 (p : Pattern) (guard : d8096 p = 1) : d2205 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39976 p hg
    simpa only [d8096, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39977 p hg
    simpa only [d8096, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39979 (p : Pattern) (guard : d8102 p = 1) : d2206 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39978 p hg
    simpa only [d8102, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39980 (p : Pattern) (guard : d8103 p = 1) : d2207 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39973 p hg
    simpa only [d8103, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39979 p hg
    simpa only [d8103, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39981 (p : Pattern) (guard : d8104 p = 1) : d2208 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39965 p hg
    simpa only [d8104, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39980 p hg
    simpa only [d8104, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39982 (p : Pattern) (guard : d1 p = 1) : d2185 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34404 p hg
    simpa only [d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d2185, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39983 (p : Pattern) (guard : d8087 p = 1) : d2185 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39982 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39954 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39984 (p : Pattern) (guard : d8086 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8086, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39985 (p : Pattern) (guard : d8091 p = 1) : d2210 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39984 p hg
    simpa only [d8091, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39986 (p : Pattern) (guard : d8092 p = 1) : d2211 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39983 p hg
    simpa only [d8092, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39985 p hg
    simpa only [d8092, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39987 (p : Pattern) (guard : d8086 p = 1) : d2185 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34414 p hg
    simpa only [d8086, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39988 (p : Pattern) (guard : d8090 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8090, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39989 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39987 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39990 (p : Pattern) (guard : d8090 p = 1) : d2212 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34422 p hg
    simpa only [d8090, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39991 (p : Pattern) (guard : d8095 p = 1) : d2213 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39990 p hg
    simpa only [d8095, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39992 (p : Pattern) (guard : d8096 p = 1) : d2214 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39989 p hg
    simpa only [d8096, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39991 p hg
    simpa only [d8096, d2214, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39993 (p : Pattern) (guard : d8097 p = 1) : d2215 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39986 p hg
    simpa only [d8097, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39992 p hg
    simpa only [d8097, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39994 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39948 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39995 (p : Pattern) (guard : d8090 p = 1) : d2216 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34433 p hg
    simpa only [d8090, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39996 (p : Pattern) (guard : d8095 p = 1) : d2217 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39995 p hg
    simpa only [d8095, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39997 (p : Pattern) (guard : d8096 p = 1) : d2218 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39994 p hg
    simpa only [d8096, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39996 p hg
    simpa only [d8096, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39998 (p : Pattern) (guard : d5854 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare39999 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8094, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40000 (p : Pattern) (guard : d8095 p = 1) : d2196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40001 (p : Pattern) (guard : d8101 p = 1) : d2219 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40000 p hg
    simpa only [d8101, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40002 (p : Pattern) (guard : d8102 p = 1) : d2220 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39997 p hg
    simpa only [d8102, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40001 p hg
    simpa only [d8102, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40003 (p : Pattern) (guard : d8103 p = 1) : d2221 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39993 p hg
    simpa only [d8103, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40002 p hg
    simpa only [d8103, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40004 (p : Pattern) (guard : d8091 p = 1) : d2185 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39988 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40005 (p : Pattern) (guard : d8096 p = 1) : d2222 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40004 p hg
    simpa only [d8096, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40006 (p : Pattern) (guard : d8102 p = 1) : d2223 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40005 p hg
    simpa only [d8102, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40001 p hg
    simpa only [d8102, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40007 (p : Pattern) (guard : d8094 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d8094, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40008 (p : Pattern) (guard : d8095 p = 1) : d2203 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39975 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40009 (p : Pattern) (guard : d8101 p = 1) : d2224 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40008 p hg
    simpa only [d8101, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40010 (p : Pattern) (guard : d8107 p = 1) : d2225 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40009 p hg
    simpa only [d8107, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40011 (p : Pattern) (guard : d8108 p = 1) : d2226 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40006 p hg
    simpa only [d8108, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40010 p hg
    simpa only [d8108, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40012 (p : Pattern) (guard : d8109 p = 1) : d2227 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40003 p hg
    simpa only [d8109, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40011 p hg
    simpa only [d8109, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40013 (p : Pattern) (guard : d8110 p = 1) : d2228 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39981 p hg
    simpa only [d8110, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40012 p hg
    simpa only [d8110, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40014 (p : Pattern) (guard : d1 p = 1) : d357 p ≤ (0 : Int) + d357 p := by
  omega
theorem compare40015 (p : Pattern) (guard : d1 p = 1) : d2229 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34462 p hg
    simpa only [d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40014 p hg
    simpa only [d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40016 (p : Pattern) (guard : d8087 p = 1) : d2230 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40015 p hg
    simpa only [d8087, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39948 p hg
    simpa only [d8087, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40017 (p : Pattern) (guard : d8091 p = 1) : d2187 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39987 p hg
    simpa only [d8091, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40018 (p : Pattern) (guard : d8092 p = 1) : d2231 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40016 p hg
    simpa only [d8092, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40017 p hg
    simpa only [d8092, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40019 (p : Pattern) (guard : d8086 p = 1) : d2209 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34469 p hg
    simpa only [d8086, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40020 (p : Pattern) (guard : d8090 p = 1) : d2209 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8090, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40021 (p : Pattern) (guard : d8091 p = 1) : d2209 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40019 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40022 (p : Pattern) (guard : d8095 p = 1) : d2210 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d8095, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40023 (p : Pattern) (guard : d8096 p = 1) : d2232 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40021 p hg
    simpa only [d8096, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d8096, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40024 (p : Pattern) (guard : d8097 p = 1) : d2233 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40018 p hg
    simpa only [d8097, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40023 p hg
    simpa only [d8097, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40025 (p : Pattern) (guard : d8086 p = 1) : d2196 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34481 p hg
    simpa only [d8086, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39945 p hg
    simpa only [d8086, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40026 (p : Pattern) (guard : d8091 p = 1) : d2196 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40025 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39960 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40027 (p : Pattern) (guard : d8096 p = 1) : d2198 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d8096, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39962 p hg
    simpa only [d8096, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40028 (p : Pattern) (guard : d8090 p = 1) : d2203 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34485 p hg
    simpa only [d8090, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40029 (p : Pattern) (guard : d8095 p = 1) : d2203 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40028 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40030 (p : Pattern) (guard : d8100 p = 1) : d2204 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d8100, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40031 (p : Pattern) (guard : d8101 p = 1) : d2205 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40029 p hg
    simpa only [d8101, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40030 p hg
    simpa only [d8101, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40032 (p : Pattern) (guard : d8102 p = 1) : d2234 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40027 p hg
    simpa only [d8102, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40031 p hg
    simpa only [d8102, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40033 (p : Pattern) (guard : d8103 p = 1) : d2235 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d8103, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40032 p hg
    simpa only [d8103, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40034 (p : Pattern) (guard : d8090 p = 1) : d2236 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34496 p hg
    simpa only [d8090, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40035 (p : Pattern) (guard : d8094 p = 1) : d2236 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34499 p hg
    simpa only [d8094, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40036 (p : Pattern) (guard : d8095 p = 1) : d2236 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40034 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40035 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40037 (p : Pattern) (guard : d8100 p = 1) : d2237 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40035 p hg
    simpa only [d8100, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40038 (p : Pattern) (guard : d8101 p = 1) : d2238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40036 p hg
    simpa only [d8101, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40037 p hg
    simpa only [d8101, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40039 (p : Pattern) (guard : d8102 p = 1) : d2239 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39963 p hg
    simpa only [d8102, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40038 p hg
    simpa only [d8102, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
