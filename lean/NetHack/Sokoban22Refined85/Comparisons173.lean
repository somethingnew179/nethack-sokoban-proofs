/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24220 (p : Pattern) (guard : d4474 p = 1) : d3169 p ≤ (0 : Int) + d2118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3169, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24219 p hg
    simpa only [d3169, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3169, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24195 p hg
    simpa only [d3169, d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24221 (p : Pattern) (guard : d4474 p = 1) : d3170 p ≤ (0 : Int) + d2119 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3170, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24090 p hg
    simpa only [d3170, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3170, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3170, d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24222 (p : Pattern) (guard : d4474 p = 1) : d3171 p ≤ (0 : Int) + d2120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3171, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24221 p hg
    simpa only [d3171, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3171, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3171, d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24223 (p : Pattern) (guard : d4474 p = 1) : d3172 p ≤ (0 : Int) + d2121 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3172, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24222 p hg
    simpa only [d3172, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3172, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3172, d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24224 (p : Pattern) (guard : d4474 p = 1) : d3173 p ≤ (0 : Int) + d2122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3173, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24220 p hg
    simpa only [d3173, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3173, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24223 p hg
    simpa only [d3173, d2122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24225 (p : Pattern) (guard : d4474 p = 1) : d3174 p ≤ (0 : Int) + d2123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3174, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24217 p hg
    simpa only [d3174, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3174, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24224 p hg
    simpa only [d3174, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24226 (p : Pattern) (guard : d0 p = 1) : d3176 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24227 (p : Pattern) (guard : d4474 p = 1) : d3177 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3177, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d3177, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3177, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24226 p hg
    simpa only [d4474, d3177, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24228 (p : Pattern) (guard : d4474 p = 1) : d3178 p ≤ (0 : Int) + d2127 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3178, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24227 p hg
    simpa only [d3178, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3178, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16693 p hg
    simpa only [d3178, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24229 (p : Pattern) (guard : d4474 p = 1) : d3179 p ≤ (0 : Int) + d2128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3179, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24212 p hg
    simpa only [d3179, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3179, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24228 p hg
    simpa only [d3179, d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24230 (p : Pattern) (guard : d0 p = 1) : d2136 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24231 (p : Pattern) (guard : d4474 p = 1) : d3180 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d3180, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d3180, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d3180, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24230 p hg
    simpa only [d4474, d3180, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24232 (p : Pattern) (guard : d4474 p = 1) : d3181 p ≤ (0 : Int) + d2132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3181, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24231 p hg
    simpa only [d3181, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3181, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16697 p hg
    simpa only [d3181, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24233 (p : Pattern) (guard : d4474 p = 1) : d3182 p ≤ (0 : Int) + d2133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3182, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24232 p hg
    simpa only [d3182, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3182, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3182, d2133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24234 (p : Pattern) (guard : d4474 p = 1) : d3183 p ≤ (0 : Int) + d2134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3183, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24229 p hg
    simpa only [d3183, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3183, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24233 p hg
    simpa only [d3183, d2134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24235 (p : Pattern) (guard : d4474 p = 1) : d3184 p ≤ (0 : Int) + d2138 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3184, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24044 p hg
    simpa only [d3184, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3184, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16701 p hg
    simpa only [d3184, d2138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24236 (p : Pattern) (guard : d4474 p = 1) : d3185 p ≤ (0 : Int) + d2139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3185, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24235 p hg
    simpa only [d3185, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3185, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3185, d2139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24237 (p : Pattern) (guard : d4474 p = 1) : d3186 p ≤ (0 : Int) + d2140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3186, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24236 p hg
    simpa only [d3186, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3186, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3186, d2140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24238 (p : Pattern) (guard : d4474 p = 1) : d3187 p ≤ (0 : Int) + d2141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3187, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24234 p hg
    simpa only [d3187, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3187, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24237 p hg
    simpa only [d3187, d2141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24239 (p : Pattern) (guard : d4474 p = 1) : d3188 p ≤ (0 : Int) + d2142 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3188, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24044 p hg
    simpa only [d3188, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3188, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d3188, d2142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24240 (p : Pattern) (guard : d4474 p = 1) : d3189 p ≤ (0 : Int) + d2143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3189, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24239 p hg
    simpa only [d3189, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3189, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24045 p hg
    simpa only [d3189, d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24241 (p : Pattern) (guard : d4474 p = 1) : d3190 p ≤ (0 : Int) + d2144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3190, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24240 p hg
    simpa only [d3190, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3190, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24222 p hg
    simpa only [d3190, d2144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24242 (p : Pattern) (guard : d4474 p = 1) : d3191 p ≤ (0 : Int) + d2145 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3191, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23905 p hg
    simpa only [d3191, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3191, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3191, d2145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24243 (p : Pattern) (guard : d4474 p = 1) : d3192 p ≤ (0 : Int) + d2146 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3192, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24241 p hg
    simpa only [d3192, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3192, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24242 p hg
    simpa only [d3192, d2146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24244 (p : Pattern) (guard : d4474 p = 1) : d3193 p ≤ (0 : Int) + d2147 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3193, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24238 p hg
    simpa only [d3193, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3193, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24243 p hg
    simpa only [d3193, d2147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24245 (p : Pattern) (guard : d4474 p = 1) : d3194 p ≤ (0 : Int) + d2148 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3194, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24225 p hg
    simpa only [d3194, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3194, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24244 p hg
    simpa only [d3194, d2148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24246 (p : Pattern) (guard : d4474 p = 1) : d3195 p ≤ (0 : Int) + d2149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3195, d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24080 p hg
    simpa only [d3195, d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3195, d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24082 p hg
    simpa only [d3195, d2149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24247 (p : Pattern) (guard : d4474 p = 1) : d3196 p ≤ (0 : Int) + d2150 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3196, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3196, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3196, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d3196, d2150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24248 (p : Pattern) (guard : d4474 p = 1) : d3197 p ≤ (0 : Int) + d2151 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3197, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24246 p hg
    simpa only [d3197, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3197, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24247 p hg
    simpa only [d3197, d2151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24249 (p : Pattern) (guard : d4474 p = 1) : d3198 p ≤ (0 : Int) + d2152 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3198, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24248 p hg
    simpa only [d3198, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3198, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24100 p hg
    simpa only [d3198, d2152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24250 (p : Pattern) (guard : d4474 p = 1) : d3199 p ≤ (0 : Int) + d2153 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3199, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24249 p hg
    simpa only [d3199, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3199, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24104 p hg
    simpa only [d3199, d2153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24251 (p : Pattern) (guard : d4474 p = 1) : d3200 p ≤ (0 : Int) + d2159 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3200, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24065 p hg
    simpa only [d3200, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3200, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16718 p hg
    simpa only [d3200, d2159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24252 (p : Pattern) (guard : d4474 p = 1) : d3201 p ≤ (0 : Int) + d2160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3201, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24251 p hg
    simpa only [d3201, d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3201, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3201, d2160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24253 (p : Pattern) (guard : d4474 p = 1) : d3202 p ≤ (0 : Int) + d2161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3202, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24252 p hg
    simpa only [d3202, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3202, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24201 p hg
    simpa only [d3202, d2161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24254 (p : Pattern) (guard : d4474 p = 1) : d3203 p ≤ (0 : Int) + d2162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3203, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24253 p hg
    simpa only [d3203, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3203, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24103 p hg
    simpa only [d3203, d2162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24255 (p : Pattern) (guard : d4474 p = 1) : d3204 p ≤ (0 : Int) + d2163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3204, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23954 p hg
    simpa only [d3204, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3204, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3204, d2163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24256 (p : Pattern) (guard : d4474 p = 1) : d3205 p ≤ (0 : Int) + d2164 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3205, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24255 p hg
    simpa only [d3205, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3205, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3205, d2164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24257 (p : Pattern) (guard : d4474 p = 1) : d3206 p ≤ (0 : Int) + d2165 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3206, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24254 p hg
    simpa only [d3206, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3206, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24256 p hg
    simpa only [d3206, d2165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24258 (p : Pattern) (guard : d4474 p = 1) : d3207 p ≤ (0 : Int) + d2166 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3207, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24250 p hg
    simpa only [d3207, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3207, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24257 p hg
    simpa only [d3207, d2166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24259 (p : Pattern) (guard : d4474 p = 1) : d3208 p ≤ (0 : Int) + d2167 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3208, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24245 p hg
    simpa only [d3208, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3208, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24258 p hg
    simpa only [d3208, d2167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24260 (p : Pattern) (guard : d4474 p = 1) : d3209 p ≤ (0 : Int) + d2168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3209, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24088 p hg
    simpa only [d3209, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3209, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d3209, d2168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24261 (p : Pattern) (guard : d4474 p = 1) : d3210 p ≤ (0 : Int) + d2169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3210, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24246 p hg
    simpa only [d3210, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3210, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24260 p hg
    simpa only [d3210, d2169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24262 (p : Pattern) (guard : d4474 p = 1) : d3211 p ≤ (0 : Int) + d2170 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3211, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24083 p hg
    simpa only [d3211, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3211, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23953 p hg
    simpa only [d3211, d2170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24263 (p : Pattern) (guard : d4474 p = 1) : d3212 p ≤ (0 : Int) + d2171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3212, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24262 p hg
    simpa only [d3212, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3212, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3212, d2171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24264 (p : Pattern) (guard : d4474 p = 1) : d3213 p ≤ (0 : Int) + d2172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3213, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24261 p hg
    simpa only [d3213, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3213, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24263 p hg
    simpa only [d3213, d2172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24265 (p : Pattern) (guard : d4474 p = 1) : d3214 p ≤ (0 : Int) + d2173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3214, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24091 p hg
    simpa only [d3214, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3214, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d3214, d2173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24266 (p : Pattern) (guard : d4474 p = 1) : d3215 p ≤ (0 : Int) + d2174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3215, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24265 p hg
    simpa only [d3215, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3215, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3215, d2174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24267 (p : Pattern) (guard : d4474 p = 1) : d3216 p ≤ (0 : Int) + d2175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3216, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24266 p hg
    simpa only [d3216, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3216, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3216, d2175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24268 (p : Pattern) (guard : d4474 p = 1) : d3217 p ≤ (0 : Int) + d2176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3217, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24264 p hg
    simpa only [d3217, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3217, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24267 p hg
    simpa only [d3217, d2176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24269 (p : Pattern) (guard : d4474 p = 1) : d3218 p ≤ (0 : Int) + d2177 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3218, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24268 p hg
    simpa only [d3218, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3218, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24257 p hg
    simpa only [d3218, d2177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24270 (p : Pattern) (guard : d4474 p = 1) : d3219 p ≤ (0 : Int) + d2178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3219, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24269 p hg
    simpa only [d3219, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3219, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d3219, d2178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24271 (p : Pattern) (guard : d4474 p = 1) : d3220 p ≤ (0 : Int) + d2179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3220, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24259 p hg
    simpa only [d3220, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3220, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24270 p hg
    simpa only [d3220, d2179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24272 (p : Pattern) (guard : d4474 p = 1) : d3221 p ≤ (0 : Int) + d2180 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3221, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24209 p hg
    simpa only [d3221, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3221, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24271 p hg
    simpa only [d3221, d2180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24273 (p : Pattern) (guard : d4474 p = 1) : d3222 p ≤ (0 : Int) + d2181 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3222, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23999 p hg
    simpa only [d3222, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3222, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24272 p hg
    simpa only [d3222, d2181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24274 (p : Pattern) (guard : d4474 p = 1) : d3223 p ≤ (0 : Int) + d2182 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3223, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24190 p hg
    simpa only [d3223, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3223, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24273 p hg
    simpa only [d3223, d2182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24275 (p : Pattern) (guard : d4474 p = 1) : d3224 p ≤ (0 : Int) + d2183 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3224, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24127 p hg
    simpa only [d3224, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3224, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24274 p hg
    simpa only [d3224, d2183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24276 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24277 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d1683 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1769, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d1769, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24278 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d1684 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24277 p hg
    simpa only [d1770, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d1770, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24279 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (2 : Int) + d1685 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d1771, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24278 p hg
    simpa only [d1771, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24280 (p : Pattern) (guard : d1 p = 1) : d1772 p ≤ (2 : Int) + d1686 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1772, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24279 p hg
    simpa only [d1772, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1772, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24278 p hg
    simpa only [d1772, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24281 (p : Pattern) (guard : d4473 p = 1) : d2895 p ≤ (2 : Int) + d1686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24276 p hg
    simpa only [d4473, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24280 p hg
    simpa only [d4473, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24282 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (2 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24283 (p : Pattern) (guard : d4985 p = 1) : d2896 p ≤ (2 : Int) + d1686 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24281 p hg
    simpa only [d4985, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24282 p hg
    simpa only [d4985, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24284 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d1696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24285 (p : Pattern) (guard : d1 p = 1) : d1794 p ≤ (2 : Int) + d1693 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1794, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d1794, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24286 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (2 : Int) + d1694 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1795, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24285 p hg
    simpa only [d1795, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1795, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d1795, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24287 (p : Pattern) (guard : d1 p = 1) : d2011 p ≤ (2 : Int) + d1695 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2011, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d2011, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2011, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24286 p hg
    simpa only [d2011, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24288 (p : Pattern) (guard : d1 p = 1) : d2012 p ≤ (2 : Int) + d1696 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2012, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24287 p hg
    simpa only [d2012, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2012, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24286 p hg
    simpa only [d2012, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24289 (p : Pattern) (guard : d4473 p = 1) : d2897 p ≤ (2 : Int) + d1696 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24284 p hg
    simpa only [d4473, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24288 p hg
    simpa only [d4473, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24290 (p : Pattern) (guard : d0 p = 1) : d1697 p ≤ (2 : Int) + d1696 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24291 (p : Pattern) (guard : d4985 p = 1) : d2898 p ≤ (2 : Int) + d1696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24289 p hg
    simpa only [d4985, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24290 p hg
    simpa only [d4985, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24292 (p : Pattern) (guard : d4985 p = 1) : d2899 p ≤ (2 : Int) + d5856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2899, d5856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24283 p hg
    simpa only [d2899, d5856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2899, d5856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24291 p hg
    simpa only [d2899, d5856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24293 (p : Pattern) (guard : d4985 p = 1) : d2900 p ≤ (2 : Int) + d5857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2900, d5857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24283 p hg
    simpa only [d2900, d5857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2900, d5857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24292 p hg
    simpa only [d2900, d5857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24294 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (2 : Int) + d1704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24295 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d1701 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d23, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24296 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (2 : Int) + d1702 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24295 p hg
    simpa only [d356, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d356, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24297 (p : Pattern) (guard : d1 p = 1) : d1802 p ≤ (2 : Int) + d1703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1802, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d1802, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1802, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24296 p hg
    simpa only [d1802, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24298 (p : Pattern) (guard : d1 p = 1) : d1803 p ≤ (2 : Int) + d1704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1803, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24297 p hg
    simpa only [d1803, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1803, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24296 p hg
    simpa only [d1803, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24299 (p : Pattern) (guard : d4473 p = 1) : d2901 p ≤ (2 : Int) + d1704 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24294 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24298 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24300 (p : Pattern) (guard : d0 p = 1) : d1705 p ≤ (2 : Int) + d1704 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24301 (p : Pattern) (guard : d4985 p = 1) : d2902 p ≤ (2 : Int) + d1704 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24299 p hg
    simpa only [d4985, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24300 p hg
    simpa only [d4985, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24302 (p : Pattern) (guard : d4985 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare24303 (p : Pattern) (guard : d4985 p = 1) : d2903 p ≤ (2 : Int) + d5858 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2903, d5858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24301 p hg
    simpa only [d2903, d5858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2903, d5858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2903, d5858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24304 (p : Pattern) (guard : d4985 p = 1) : d2904 p ≤ (2 : Int) + d5859 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2904, d5859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24292 p hg
    simpa only [d2904, d5859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2904, d5859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24303 p hg
    simpa only [d2904, d5859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24305 (p : Pattern) (guard : d4985 p = 1) : d2905 p ≤ (2 : Int) + d5860 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2905, d5860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24293 p hg
    simpa only [d2905, d5860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2905, d5860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24304 p hg
    simpa only [d2905, d5860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24306 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24307 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d1710 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d1775, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16115 p hg
    simpa only [d1775, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24308 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d1711 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24307 p hg
    simpa only [d1776, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16117 p hg
    simpa only [d1776, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24309 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d1712 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d1777, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24308 p hg
    simpa only [d1777, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24310 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d1713 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d1769, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d1769, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24311 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24310 p hg
    simpa only [d1770, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15765 p hg
    simpa only [d1770, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24312 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d1785, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1785, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24313 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d1715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24312 p hg
    simpa only [d1786, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15786 p hg
    simpa only [d1786, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24314 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d1716 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24311 p hg
    simpa only [d1787, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24313 p hg
    simpa only [d1787, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24315 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24309 p hg
    simpa only [d1788, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24314 p hg
    simpa only [d1788, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24316 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24306 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24315 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24317 (p : Pattern) (guard : d0 p = 1) : d1718 p ≤ (2 : Int) + d1717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24318 (p : Pattern) (guard : d4985 p = 1) : d2907 p ≤ (2 : Int) + d1717 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24316 p hg
    simpa only [d4985, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24317 p hg
    simpa only [d4985, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24319 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24320 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1775, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1775, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24321 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24320 p hg
    simpa only [d1776, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1776, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24322 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d1720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15757 p hg
    simpa only [d1777, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24321 p hg
    simpa only [d1777, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24323 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1769, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d1769, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24324 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24323 p hg
    simpa only [d1770, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d1770, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24325 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1785, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1785, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24326 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24325 p hg
    simpa only [d1786, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1786, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24327 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d1723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24324 p hg
    simpa only [d1787, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24326 p hg
    simpa only [d1787, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24328 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24322 p hg
    simpa only [d1788, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24327 p hg
    simpa only [d1788, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24329 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24319 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24328 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24330 (p : Pattern) (guard : d0 p = 1) : d1725 p ≤ (2 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24331 (p : Pattern) (guard : d4985 p = 1) : d2908 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24329 p hg
    simpa only [d4985, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24330 p hg
    simpa only [d4985, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24332 (p : Pattern) (guard : d4985 p = 1) : d2909 p ≤ (2 : Int) + d5861 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2909, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24318 p hg
    simpa only [d2909, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2909, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24331 p hg
    simpa only [d2909, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24333 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24334 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1775, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1775, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24335 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24334 p hg
    simpa only [d1776, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1776, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24336 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d1728 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15778 p hg
    simpa only [d1777, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24335 p hg
    simpa only [d1777, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24337 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1769, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1769, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24338 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24337 p hg
    simpa only [d1770, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d1770, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24339 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1785, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1785, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24340 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24339 p hg
    simpa only [d1786, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1786, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24341 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d327 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24338 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24340 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24342 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24336 p hg
    simpa only [d1788, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24341 p hg
    simpa only [d1788, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24343 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24333 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24342 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24344 (p : Pattern) (guard : d0 p = 1) : d1730 p ≤ (2 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24345 (p : Pattern) (guard : d4985 p = 1) : d2910 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24343 p hg
    simpa only [d4985, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24344 p hg
    simpa only [d4985, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24346 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24347 (p : Pattern) (guard : d4473 p = 1) : d2911 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24346 p hg
    simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15800 p hg
    simpa only [d4473, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24348 (p : Pattern) (guard : d4985 p = 1) : d2912 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24347 p hg
    simpa only [d4985, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24349 (p : Pattern) (guard : d4985 p = 1) : d2913 p ≤ (2 : Int) + d5862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2913, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24345 p hg
    simpa only [d2913, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2913, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d2913, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24350 (p : Pattern) (guard : d4985 p = 1) : d2914 p ≤ (2 : Int) + d5863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2914, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24332 p hg
    simpa only [d2914, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2914, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24349 p hg
    simpa only [d2914, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24351 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24352 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24351 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15817 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24353 (p : Pattern) (guard : d4985 p = 1) : d2915 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24352 p hg
    simpa only [d4985, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24354 (p : Pattern) (guard : d4985 p = 1) : d2916 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24353 p hg
    simpa only [d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24355 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24356 (p : Pattern) (guard : d4473 p = 1) : d2901 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24355 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15824 p hg
    simpa only [d4473, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24357 (p : Pattern) (guard : d4985 p = 1) : d2917 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24356 p hg
    simpa only [d4985, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24358 (p : Pattern) (guard : d4985 p = 1) : d2918 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24357 p hg
    simpa only [d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24359 (p : Pattern) (guard : d4985 p = 1) : d2919 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24354 p hg
    simpa only [d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24358 p hg
    simpa only [d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
