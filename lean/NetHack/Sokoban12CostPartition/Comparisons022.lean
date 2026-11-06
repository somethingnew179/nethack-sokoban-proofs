/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3080 (p : Pattern) (guard : d986 p = 1) : d248 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3079 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3081 (p : Pattern) (guard : d770 p = 1) : d145 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3082 (p : Pattern) (guard : d770 p = 1) : d147 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3081 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3083 (p : Pattern) (guard : d770 p = 1) : d249 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3082 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3084 (p : Pattern) (guard : d986 p = 1) : d250 p ≤ (0 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d986, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3085 (p : Pattern) (guard : d986 p = 1) : d251 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3084 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3086 (p : Pattern) (guard : d986 p = 1) : d252 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3080 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3085 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3087 (p : Pattern) (guard : d770 p = 1) : d253 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3088 (p : Pattern) (guard : d986 p = 1) : d254 p ≤ (0 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3087 p hg
    simpa only [d986, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3089 (p : Pattern) (guard : d986 p = 1) : d255 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3088 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3090 (p : Pattern) (guard : d986 p = 1) : d256 p ≤ (0 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3091 (p : Pattern) (guard : d986 p = 1) : d257 p ≤ (0 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3086 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3090 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3092 (p : Pattern) (guard : d986 p = 1) : d258 p ≤ (0 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3073 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3091 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3093 (p : Pattern) (guard : d1133 p = 1) : d258 p ≤ (0 : Int) + d258 p := by
  omega
theorem compare3094 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3095 (p : Pattern) (guard : d770 p = 1) : d21 p ≤ (0 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3094 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3096 (p : Pattern) (guard : d0 p = 1) : d261 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3097 (p : Pattern) (guard : d770 p = 1) : d375 p ≤ (0 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3098 (p : Pattern) (guard : d770 p = 1) : d376 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3097 p hg
    simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3099 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3100 (p : Pattern) (guard : d770 p = 1) : d22 p ≤ (0 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3101 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3102 (p : Pattern) (guard : d770 p = 1) : d377 p ≤ (0 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3103 (p : Pattern) (guard : d770 p = 1) : d378 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3102 p hg
    simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3104 (p : Pattern) (guard : d770 p = 1) : d379 p ≤ (0 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3105 (p : Pattern) (guard : d0 p = 1) : d260 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3106 (p : Pattern) (guard : d770 p = 1) : d380 p ≤ (0 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3107 (p : Pattern) (guard : d770 p = 1) : d381 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3108 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3109 (p : Pattern) (guard : d770 p = 1) : d382 p ≤ (0 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3108 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3110 (p : Pattern) (guard : d770 p = 1) : d383 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3109 p hg
    simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3111 (p : Pattern) (guard : d770 p = 1) : d384 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3110 p hg
    simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3112 (p : Pattern) (guard : d770 p = 1) : d385 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3111 p hg
    simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3113 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3114 (p : Pattern) (guard : d770 p = 1) : d386 p ≤ (0 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3115 (p : Pattern) (guard : d770 p = 1) : d387 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3116 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3117 (p : Pattern) (guard : d770 p = 1) : d388 p ≤ (0 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3118 (p : Pattern) (guard : d770 p = 1) : d389 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3117 p hg
    simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3119 (p : Pattern) (guard : d770 p = 1) : d390 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3118 p hg
    simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3120 (p : Pattern) (guard : d770 p = 1) : d391 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3121 (p : Pattern) (guard : d770 p = 1) : d392 p ≤ (0 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3120 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3122 (p : Pattern) (guard : d770 p = 1) : d393 p ≤ (0 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3121 p hg
    simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3123 (p : Pattern) (guard : d770 p = 1) : d394 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3124 (p : Pattern) (guard : d770 p = 1) : d395 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3125 (p : Pattern) (guard : d770 p = 1) : d396 p ≤ (0 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3124 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3126 (p : Pattern) (guard : d770 p = 1) : d397 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3111 p hg
    simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3127 (p : Pattern) (guard : d770 p = 1) : d398 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3128 (p : Pattern) (guard : d770 p = 1) : d399 p ≤ (0 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3127 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3129 (p : Pattern) (guard : d770 p = 1) : d400 p ≤ (0 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3125 p hg
    simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3128 p hg
    simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3130 (p : Pattern) (guard : d770 p = 1) : d401 p ≤ (0 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3122 p hg
    simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3131 (p : Pattern) (guard : d770 p = 1) : d402 p ≤ (0 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3132 (p : Pattern) (guard : d770 p = 1) : d403 p ≤ (0 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3133 (p : Pattern) (guard : d770 p = 1) : d404 p ≤ (0 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3130 p hg
    simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3132 p hg
    simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3134 (p : Pattern) (guard : d0 p = 1) : d290 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3135 (p : Pattern) (guard : d770 p = 1) : d405 p ≤ (0 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3134 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3136 (p : Pattern) (guard : d770 p = 1) : d406 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3109 p hg
    simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3135 p hg
    simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3137 (p : Pattern) (guard : d770 p = 1) : d407 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3136 p hg
    simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3138 (p : Pattern) (guard : d770 p = 1) : d408 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3139 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3140 (p : Pattern) (guard : d770 p = 1) : d409 p ≤ (0 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3139 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3141 (p : Pattern) (guard : d770 p = 1) : d410 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3117 p hg
    simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3142 (p : Pattern) (guard : d770 p = 1) : d411 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3141 p hg
    simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3143 (p : Pattern) (guard : d770 p = 1) : d412 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3144 (p : Pattern) (guard : d770 p = 1) : d413 p ≤ (0 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3143 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3145 (p : Pattern) (guard : d770 p = 1) : d414 p ≤ (0 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3144 p hg
    simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3146 (p : Pattern) (guard : d770 p = 1) : d415 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3135 p hg
    simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3147 (p : Pattern) (guard : d770 p = 1) : d416 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3146 p hg
    simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3136 p hg
    simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3148 (p : Pattern) (guard : d770 p = 1) : d417 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3147 p hg
    simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3149 (p : Pattern) (guard : d770 p = 1) : d418 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3150 (p : Pattern) (guard : d770 p = 1) : d419 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3141 p hg
    simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3151 (p : Pattern) (guard : d770 p = 1) : d420 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3150 p hg
    simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3152 (p : Pattern) (guard : d770 p = 1) : d421 p ≤ (0 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3153 (p : Pattern) (guard : d770 p = 1) : d422 p ≤ (0 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3152 p hg
    simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3154 (p : Pattern) (guard : d770 p = 1) : d423 p ≤ (0 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3145 p hg
    simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3155 (p : Pattern) (guard : d770 p = 1) : d424 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3156 (p : Pattern) (guard : d770 p = 1) : d425 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3157 (p : Pattern) (guard : d770 p = 1) : d426 p ≤ (0 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3156 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3158 (p : Pattern) (guard : d770 p = 1) : d427 p ≤ (0 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3159 (p : Pattern) (guard : d770 p = 1) : d428 p ≤ (0 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3158 p hg
    simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3160 (p : Pattern) (guard : d770 p = 1) : d429 p ≤ (0 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3154 p hg
    simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3161 (p : Pattern) (guard : d770 p = 1) : d430 p ≤ (0 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3133 p hg
    simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3160 p hg
    simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3162 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (1 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3163 (p : Pattern) (guard : d770 p = 1) : d21 p ≤ (1 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3162 p hg
    simpa only [d770, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3164 (p : Pattern) (guard : d0 p = 1) : d261 p ≤ (1 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3165 (p : Pattern) (guard : d770 p = 1) : d375 p ≤ (1 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3164 p hg
    simpa only [d770, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3166 (p : Pattern) (guard : d770 p = 1) : d376 p ≤ (1 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3165 p hg
    simpa only [d376, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3167 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (1 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3168 (p : Pattern) (guard : d770 p = 1) : d22 p ≤ (1 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3167 p hg
    simpa only [d770, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3169 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (1 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3170 (p : Pattern) (guard : d770 p = 1) : d377 p ≤ (1 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3169 p hg
    simpa only [d770, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3171 (p : Pattern) (guard : d770 p = 1) : d378 p ≤ (1 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3170 p hg
    simpa only [d378, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3172 (p : Pattern) (guard : d770 p = 1) : d379 p ≤ (1 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3173 (p : Pattern) (guard : d0 p = 1) : d260 p ≤ (1 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3174 (p : Pattern) (guard : d770 p = 1) : d380 p ≤ (1 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3173 p hg
    simpa only [d770, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3175 (p : Pattern) (guard : d770 p = 1) : d381 p ≤ (1 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d381, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3176 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (1 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3177 (p : Pattern) (guard : d770 p = 1) : d382 p ≤ (1 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3176 p hg
    simpa only [d770, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3178 (p : Pattern) (guard : d770 p = 1) : d383 p ≤ (1 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d383, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3179 (p : Pattern) (guard : d770 p = 1) : d384 p ≤ (1 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3178 p hg
    simpa only [d384, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3180 (p : Pattern) (guard : d770 p = 1) : d385 p ≤ (1 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d385, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3181 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (1 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3182 (p : Pattern) (guard : d770 p = 1) : d386 p ≤ (1 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3181 p hg
    simpa only [d770, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3183 (p : Pattern) (guard : d770 p = 1) : d387 p ≤ (1 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d387, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3184 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (1 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3185 (p : Pattern) (guard : d770 p = 1) : d388 p ≤ (1 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3184 p hg
    simpa only [d770, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3186 (p : Pattern) (guard : d770 p = 1) : d389 p ≤ (1 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3185 p hg
    simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d389, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3187 (p : Pattern) (guard : d770 p = 1) : d390 p ≤ (1 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3186 p hg
    simpa only [d390, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3188 (p : Pattern) (guard : d770 p = 1) : d391 p ≤ (1 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d391, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3189 (p : Pattern) (guard : d770 p = 1) : d392 p ≤ (1 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3180 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3188 p hg
    simpa only [d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3190 (p : Pattern) (guard : d770 p = 1) : d393 p ≤ (1 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3172 p hg
    simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3189 p hg
    simpa only [d393, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3191 (p : Pattern) (guard : d770 p = 1) : d394 p ≤ (1 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d394, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3192 (p : Pattern) (guard : d770 p = 1) : d395 p ≤ (1 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d395, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3193 (p : Pattern) (guard : d770 p = 1) : d396 p ≤ (1 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3192 p hg
    simpa only [d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3194 (p : Pattern) (guard : d770 p = 1) : d397 p ≤ (1 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d397, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3195 (p : Pattern) (guard : d770 p = 1) : d398 p ≤ (1 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d398, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3196 (p : Pattern) (guard : d770 p = 1) : d399 p ≤ (1 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3195 p hg
    simpa only [d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3197 (p : Pattern) (guard : d770 p = 1) : d400 p ≤ (1 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3193 p hg
    simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3196 p hg
    simpa only [d400, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3198 (p : Pattern) (guard : d770 p = 1) : d401 p ≤ (1 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3190 p hg
    simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d401, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3199 (p : Pattern) (guard : d770 p = 1) : d402 p ≤ (1 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3200 (p : Pattern) (guard : d770 p = 1) : d403 p ≤ (1 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d403, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3201 (p : Pattern) (guard : d770 p = 1) : d404 p ≤ (1 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3198 p hg
    simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3200 p hg
    simpa only [d404, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3202 (p : Pattern) (guard : d0 p = 1) : d290 p ≤ (1 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3203 (p : Pattern) (guard : d770 p = 1) : d405 p ≤ (1 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3202 p hg
    simpa only [d770, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3204 (p : Pattern) (guard : d770 p = 1) : d406 p ≤ (1 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3203 p hg
    simpa only [d406, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3205 (p : Pattern) (guard : d770 p = 1) : d407 p ≤ (1 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d407, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3206 (p : Pattern) (guard : d770 p = 1) : d408 p ≤ (1 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3205 p hg
    simpa only [d408, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3207 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (1 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3208 (p : Pattern) (guard : d770 p = 1) : d409 p ≤ (1 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d770, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3209 (p : Pattern) (guard : d770 p = 1) : d410 p ≤ (1 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3185 p hg
    simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3208 p hg
    simpa only [d410, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3210 (p : Pattern) (guard : d770 p = 1) : d411 p ≤ (1 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3209 p hg
    simpa only [d411, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3211 (p : Pattern) (guard : d770 p = 1) : d412 p ≤ (1 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3210 p hg
    simpa only [d412, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3212 (p : Pattern) (guard : d770 p = 1) : d413 p ≤ (1 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3211 p hg
    simpa only [d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3213 (p : Pattern) (guard : d770 p = 1) : d414 p ≤ (1 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d414, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3214 (p : Pattern) (guard : d770 p = 1) : d415 p ≤ (1 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3203 p hg
    simpa only [d415, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3215 (p : Pattern) (guard : d770 p = 1) : d416 p ≤ (1 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d416, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3216 (p : Pattern) (guard : d770 p = 1) : d417 p ≤ (1 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d417, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3217 (p : Pattern) (guard : d770 p = 1) : d418 p ≤ (1 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3208 p hg
    simpa only [d418, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3218 (p : Pattern) (guard : d770 p = 1) : d419 p ≤ (1 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3209 p hg
    simpa only [d419, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3219 (p : Pattern) (guard : d770 p = 1) : d420 p ≤ (1 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d420, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
