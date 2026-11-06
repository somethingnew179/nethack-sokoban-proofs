/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons320
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44940 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44939 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44941 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44940 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44942 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44941 p hg
    simpa only [d8106, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44943 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d8107, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44942 p hg
    simpa only [d8107, d3306, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44944 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d8084, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44945 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44944 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44946 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44945 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44947 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44946 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44948 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44947 p hg
    simpa only [d8106, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44949 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44948 p hg
    simpa only [d8112, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d8112, d3277, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44950 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44943 p hg
    simpa only [d8113, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44949 p hg
    simpa only [d8113, d3307, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44951 (p : Pattern) (guard : d8112 p = 1) : d3282 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44897 p hg
    simpa only [d8112, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d8112, d3282, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44952 (p : Pattern) (guard : d8118 p = 1) : d3285 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44951 p hg
    simpa only [d8118, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3285, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44953 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44950 p hg
    simpa only [d8119, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44952 p hg
    simpa only [d8119, d3308, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44954 (p : Pattern) (guard : d8105 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44955 (p : Pattern) (guard : d8111 p = 1) : d3287 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44954 p hg
    simpa only [d8111, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44956 (p : Pattern) (guard : d8112 p = 1) : d3288 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44921 p hg
    simpa only [d8112, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44955 p hg
    simpa only [d8112, d3288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44957 (p : Pattern) (guard : d0 p = 1) : d3265 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44958 (p : Pattern) (guard : d8117 p = 1) : d3289 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8117, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44957 p hg
    simpa only [d8117, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44959 (p : Pattern) (guard : d8118 p = 1) : d3290 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44956 p hg
    simpa only [d8118, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44958 p hg
    simpa only [d8118, d3290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44960 (p : Pattern) (guard : d0 p = 1) : d3291 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44961 (p : Pattern) (guard : d8117 p = 1) : d3292 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44925 p hg
    simpa only [d8117, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44960 p hg
    simpa only [d8117, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44962 (p : Pattern) (guard : d0 p = 1) : d3294 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44963 (p : Pattern) (guard : d8123 p = 1) : d3295 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44961 p hg
    simpa only [d8123, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44962 p hg
    simpa only [d8123, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44964 (p : Pattern) (guard : d8124 p = 1) : d3296 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44959 p hg
    simpa only [d8124, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44963 p hg
    simpa only [d8124, d3296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44965 (p : Pattern) (guard : d8125 p = 1) : d3329 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3329, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44953 p hg
    simpa only [d8125, d3329, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3329, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44964 p hg
    simpa only [d8125, d3329, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44966 (p : Pattern) (guard : d8126 p = 1) : d3352 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3352, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44933 p hg
    simpa only [d8126, d3352, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3352, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44965 p hg
    simpa only [d8126, d3352, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44967 (p : Pattern) (guard : d8105 p = 1) : d3230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8105, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44968 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44920 p hg
    simpa only [d8106, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44969 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44774 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44968 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44970 (p : Pattern) (guard : d0 p = 1) : d3240 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44971 (p : Pattern) (guard : d8111 p = 1) : d3241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44924 p hg
    simpa only [d8111, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44970 p hg
    simpa only [d8111, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44972 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44968 p hg
    simpa only [d8112, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8112, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44973 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44969 p hg
    simpa only [d8113, d3299, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44972 p hg
    simpa only [d8113, d3299, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44974 (p : Pattern) (guard : d8117 p = 1) : d3247 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d8117, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44975 (p : Pattern) (guard : d8118 p = 1) : d3248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44972 p hg
    simpa only [d8118, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44974 p hg
    simpa only [d8118, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44976 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44973 p hg
    simpa only [d8119, d3300, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44975 p hg
    simpa only [d8119, d3300, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44977 (p : Pattern) (guard : d8105 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44733 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44978 (p : Pattern) (guard : d0 p = 1) : d3254 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44979 (p : Pattern) (guard : d8111 p = 1) : d3301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44977 p hg
    simpa only [d8111, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44978 p hg
    simpa only [d8111, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44980 (p : Pattern) (guard : d8112 p = 1) : d3302 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44746 p hg
    simpa only [d8112, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44979 p hg
    simpa only [d8112, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44981 (p : Pattern) (guard : d8118 p = 1) : d3303 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44980 p hg
    simpa only [d8118, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44982 (p : Pattern) (guard : d8124 p = 1) : d3304 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44981 p hg
    simpa only [d8124, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44983 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44976 p hg
    simpa only [d8125, d3305, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44982 p hg
    simpa only [d8125, d3305, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44984 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d8084, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44985 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44984 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44986 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44985 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44987 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44986 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44988 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44987 p hg
    simpa only [d8106, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44989 (p : Pattern) (guard : d0 p = 1) : d3251 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44990 (p : Pattern) (guard : d8111 p = 1) : d3275 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44954 p hg
    simpa only [d8111, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44989 p hg
    simpa only [d8111, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44991 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44988 p hg
    simpa only [d8112, d3306, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44990 p hg
    simpa only [d8112, d3306, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44992 (p : Pattern) (guard : d0 p = 1) : d3246 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44993 (p : Pattern) (guard : d8117 p = 1) : d3277 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8117, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44992 p hg
    simpa only [d8117, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44994 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44991 p hg
    simpa only [d8118, d3307, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44993 p hg
    simpa only [d8118, d3307, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44995 (p : Pattern) (guard : d0 p = 1) : d3281 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44996 (p : Pattern) (guard : d8117 p = 1) : d3282 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8117, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44997 (p : Pattern) (guard : d0 p = 1) : d3284 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44998 (p : Pattern) (guard : d8123 p = 1) : d3285 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44996 p hg
    simpa only [d8123, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44997 p hg
    simpa only [d8123, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44999 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44994 p hg
    simpa only [d8124, d3308, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d8124, d3308, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45000 (p : Pattern) (guard : d8117 p = 1) : d3309 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44979 p hg
    simpa only [d8117, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45001 (p : Pattern) (guard : d8123 p = 1) : d3310 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45000 p hg
    simpa only [d8123, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45002 (p : Pattern) (guard : d8129 p = 1) : d3311 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45001 p hg
    simpa only [d8129, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45003 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44999 p hg
    simpa only [d8130, d3312, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45004 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44983 p hg
    simpa only [d8131, d3313, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45003 p hg
    simpa only [d8131, d3313, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45005 (p : Pattern) (guard : d8132 p = 1) : d3353 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3353, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44966 p hg
    simpa only [d8132, d3353, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3353, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45004 p hg
    simpa only [d8132, d3353, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45006 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44861 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44988 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45007 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45006 p hg
    simpa only [d8113, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44972 p hg
    simpa only [d8113, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45008 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45007 p hg
    simpa only [d8119, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44975 p hg
    simpa only [d8119, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45009 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45008 p hg
    simpa only [d8125, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44982 p hg
    simpa only [d8125, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45010 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d8084, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45011 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45010 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45012 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45011 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45013 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45012 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45014 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45013 p hg
    simpa only [d8106, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45015 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45014 p hg
    simpa only [d8112, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44990 p hg
    simpa only [d8112, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45016 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45015 p hg
    simpa only [d8118, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44993 p hg
    simpa only [d8118, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45017 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45016 p hg
    simpa only [d8124, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d8124, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45018 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45017 p hg
    simpa only [d8130, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45019 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45009 p hg
    simpa only [d8131, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45018 p hg
    simpa only [d8131, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45020 (p : Pattern) (guard : d8137 p = 1) : d3332 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3332, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45019 p hg
    simpa only [d8137, d3332, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3332, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d3332, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45021 (p : Pattern) (guard : d8138 p = 1) : d3354 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3354, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45005 p hg
    simpa only [d8138, d3354, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3354, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45020 p hg
    simpa only [d8138, d3354, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45022 (p : Pattern) (guard : d8139 p = 1) : d3355 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d3355, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44912 p hg
    simpa only [d8139, d3355, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d3355, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45021 p hg
    simpa only [d8139, d3355, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45023 (p : Pattern) (guard : d8140 p = 1) : d3356 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d3356, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44782 p hg
    simpa only [d8140, d3356, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d3356, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45022 p hg
    simpa only [d8140, d3356, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45024 (p : Pattern) (guard : d8087 p = 1) : d3229 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44346 p hg
    simpa only [d8087, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44519 p hg
    simpa only [d8087, d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45025 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44577 p hg
    simpa only [d8091, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45026 (p : Pattern) (guard : d8092 p = 1) : d3231 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45024 p hg
    simpa only [d8092, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45025 p hg
    simpa only [d8092, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45027 (p : Pattern) (guard : d8097 p = 1) : d3237 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45026 p hg
    simpa only [d8097, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44820 p hg
    simpa only [d8097, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45028 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44792 p hg
    simpa only [d8102, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44830 p hg
    simpa only [d8102, d3242, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45029 (p : Pattern) (guard : d8103 p = 1) : d3243 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45027 p hg
    simpa only [d8103, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45028 p hg
    simpa only [d8103, d3243, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45030 (p : Pattern) (guard : d8107 p = 1) : d3247 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44493 p hg
    simpa only [d8107, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3247, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45031 (p : Pattern) (guard : d8108 p = 1) : d3248 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44798 p hg
    simpa only [d8108, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45030 p hg
    simpa only [d8108, d3248, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45032 (p : Pattern) (guard : d8109 p = 1) : d3249 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45029 p hg
    simpa only [d8109, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45031 p hg
    simpa only [d8109, d3249, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45033 (p : Pattern) (guard : d8096 p = 1) : d3252 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44624 p hg
    simpa only [d8096, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3252, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45034 (p : Pattern) (guard : d8102 p = 1) : d3256 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45033 p hg
    simpa only [d8102, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44846 p hg
    simpa only [d8102, d3256, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45035 (p : Pattern) (guard : d8101 p = 1) : d3259 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44743 p hg
    simpa only [d8101, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d8101, d3259, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45036 (p : Pattern) (guard : d8107 p = 1) : d3261 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45035 p hg
    simpa only [d8107, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8107, d3261, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45037 (p : Pattern) (guard : d8108 p = 1) : d3262 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45034 p hg
    simpa only [d8108, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45036 p hg
    simpa only [d8108, d3262, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45038 (p : Pattern) (guard : d8101 p = 1) : d3263 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44700 p hg
    simpa only [d8101, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3263, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45039 (p : Pattern) (guard : d8107 p = 1) : d3264 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45038 p hg
    simpa only [d8107, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8107, d3264, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45040 (p : Pattern) (guard : d8113 p = 1) : d3267 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45039 p hg
    simpa only [d8113, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44675 p hg
    simpa only [d8113, d3267, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45041 (p : Pattern) (guard : d8114 p = 1) : d3268 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45037 p hg
    simpa only [d8114, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45040 p hg
    simpa only [d8114, d3268, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45042 (p : Pattern) (guard : d8115 p = 1) : d3269 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45032 p hg
    simpa only [d8115, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45041 p hg
    simpa only [d8115, d3269, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45043 (p : Pattern) (guard : d8086 p = 1) : d3272 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44469 p hg
    simpa only [d8086, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44771 p hg
    simpa only [d8086, d3272, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45044 (p : Pattern) (guard : d8091 p = 1) : d3273 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45043 p hg
    simpa only [d8091, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44742 p hg
    simpa only [d8091, d3273, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45045 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d8095, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45046 (p : Pattern) (guard : d8096 p = 1) : d3274 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45044 p hg
    simpa only [d8096, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45045 p hg
    simpa only [d8096, d3274, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45047 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44474 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45048 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45047 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45049 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45048 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45050 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45049 p hg
    simpa only [d8101, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45051 (p : Pattern) (guard : d8102 p = 1) : d3276 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45046 p hg
    simpa only [d8102, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45050 p hg
    simpa only [d8102, d3276, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45052 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44484 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45053 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45052 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45054 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45053 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45055 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45054 p hg
    simpa only [d8101, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45056 (p : Pattern) (guard : d8084 p = 1) : d3244 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d8084, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3244, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45057 (p : Pattern) (guard : d8089 p = 1) : d3244 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45056 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45058 (p : Pattern) (guard : d8094 p = 1) : d3244 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45057 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44460 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45059 (p : Pattern) (guard : d8100 p = 1) : d3244 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45058 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45060 (p : Pattern) (guard : d8106 p = 1) : d3246 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45059 p hg
    simpa only [d8106, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44592 p hg
    simpa only [d8106, d3246, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45061 (p : Pattern) (guard : d8107 p = 1) : d3277 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45055 p hg
    simpa only [d8107, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45060 p hg
    simpa only [d8107, d3277, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45062 (p : Pattern) (guard : d8108 p = 1) : d3278 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45051 p hg
    simpa only [d8108, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45061 p hg
    simpa only [d8108, d3278, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45063 (p : Pattern) (guard : d8084 p = 1) : d3279 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d8084, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3279, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45064 (p : Pattern) (guard : d8089 p = 1) : d3279 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45063 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44499 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45065 (p : Pattern) (guard : d8094 p = 1) : d3279 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45064 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44502 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45066 (p : Pattern) (guard : d8100 p = 1) : d3279 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45065 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45067 (p : Pattern) (guard : d8106 p = 1) : d3281 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45066 p hg
    simpa only [d8106, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44596 p hg
    simpa only [d8106, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45068 (p : Pattern) (guard : d8107 p = 1) : d3282 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44830 p hg
    simpa only [d8107, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45067 p hg
    simpa only [d8107, d3282, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45069 (p : Pattern) (guard : d8084 p = 1) : d3257 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d8084, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3257, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45070 (p : Pattern) (guard : d8089 p = 1) : d3257 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45069 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44446 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45071 (p : Pattern) (guard : d8094 p = 1) : d3257 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45070 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44511 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45072 (p : Pattern) (guard : d8100 p = 1) : d3257 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45071 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44539 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45073 (p : Pattern) (guard : d8106 p = 1) : d3283 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45072 p hg
    simpa only [d8106, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44599 p hg
    simpa only [d8106, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45074 (p : Pattern) (guard : d8112 p = 1) : d3284 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45073 p hg
    simpa only [d8112, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3284, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45075 (p : Pattern) (guard : d8113 p = 1) : d3285 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45068 p hg
    simpa only [d8113, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45074 p hg
    simpa only [d8113, d3285, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45076 (p : Pattern) (guard : d8114 p = 1) : d3286 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45062 p hg
    simpa only [d8114, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45075 p hg
    simpa only [d8114, d3286, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45077 (p : Pattern) (guard : d8101 p = 1) : d3255 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44860 p hg
    simpa only [d8101, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3255, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45078 (p : Pattern) (guard : d8106 p = 1) : d3287 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44865 p hg
    simpa only [d8106, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3287, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45079 (p : Pattern) (guard : d8107 p = 1) : d3288 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45077 p hg
    simpa only [d8107, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45078 p hg
    simpa only [d8107, d3288, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
