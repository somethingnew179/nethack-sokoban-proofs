/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3080 (p : Pattern) (guard : d4207 p = 1) : d596 p ≤ (0 : Int) + d4258 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d4207, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3079 p hg
    simpa only [d4207, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3081 (p : Pattern) (guard : d0 p = 1) : d200 p ≤ (0 : Int) + d4263 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3082 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3083 (p : Pattern) (guard : d4206 p = 1) : d597 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3070 p hg
    simpa only [d4206, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3082 p hg
    simpa only [d4206, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3084 (p : Pattern) (guard : d4206 p = 1) : d598 p ≤ (0 : Int) + d32 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2970 p hg
    simpa only [d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3085 (p : Pattern) (guard : d4206 p = 1) : d599 p ≤ (0 : Int) + d4259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d599, d4259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d599, d4259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d599, d4259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d599, d4259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3086 (p : Pattern) (guard : d4206 p = 1) : d600 p ≤ (0 : Int) + d4260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d600, d4260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3084 p hg
    simpa only [d600, d4260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d600, d4260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3085 p hg
    simpa only [d600, d4260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3087 (p : Pattern) (guard : d4206 p = 1) : d601 p ≤ (0 : Int) + d4261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d601, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d601, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d601, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d601, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3088 (p : Pattern) (guard : d4206 p = 1) : d602 p ≤ (0 : Int) + d4262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d602, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3087 p hg
    simpa only [d602, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d602, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d602, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3089 (p : Pattern) (guard : d4206 p = 1) : d603 p ≤ (0 : Int) + d4263 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d603, d4263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3086 p hg
    simpa only [d603, d4263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d603, d4263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3088 p hg
    simpa only [d603, d4263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3090 (p : Pattern) (guard : d4207 p = 1) : d604 p ≤ (0 : Int) + d4263 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3081 p hg
    simpa only [d4207, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d4207, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3091 (p : Pattern) (guard : d4207 p = 1) : d605 p ≤ (0 : Int) + d4264 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d605, d4264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3080 p hg
    simpa only [d605, d4264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d605, d4264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3090 p hg
    simpa only [d605, d4264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3092 (p : Pattern) (guard : d4208 p = 1) : d606 p ≤ (0 : Int) + d4266 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d606, d4266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3091 p hg
    simpa only [d4208, d606, d4266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d606, d4266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4208, d606, d4266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3093 (p : Pattern) (guard : d4208 p = 1) : d607 p ≤ (0 : Int) + d4267 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d607, d4267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d607, d4267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d607, d4267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d607, d4267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3094 (p : Pattern) (guard : d4208 p = 1) : d608 p ≤ (0 : Int) + d4268 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d608, d4268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d608, d4268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d608, d4268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3093 p hg
    simpa only [d608, d4268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3095 (p : Pattern) (guard : d4208 p = 1) : d609 p ≤ (0 : Int) + d4269 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d609, d4269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d609, d4269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d609, d4269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3094 p hg
    simpa only [d609, d4269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3096 (p : Pattern) (guard : d0 p = 1) : d214 p ≤ (0 : Int) + d4273 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3097 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (0 : Int) + d4270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d215, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d215, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d215, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d215, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3098 (p : Pattern) (guard : d4206 p = 1) : d216 p ≤ (0 : Int) + d4271 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d216, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3023 p hg
    simpa only [d216, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d216, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3097 p hg
    simpa only [d216, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3099 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (0 : Int) + d4272 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d217, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3097 p hg
    simpa only [d217, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d217, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d217, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3100 (p : Pattern) (guard : d4206 p = 1) : d218 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d218, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d218, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d218, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d218, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3101 (p : Pattern) (guard : d4207 p = 1) : d219 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d4207, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d4207, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3102 (p : Pattern) (guard : d4207 p = 1) : d220 p ≤ (0 : Int) + d4274 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d220, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3018 p hg
    simpa only [d220, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d220, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d220, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3103 (p : Pattern) (guard : d0 p = 1) : d457 p ≤ (0 : Int) + d4274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3104 (p : Pattern) (guard : d4208 p = 1) : d610 p ≤ (0 : Int) + d4274 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3102 p hg
    simpa only [d4208, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d4208, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3105 (p : Pattern) (guard : d4206 p = 1) : d611 p ≤ (0 : Int) + d4270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d611, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d611, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d611, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d611, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3106 (p : Pattern) (guard : d4206 p = 1) : d612 p ≤ (0 : Int) + d4271 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d612, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3049 p hg
    simpa only [d612, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d612, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d612, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3107 (p : Pattern) (guard : d4206 p = 1) : d613 p ≤ (0 : Int) + d4272 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d613, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d613, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d613, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d613, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3108 (p : Pattern) (guard : d4206 p = 1) : d614 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d614, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d614, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d614, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d614, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3109 (p : Pattern) (guard : d4207 p = 1) : d615 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d4207, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3108 p hg
    simpa only [d4207, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3110 (p : Pattern) (guard : d4207 p = 1) : d616 p ≤ (0 : Int) + d4274 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d616, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3046 p hg
    simpa only [d616, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d616, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3109 p hg
    simpa only [d616, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3111 (p : Pattern) (guard : d4208 p = 1) : d617 p ≤ (0 : Int) + d4275 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d617, d4275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3110 p hg
    simpa only [d4208, d617, d4275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d617, d4275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d4208, d617, d4275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3112 (p : Pattern) (guard : d4208 p = 1) : d618 p ≤ (0 : Int) + d4276 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d618, d4276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d618, d4276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d618, d4276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3111 p hg
    simpa only [d618, d4276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3113 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d268, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d268, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3114 (p : Pattern) (guard : d4206 p = 1) : d269 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d4206, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d4206, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3115 (p : Pattern) (guard : d4206 p = 1) : d270 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d4206, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d4206, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3116 (p : Pattern) (guard : d4206 p = 1) : d271 p ≤ (0 : Int) + d104 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3117 (p : Pattern) (guard : d4206 p = 1) : d272 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d4206, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d4206, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3118 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d273, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d273, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3119 (p : Pattern) (guard : d4206 p = 1) : d274 p ≤ (0 : Int) + d108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3118 p hg
    simpa only [d4206, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d4206, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3120 (p : Pattern) (guard : d4206 p = 1) : d275 p ≤ (0 : Int) + d4233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d275, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3117 p hg
    simpa only [d275, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d275, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d275, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3121 (p : Pattern) (guard : d4206 p = 1) : d276 p ≤ (0 : Int) + d4234 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d276, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d276, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d276, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3120 p hg
    simpa only [d276, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3122 (p : Pattern) (guard : d4206 p = 1) : d279 p ≤ (0 : Int) + d4236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d279, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3120 p hg
    simpa only [d279, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d279, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3043 p hg
    simpa only [d279, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3123 (p : Pattern) (guard : d4206 p = 1) : d280 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d280, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3121 p hg
    simpa only [d280, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d280, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3122 p hg
    simpa only [d280, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3124 (p : Pattern) (guard : d4207 p = 1) : d281 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d4207, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d4207, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3125 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d282, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d282, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3126 (p : Pattern) (guard : d4206 p = 1) : d283 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3125 p hg
    simpa only [d4206, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3127 (p : Pattern) (guard : d4206 p = 1) : d284 p ≤ (0 : Int) + d4238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d284, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d284, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d284, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d284, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3128 (p : Pattern) (guard : d4206 p = 1) : d285 p ≤ (0 : Int) + d4270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d285, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d285, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d285, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d285, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3129 (p : Pattern) (guard : d4206 p = 1) : d286 p ≤ (0 : Int) + d4271 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d286, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3127 p hg
    simpa only [d286, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d286, d4271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3128 p hg
    simpa only [d286, d4271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3130 (p : Pattern) (guard : d4206 p = 1) : d287 p ≤ (0 : Int) + d4272 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d287, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3128 p hg
    simpa only [d287, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d287, d4272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d287, d4272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3131 (p : Pattern) (guard : d4206 p = 1) : d288 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d288, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d288, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d288, d4273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3130 p hg
    simpa only [d288, d4273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3132 (p : Pattern) (guard : d4207 p = 1) : d289 p ≤ (0 : Int) + d4273 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d4207, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d4207, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3133 (p : Pattern) (guard : d4207 p = 1) : d290 p ≤ (0 : Int) + d4274 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d290, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3124 p hg
    simpa only [d290, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d290, d4274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3132 p hg
    simpa only [d290, d4274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3134 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d4284 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3135 (p : Pattern) (guard : d4208 p = 1) : d619 p ≤ (0 : Int) + d4285 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d619, d4285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3133 p hg
    simpa only [d4208, d619, d4285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d619, d4285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3134 p hg
    simpa only [d4208, d619, d4285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3136 (p : Pattern) (guard : d0 p = 1) : d256 p ≤ (0 : Int) + d4290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3137 (p : Pattern) (guard : d1 p = 1) : d620 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d620, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d620, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d620, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d620, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3138 (p : Pattern) (guard : d4206 p = 1) : d621 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d4206, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d4206, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3139 (p : Pattern) (guard : d4206 p = 1) : d622 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d4206, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d4206, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3140 (p : Pattern) (guard : d4206 p = 1) : d623 p ≤ (0 : Int) + d104 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3139 p hg
    simpa only [d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3141 (p : Pattern) (guard : d1 p = 1) : d624 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d624, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d624, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d624, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d624, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3142 (p : Pattern) (guard : d4206 p = 1) : d625 p ≤ (0 : Int) + d25 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3141 p hg
    simpa only [d4206, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d4206, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3143 (p : Pattern) (guard : d4206 p = 1) : d626 p ≤ (0 : Int) + d4286 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d626, d4286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3048 p hg
    simpa only [d626, d4286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d626, d4286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d626, d4286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3144 (p : Pattern) (guard : d4206 p = 1) : d627 p ≤ (0 : Int) + d4287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d627, d4287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d627, d4287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d627, d4287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3143 p hg
    simpa only [d627, d4287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3145 (p : Pattern) (guard : d4206 p = 1) : d628 p ≤ (0 : Int) + d4288 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d628, d4288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d628, d4288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d628, d4288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d628, d4288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3146 (p : Pattern) (guard : d4206 p = 1) : d629 p ≤ (0 : Int) + d4289 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d629, d4289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3145 p hg
    simpa only [d629, d4289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d629, d4289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d629, d4289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3147 (p : Pattern) (guard : d4206 p = 1) : d630 p ≤ (0 : Int) + d4290 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d630, d4290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3144 p hg
    simpa only [d630, d4290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d630, d4290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3146 p hg
    simpa only [d630, d4290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3148 (p : Pattern) (guard : d4207 p = 1) : d631 p ≤ (0 : Int) + d4290 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3136 p hg
    simpa only [d4207, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3147 p hg
    simpa only [d4207, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3149 (p : Pattern) (guard : d0 p = 1) : d246 p ≤ (0 : Int) + d4283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3150 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3151 (p : Pattern) (guard : d4206 p = 1) : d632 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3047 p hg
    simpa only [d4206, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3150 p hg
    simpa only [d4206, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3152 (p : Pattern) (guard : d1 p = 1) : d633 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d633, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d633, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d633, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d633, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3153 (p : Pattern) (guard : d4206 p = 1) : d634 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3152 p hg
    simpa only [d4206, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3154 (p : Pattern) (guard : d4206 p = 1) : d635 p ≤ (0 : Int) + d117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3155 (p : Pattern) (guard : d1 p = 1) : d636 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d636, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3156 (p : Pattern) (guard : d4206 p = 1) : d637 p ≤ (0 : Int) + d108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d4206, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d4206, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3157 (p : Pattern) (guard : d4206 p = 1) : d638 p ≤ (0 : Int) + d4270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d638, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3156 p hg
    simpa only [d638, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d638, d4270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d638, d4270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3158 (p : Pattern) (guard : d4206 p = 1) : d639 p ≤ (0 : Int) + d4280 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d639, d4280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3154 p hg
    simpa only [d639, d4280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d639, d4280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d639, d4280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3159 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d120 p := by
  omega
theorem compare3160 (p : Pattern) (guard : d1 p = 1) : d640 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d640, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3161 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3162 (p : Pattern) (guard : d4206 p = 1) : d641 p ≤ (0 : Int) + d121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3160 p hg
    simpa only [d4206, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d4206, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3163 (p : Pattern) (guard : d4206 p = 1) : d642 p ≤ (0 : Int) + d4281 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d642, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3162 p hg
    simpa only [d642, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d642, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d642, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3164 (p : Pattern) (guard : d4206 p = 1) : d643 p ≤ (0 : Int) + d4282 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d643, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d643, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d643, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d643, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3165 (p : Pattern) (guard : d4206 p = 1) : d644 p ≤ (0 : Int) + d4283 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d644, d4283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3158 p hg
    simpa only [d644, d4283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d644, d4283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3164 p hg
    simpa only [d644, d4283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3166 (p : Pattern) (guard : d4207 p = 1) : d645 p ≤ (0 : Int) + d4283 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4207, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d4207, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d4207, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3165 p hg
    simpa only [d4207, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3167 (p : Pattern) (guard : d4207 p = 1) : d646 p ≤ (0 : Int) + d4291 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d646, d4291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d646, d4291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4207 p = 1 := by simpa only [d646, d4291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d646, d4291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3168 (p : Pattern) (guard : d4208 p = 1) : d647 p ≤ (0 : Int) + d4292 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4207 p = 1 := by simpa only [d4208, d647, d4292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3167 p hg
    simpa only [d4208, d647, d4292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4208, d647, d4292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4208, d647, d4292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3169 (p : Pattern) (guard : d4208 p = 1) : d648 p ≤ (0 : Int) + d4293 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d648, d4293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3135 p hg
    simpa only [d648, d4293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d648, d4293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d648, d4293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3170 (p : Pattern) (guard : d4208 p = 1) : d649 p ≤ (0 : Int) + d4294 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d649, d4294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d649, d4294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d649, d4294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3169 p hg
    simpa only [d649, d4294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3171 (p : Pattern) (guard : d4208 p = 1) : d650 p ≤ (0 : Int) + d4295 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d650, d4295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d650, d4295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d650, d4295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3170 p hg
    simpa only [d650, d4295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3172 (p : Pattern) (guard : d4208 p = 1) : d651 p ≤ (0 : Int) + d4296 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d651, d4296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d651, d4296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d651, d4296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d651, d4296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3173 (p : Pattern) (guard : d4208 p = 1) : d652 p ≤ (0 : Int) + d4297 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4208 p = 1 := by simpa only [d652, d4297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d652, d4297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4208 p = 1 := by simpa only [d652, d4297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3172 p hg
    simpa only [d652, d4297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3174 (p : Pattern) (guard : d0 p = 1) : d544 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3175 (p : Pattern) (guard : d4113 p = 1) : d545 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d4113, d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d4113, d545, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3176 (p : Pattern) (guard : d0 p = 1) : d548 p ≤ (0 : Int) + d426 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3177 (p : Pattern) (guard : d4114 p = 1) : d549 p ≤ (0 : Int) + d489 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d549, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d4114, d549, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d549, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3176 p hg
    simpa only [d4114, d549, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3178 (p : Pattern) (guard : d0 p = 1) : d551 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3179 (p : Pattern) (guard : d4113 p = 1) : d552 p ≤ (0 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d4113, d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3178 p hg
    simpa only [d4113, d552, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3180 (p : Pattern) (guard : d0 p = 1) : d554 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3181 (p : Pattern) (guard : d4114 p = 1) : d555 p ≤ (0 : Int) + d490 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d555, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d4114, d555, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d555, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3180 p hg
    simpa only [d4114, d555, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3182 (p : Pattern) (guard : d4114 p = 1) : d556 p ≤ (0 : Int) + d491 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d556, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d556, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d556, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3181 p hg
    simpa only [d556, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3183 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3184 (p : Pattern) (guard : d4113 p = 1) : d581 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2479 p hg
    simpa only [d4113, d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d4113, d581, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3185 (p : Pattern) (guard : d0 p = 1) : d584 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3186 (p : Pattern) (guard : d4114 p = 1) : d585 p ≤ (0 : Int) + d492 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d585, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3184 p hg
    simpa only [d4114, d585, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d585, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3185 p hg
    simpa only [d4114, d585, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3187 (p : Pattern) (guard : d4114 p = 1) : d586 p ≤ (0 : Int) + d493 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d586, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d586, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d586, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3186 p hg
    simpa only [d586, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3188 (p : Pattern) (guard : d4114 p = 1) : d587 p ≤ (0 : Int) + d494 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d587, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d587, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d587, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d587, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3189 (p : Pattern) (guard : d0 p = 1) : d607 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3190 (p : Pattern) (guard : d4114 p = 1) : d608 p ≤ (0 : Int) + d490 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d608, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d4114, d608, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d608, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3189 p hg
    simpa only [d4114, d608, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3191 (p : Pattern) (guard : d4114 p = 1) : d609 p ≤ (0 : Int) + d491 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d609, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d609, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d609, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3190 p hg
    simpa only [d609, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3192 (p : Pattern) (guard : d0 p = 1) : d617 p ≤ (0 : Int) + d224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3193 (p : Pattern) (guard : d4113 p = 1) : d618 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d4113, d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3192 p hg
    simpa only [d4113, d618, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3194 (p : Pattern) (guard : d0 p = 1) : d648 p ≤ (0 : Int) + d477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3195 (p : Pattern) (guard : d4114 p = 1) : d649 p ≤ (0 : Int) + d495 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d4114, d649, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3193 p hg
    simpa only [d4114, d649, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4114, d649, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d4114, d649, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3196 (p : Pattern) (guard : d4114 p = 1) : d650 p ≤ (0 : Int) + d496 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d650, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d650, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d650, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3195 p hg
    simpa only [d650, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3197 (p : Pattern) (guard : d4114 p = 1) : d651 p ≤ (0 : Int) + d497 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d651, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d651, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d651, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3196 p hg
    simpa only [d651, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3198 (p : Pattern) (guard : d4114 p = 1) : d652 p ≤ (0 : Int) + d498 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4114 p = 1 := by simpa only [d652, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3188 p hg
    simpa only [d652, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4114 p = 1 := by simpa only [d652, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d652, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3199 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d22 p := by
  omega
theorem compare3200 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3201 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d790 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3200 p hg
    simpa only [d4299, d29, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3202 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3203 (p : Pattern) (guard : d4301 p = 1) : d52 p ≤ (0 : Int) + d793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d52, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3201 p hg
    simpa only [d4301, d52, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d52, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3202 p hg
    simpa only [d4301, d52, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3204 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  omega
theorem compare3205 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d387 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3206 (p : Pattern) (guard : d4299 p = 1) : d65 p ≤ (0 : Int) + d794 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d65, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d65, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d65, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3205 p hg
    simpa only [d4299, d65, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3207 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3208 (p : Pattern) (guard : d4301 p = 1) : d76 p ≤ (0 : Int) + d801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d76, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d4301, d76, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d76, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d4301, d76, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3209 (p : Pattern) (guard : d4301 p = 1) : d77 p ≤ (0 : Int) + d802 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d77, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3203 p hg
    simpa only [d77, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d77, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3208 p hg
    simpa only [d77, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3210 (p : Pattern) (guard : d0 p = 1) : d400 p ≤ (0 : Int) + d813 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3211 (p : Pattern) (guard : d4302 p = 1) : d517 p ≤ (0 : Int) + d814 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d517, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3209 p hg
    simpa only [d4302, d517, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d517, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3210 p hg
    simpa only [d4302, d517, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3212 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3213 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d4299, d29, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3214 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3215 (p : Pattern) (guard : d4301 p = 1) : d531 p ≤ (0 : Int) + d816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d531, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d4301, d531, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d531, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d4301, d531, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3216 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3217 (p : Pattern) (guard : d4299 p = 1) : d65 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d65, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d65, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d65, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d4299, d65, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3218 (p : Pattern) (guard : d0 p = 1) : d541 p ≤ (0 : Int) + d811 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3219 (p : Pattern) (guard : d4301 p = 1) : d542 p ≤ (0 : Int) + d818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d542, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d4301, d542, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d542, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d4301, d542, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
