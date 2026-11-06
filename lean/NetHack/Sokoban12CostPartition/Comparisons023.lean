/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3220 (p : Pattern) (guard : d770 p = 1) : d421 p ≤ (1 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3219 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3221 (p : Pattern) (guard : d770 p = 1) : d422 p ≤ (1 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3220 p hg
    simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d422, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3222 (p : Pattern) (guard : d770 p = 1) : d423 p ≤ (1 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3221 p hg
    simpa only [d423, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3223 (p : Pattern) (guard : d770 p = 1) : d424 p ≤ (1 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3205 p hg
    simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d424, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3224 (p : Pattern) (guard : d770 p = 1) : d425 p ≤ (1 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3210 p hg
    simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d425, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3225 (p : Pattern) (guard : d770 p = 1) : d426 p ≤ (1 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3226 (p : Pattern) (guard : d770 p = 1) : d427 p ≤ (1 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3225 p hg
    simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d427, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3227 (p : Pattern) (guard : d770 p = 1) : d428 p ≤ (1 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d428, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3228 (p : Pattern) (guard : d770 p = 1) : d429 p ≤ (1 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3222 p hg
    simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3227 p hg
    simpa only [d429, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3229 (p : Pattern) (guard : d770 p = 1) : d430 p ≤ (1 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3201 p hg
    simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d430, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3230 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3231 (p : Pattern) (guard : d770 p = 1) : d22 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3230 p hg
    simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3232 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3233 (p : Pattern) (guard : d770 p = 1) : d377 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3232 p hg
    simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3234 (p : Pattern) (guard : d770 p = 1) : d378 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3233 p hg
    simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3235 (p : Pattern) (guard : d770 p = 1) : d379 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3236 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3237 (p : Pattern) (guard : d770 p = 1) : d386 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3236 p hg
    simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3238 (p : Pattern) (guard : d770 p = 1) : d387 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3239 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3240 (p : Pattern) (guard : d770 p = 1) : d388 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3239 p hg
    simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3241 (p : Pattern) (guard : d770 p = 1) : d389 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3242 (p : Pattern) (guard : d770 p = 1) : d390 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3241 p hg
    simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3243 (p : Pattern) (guard : d770 p = 1) : d391 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3244 (p : Pattern) (guard : d770 p = 1) : d392 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3245 (p : Pattern) (guard : d770 p = 1) : d393 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3235 p hg
    simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3244 p hg
    simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3246 (p : Pattern) (guard : d770 p = 1) : d395 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3247 (p : Pattern) (guard : d770 p = 1) : d396 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3246 p hg
    simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3248 (p : Pattern) (guard : d770 p = 1) : d398 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3249 (p : Pattern) (guard : d770 p = 1) : d399 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3250 (p : Pattern) (guard : d770 p = 1) : d400 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3247 p hg
    simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3249 p hg
    simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3251 (p : Pattern) (guard : d770 p = 1) : d401 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3252 (p : Pattern) (guard : d770 p = 1) : d402 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3253 (p : Pattern) (guard : d770 p = 1) : d403 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3254 (p : Pattern) (guard : d770 p = 1) : d404 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3251 p hg
    simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3253 p hg
    simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3255 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (0 : Int) + d143 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3256 (p : Pattern) (guard : d770 p = 1) : d409 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3255 p hg
    simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3257 (p : Pattern) (guard : d770 p = 1) : d410 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3258 (p : Pattern) (guard : d770 p = 1) : d411 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3257 p hg
    simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3259 (p : Pattern) (guard : d770 p = 1) : d412 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3260 (p : Pattern) (guard : d770 p = 1) : d413 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3261 (p : Pattern) (guard : d770 p = 1) : d414 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3260 p hg
    simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3262 (p : Pattern) (guard : d770 p = 1) : d418 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3263 (p : Pattern) (guard : d770 p = 1) : d419 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3262 p hg
    simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3257 p hg
    simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3264 (p : Pattern) (guard : d770 p = 1) : d420 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3263 p hg
    simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3265 (p : Pattern) (guard : d770 p = 1) : d421 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3264 p hg
    simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3266 (p : Pattern) (guard : d770 p = 1) : d422 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3265 p hg
    simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3267 (p : Pattern) (guard : d770 p = 1) : d423 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3261 p hg
    simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3266 p hg
    simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3268 (p : Pattern) (guard : d770 p = 1) : d425 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3269 (p : Pattern) (guard : d770 p = 1) : d426 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3270 (p : Pattern) (guard : d770 p = 1) : d427 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3271 (p : Pattern) (guard : d770 p = 1) : d428 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3270 p hg
    simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3272 (p : Pattern) (guard : d770 p = 1) : d429 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3267 p hg
    simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3273 (p : Pattern) (guard : d770 p = 1) : d430 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3254 p hg
    simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3272 p hg
    simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3274 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (1 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3275 (p : Pattern) (guard : d770 p = 1) : d22 p ≤ (1 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d770, d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3276 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (1 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3277 (p : Pattern) (guard : d770 p = 1) : d377 p ≤ (1 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3276 p hg
    simpa only [d770, d377, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3278 (p : Pattern) (guard : d770 p = 1) : d378 p ≤ (1 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3277 p hg
    simpa only [d378, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3279 (p : Pattern) (guard : d770 p = 1) : d379 p ≤ (1 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d379, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3280 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (1 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3281 (p : Pattern) (guard : d770 p = 1) : d386 p ≤ (1 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3280 p hg
    simpa only [d770, d386, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3282 (p : Pattern) (guard : d770 p = 1) : d387 p ≤ (1 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d387, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3283 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (1 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3284 (p : Pattern) (guard : d770 p = 1) : d388 p ≤ (1 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d770, d388, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3285 (p : Pattern) (guard : d770 p = 1) : d389 p ≤ (1 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d389, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3286 (p : Pattern) (guard : d770 p = 1) : d390 p ≤ (1 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d390, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3287 (p : Pattern) (guard : d770 p = 1) : d391 p ≤ (1 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d391, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3288 (p : Pattern) (guard : d770 p = 1) : d392 p ≤ (1 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3180 p hg
    simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3287 p hg
    simpa only [d392, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3289 (p : Pattern) (guard : d770 p = 1) : d393 p ≤ (1 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3279 p hg
    simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3288 p hg
    simpa only [d393, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3290 (p : Pattern) (guard : d770 p = 1) : d395 p ≤ (1 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d395, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3291 (p : Pattern) (guard : d770 p = 1) : d396 p ≤ (1 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d396, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3292 (p : Pattern) (guard : d770 p = 1) : d398 p ≤ (1 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d398, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3293 (p : Pattern) (guard : d770 p = 1) : d399 p ≤ (1 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3292 p hg
    simpa only [d399, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3294 (p : Pattern) (guard : d770 p = 1) : d400 p ≤ (1 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3291 p hg
    simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d400, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3295 (p : Pattern) (guard : d770 p = 1) : d401 p ≤ (1 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3289 p hg
    simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3294 p hg
    simpa only [d401, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3296 (p : Pattern) (guard : d770 p = 1) : d402 p ≤ (1 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d402, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3297 (p : Pattern) (guard : d770 p = 1) : d403 p ≤ (1 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3294 p hg
    simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d403, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3298 (p : Pattern) (guard : d770 p = 1) : d404 p ≤ (1 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3295 p hg
    simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3297 p hg
    simpa only [d404, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3299 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (1 : Int) + d143 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3300 (p : Pattern) (guard : d770 p = 1) : d409 p ≤ (1 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3299 p hg
    simpa only [d770, d409, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3301 (p : Pattern) (guard : d770 p = 1) : d410 p ≤ (1 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d410, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3302 (p : Pattern) (guard : d770 p = 1) : d411 p ≤ (1 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3301 p hg
    simpa only [d411, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3303 (p : Pattern) (guard : d770 p = 1) : d412 p ≤ (1 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d412, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3304 (p : Pattern) (guard : d770 p = 1) : d413 p ≤ (1 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3303 p hg
    simpa only [d413, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3305 (p : Pattern) (guard : d770 p = 1) : d414 p ≤ (1 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3304 p hg
    simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d414, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3306 (p : Pattern) (guard : d770 p = 1) : d418 p ≤ (1 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d418, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3307 (p : Pattern) (guard : d770 p = 1) : d419 p ≤ (1 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3306 p hg
    simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3301 p hg
    simpa only [d419, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3308 (p : Pattern) (guard : d770 p = 1) : d420 p ≤ (1 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3307 p hg
    simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d420, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3309 (p : Pattern) (guard : d770 p = 1) : d421 p ≤ (1 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3308 p hg
    simpa only [d421, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3310 (p : Pattern) (guard : d770 p = 1) : d422 p ≤ (1 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3309 p hg
    simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d422, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3311 (p : Pattern) (guard : d770 p = 1) : d423 p ≤ (1 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3305 p hg
    simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3310 p hg
    simpa only [d423, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3312 (p : Pattern) (guard : d770 p = 1) : d425 p ≤ (1 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d425, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3313 (p : Pattern) (guard : d770 p = 1) : d426 p ≤ (1 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3312 p hg
    simpa only [d426, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3314 (p : Pattern) (guard : d770 p = 1) : d427 p ≤ (1 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3313 p hg
    simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d427, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3315 (p : Pattern) (guard : d770 p = 1) : d428 p ≤ (1 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3314 p hg
    simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d428, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3316 (p : Pattern) (guard : d770 p = 1) : d429 p ≤ (1 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3311 p hg
    simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3315 p hg
    simpa only [d429, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3317 (p : Pattern) (guard : d770 p = 1) : d430 p ≤ (1 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3298 p hg
    simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3316 p hg
    simpa only [d430, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3318 (p : Pattern) (guard : d0 p = 1) : d378 p ≤ (0 : Int) + d267 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3319 (p : Pattern) (guard : d984 p = 1) : d379 p ≤ (0 : Int) + d268 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d379, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d984, d379, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d379, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d984, d379, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3320 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (0 : Int) + d278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3321 (p : Pattern) (guard : d984 p = 1) : d392 p ≤ (0 : Int) + d279 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d392, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d984, d392, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d392, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3320 p hg
    simpa only [d984, d392, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3322 (p : Pattern) (guard : d984 p = 1) : d393 p ≤ (0 : Int) + d280 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d393, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d393, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d393, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3321 p hg
    simpa only [d393, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3323 (p : Pattern) (guard : d0 p = 1) : d395 p ≤ (0 : Int) + d281 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3324 (p : Pattern) (guard : d984 p = 1) : d396 p ≤ (0 : Int) + d282 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d396, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d984, d396, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d396, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3323 p hg
    simpa only [d984, d396, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3325 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3326 (p : Pattern) (guard : d984 p = 1) : d399 p ≤ (0 : Int) + d284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d399, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d984, d399, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d399, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3325 p hg
    simpa only [d984, d399, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3327 (p : Pattern) (guard : d984 p = 1) : d400 p ≤ (0 : Int) + d285 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d400, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3324 p hg
    simpa only [d400, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d400, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3326 p hg
    simpa only [d400, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3328 (p : Pattern) (guard : d984 p = 1) : d401 p ≤ (0 : Int) + d286 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d401, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3322 p hg
    simpa only [d401, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d401, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d401, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3329 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3330 (p : Pattern) (guard : d984 p = 1) : d402 p ≤ (0 : Int) + d287 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d402, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d984, d402, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d402, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3329 p hg
    simpa only [d984, d402, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3331 (p : Pattern) (guard : d984 p = 1) : d403 p ≤ (0 : Int) + d288 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d403, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d403, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d403, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d403, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3332 (p : Pattern) (guard : d984 p = 1) : d404 p ≤ (0 : Int) + d289 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d404, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3328 p hg
    simpa only [d404, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d404, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3331 p hg
    simpa only [d404, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3333 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3334 (p : Pattern) (guard : d984 p = 1) : d413 p ≤ (0 : Int) + d296 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d413, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d984, d413, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d413, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3333 p hg
    simpa only [d984, d413, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3335 (p : Pattern) (guard : d984 p = 1) : d414 p ≤ (0 : Int) + d297 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d414, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3334 p hg
    simpa only [d414, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d414, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d414, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3336 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3337 (p : Pattern) (guard : d984 p = 1) : d421 p ≤ (0 : Int) + d301 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d421, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d984, d421, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d421, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d984, d421, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3338 (p : Pattern) (guard : d984 p = 1) : d422 p ≤ (0 : Int) + d302 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d422, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3337 p hg
    simpa only [d422, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d422, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d422, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3339 (p : Pattern) (guard : d984 p = 1) : d423 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d423, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d423, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d423, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3338 p hg
    simpa only [d423, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3340 (p : Pattern) (guard : d0 p = 1) : d425 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3341 (p : Pattern) (guard : d984 p = 1) : d426 p ≤ (0 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d984, d426, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d984, d426, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d426, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3340 p hg
    simpa only [d984, d426, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3342 (p : Pattern) (guard : d984 p = 1) : d427 p ≤ (0 : Int) + d306 p := by
  cases selected : p 134 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d427, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3341 p hg
    simpa only [d427, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d427, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d427, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3343 (p : Pattern) (guard : d984 p = 1) : d428 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d428, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3342 p hg
    simpa only [d428, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d428, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d428, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3344 (p : Pattern) (guard : d984 p = 1) : d429 p ≤ (0 : Int) + d308 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d429, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3339 p hg
    simpa only [d429, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d429, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3343 p hg
    simpa only [d429, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3345 (p : Pattern) (guard : d984 p = 1) : d430 p ≤ (0 : Int) + d309 p := by
  cases selected : p 108 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d430, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3332 p hg
    simpa only [d430, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d430, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3344 p hg
    simpa only [d430, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3346 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3347 (p : Pattern) (guard : d1134 p = 1) : d21 p ≤ (0 : Int) + d31 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d21, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d1134, d21, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d21, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3346 p hg
    simpa only [d1134, d21, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3348 (p : Pattern) (guard : d0 p = 1) : d261 p ≤ (0 : Int) + d591 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3349 (p : Pattern) (guard : d1134 p = 1) : d375 p ≤ (0 : Int) + d592 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d375, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d1134, d375, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d375, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3348 p hg
    simpa only [d1134, d375, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3350 (p : Pattern) (guard : d1134 p = 1) : d376 p ≤ (0 : Int) + d593 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d376, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d376, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d376, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3349 p hg
    simpa only [d376, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3351 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3352 (p : Pattern) (guard : d1134 p = 1) : d22 p ≤ (0 : Int) + d33 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d22, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d1134, d22, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d22, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3351 p hg
    simpa only [d1134, d22, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3353 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d595 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3354 (p : Pattern) (guard : d1134 p = 1) : d377 p ≤ (0 : Int) + d596 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d377, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d1134, d377, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d377, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3353 p hg
    simpa only [d1134, d377, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3355 (p : Pattern) (guard : d1134 p = 1) : d378 p ≤ (0 : Int) + d597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d378, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d378, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d378, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3354 p hg
    simpa only [d378, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3356 (p : Pattern) (guard : d1134 p = 1) : d379 p ≤ (0 : Int) + d598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d379, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d379, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d379, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d379, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3357 (p : Pattern) (guard : d0 p = 1) : d260 p ≤ (0 : Int) + d590 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3358 (p : Pattern) (guard : d1134 p = 1) : d380 p ≤ (0 : Int) + d599 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d380, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d1134, d380, d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d380, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3357 p hg
    simpa only [d1134, d380, d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3359 (p : Pattern) (guard : d1134 p = 1) : d381 p ≤ (0 : Int) + d600 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d381, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d381, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d381, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d381, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
