/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons215
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30240 (p : Pattern) (guard : d5843 p = 1) : d3969 p ≤ (0 : Int) + d3165 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3969, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30239 p hg
    simpa only [d3969, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3969, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30021 p hg
    simpa only [d3969, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30241 (p : Pattern) (guard : d5843 p = 1) : d3970 p ≤ (0 : Int) + d3166 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3970, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30238 p hg
    simpa only [d3970, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3970, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30240 p hg
    simpa only [d3970, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30242 (p : Pattern) (guard : d5843 p = 1) : d3971 p ≤ (0 : Int) + d3167 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3971, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30070 p hg
    simpa only [d3971, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3971, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30040 p hg
    simpa only [d3971, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30243 (p : Pattern) (guard : d5843 p = 1) : d3972 p ≤ (0 : Int) + d3168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3972, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d3972, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3972, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30242 p hg
    simpa only [d3972, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30244 (p : Pattern) (guard : d5843 p = 1) : d3973 p ≤ (0 : Int) + d3169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3973, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30243 p hg
    simpa only [d3973, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3973, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d3973, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30245 (p : Pattern) (guard : d5843 p = 1) : d3974 p ≤ (0 : Int) + d3170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3974, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30106 p hg
    simpa only [d3974, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3974, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3974, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30246 (p : Pattern) (guard : d5843 p = 1) : d3975 p ≤ (0 : Int) + d3171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3975, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30245 p hg
    simpa only [d3975, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3975, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3975, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30247 (p : Pattern) (guard : d5843 p = 1) : d3976 p ≤ (0 : Int) + d3172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3976, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30246 p hg
    simpa only [d3976, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3976, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3976, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30248 (p : Pattern) (guard : d5843 p = 1) : d3977 p ≤ (0 : Int) + d3173 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3977, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30244 p hg
    simpa only [d3977, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3977, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30247 p hg
    simpa only [d3977, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30249 (p : Pattern) (guard : d5843 p = 1) : d3978 p ≤ (0 : Int) + d3174 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3978, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30241 p hg
    simpa only [d3978, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3978, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30248 p hg
    simpa only [d3978, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30250 (p : Pattern) (guard : d5843 p = 1) : d3979 p ≤ (0 : Int) + d3175 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3979, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d3979, d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3979, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30031 p hg
    simpa only [d3979, d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30251 (p : Pattern) (guard : d5843 p = 1) : d3980 p ≤ (0 : Int) + d3176 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3980, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30032 p hg
    simpa only [d3980, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3980, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30250 p hg
    simpa only [d3980, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30252 (p : Pattern) (guard : d5843 p = 1) : d3981 p ≤ (0 : Int) + d3177 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3981, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d3981, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3981, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30251 p hg
    simpa only [d3981, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30253 (p : Pattern) (guard : d5843 p = 1) : d3982 p ≤ (0 : Int) + d2126 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3982, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30058 p hg
    simpa only [d3982, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3982, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3982, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30254 (p : Pattern) (guard : d5843 p = 1) : d3983 p ≤ (0 : Int) + d3178 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3983, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30252 p hg
    simpa only [d3983, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3983, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30253 p hg
    simpa only [d3983, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30255 (p : Pattern) (guard : d5843 p = 1) : d3984 p ≤ (0 : Int) + d3179 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3984, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30236 p hg
    simpa only [d3984, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3984, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30254 p hg
    simpa only [d3984, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30256 (p : Pattern) (guard : d5843 p = 1) : d3985 p ≤ (0 : Int) + d2135 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3985, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d3985, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3985, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30045 p hg
    simpa only [d3985, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30257 (p : Pattern) (guard : d5843 p = 1) : d3986 p ≤ (0 : Int) + d2136 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3986, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30046 p hg
    simpa only [d3986, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3986, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30256 p hg
    simpa only [d3986, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30258 (p : Pattern) (guard : d5843 p = 1) : d3987 p ≤ (0 : Int) + d3180 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3987, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d3987, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3987, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30257 p hg
    simpa only [d3987, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30259 (p : Pattern) (guard : d5843 p = 1) : d3988 p ≤ (0 : Int) + d2131 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3988, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30013 p hg
    simpa only [d3988, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3988, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3988, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30260 (p : Pattern) (guard : d5843 p = 1) : d3989 p ≤ (0 : Int) + d3181 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3989, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30258 p hg
    simpa only [d3989, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3989, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30259 p hg
    simpa only [d3989, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30261 (p : Pattern) (guard : d5843 p = 1) : d3990 p ≤ (0 : Int) + d3182 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3990, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30260 p hg
    simpa only [d3990, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3990, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3990, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30262 (p : Pattern) (guard : d5843 p = 1) : d3991 p ≤ (0 : Int) + d3183 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3991, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30255 p hg
    simpa only [d3991, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3991, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30261 p hg
    simpa only [d3991, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30263 (p : Pattern) (guard : d5843 p = 1) : d3992 p ≤ (0 : Int) + d2137 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3992, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30257 p hg
    simpa only [d3992, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3992, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3992, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30264 (p : Pattern) (guard : d5843 p = 1) : d3993 p ≤ (0 : Int) + d3184 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3993, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30049 p hg
    simpa only [d3993, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3993, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30263 p hg
    simpa only [d3993, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30265 (p : Pattern) (guard : d5843 p = 1) : d3994 p ≤ (0 : Int) + d3185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3994, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30264 p hg
    simpa only [d3994, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3994, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3994, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30266 (p : Pattern) (guard : d5843 p = 1) : d3995 p ≤ (0 : Int) + d3186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3995, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30265 p hg
    simpa only [d3995, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3995, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3995, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30267 (p : Pattern) (guard : d5843 p = 1) : d3996 p ≤ (0 : Int) + d3187 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3996, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30262 p hg
    simpa only [d3996, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3996, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30266 p hg
    simpa only [d3996, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30268 (p : Pattern) (guard : d5843 p = 1) : d3997 p ≤ (0 : Int) + d3188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3997, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30049 p hg
    simpa only [d3997, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3997, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30040 p hg
    simpa only [d3997, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30269 (p : Pattern) (guard : d5843 p = 1) : d3998 p ≤ (0 : Int) + d3189 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3998, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30268 p hg
    simpa only [d3998, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3998, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d3998, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30270 (p : Pattern) (guard : d5843 p = 1) : d3999 p ≤ (0 : Int) + d3190 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3999, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30269 p hg
    simpa only [d3999, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3999, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30246 p hg
    simpa only [d3999, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30271 (p : Pattern) (guard : d5843 p = 1) : d4000 p ≤ (0 : Int) + d3191 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4000, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29876 p hg
    simpa only [d4000, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4000, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4000, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30272 (p : Pattern) (guard : d5843 p = 1) : d4001 p ≤ (0 : Int) + d3192 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4001, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30270 p hg
    simpa only [d4001, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4001, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30271 p hg
    simpa only [d4001, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30273 (p : Pattern) (guard : d5843 p = 1) : d4002 p ≤ (0 : Int) + d3193 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4002, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30267 p hg
    simpa only [d4002, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4002, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30272 p hg
    simpa only [d4002, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30274 (p : Pattern) (guard : d5843 p = 1) : d4003 p ≤ (0 : Int) + d3194 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4003, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30249 p hg
    simpa only [d4003, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4003, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30273 p hg
    simpa only [d4003, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30275 (p : Pattern) (guard : d5843 p = 1) : d4004 p ≤ (0 : Int) + d3195 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4004, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d4004, d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4004, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30098 p hg
    simpa only [d4004, d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30276 (p : Pattern) (guard : d5843 p = 1) : d4005 p ≤ (0 : Int) + d3196 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4005, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d4005, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4005, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d4005, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30277 (p : Pattern) (guard : d5843 p = 1) : d4006 p ≤ (0 : Int) + d3197 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4006, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30275 p hg
    simpa only [d4006, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4006, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30276 p hg
    simpa only [d4006, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30278 (p : Pattern) (guard : d5843 p = 1) : d4007 p ≤ (0 : Int) + d3198 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4007, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30277 p hg
    simpa only [d4007, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4007, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30116 p hg
    simpa only [d4007, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30279 (p : Pattern) (guard : d5843 p = 1) : d4008 p ≤ (0 : Int) + d3199 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4008, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30278 p hg
    simpa only [d4008, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4008, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30120 p hg
    simpa only [d4008, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30280 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d2154 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d115, d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30281 (p : Pattern) (guard : d5843 p = 1) : d326 p ≤ (0 : Int) + d2155 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d326, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30280 p hg
    simpa only [d326, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d326, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d326, d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30282 (p : Pattern) (guard : d5843 p = 1) : d4009 p ≤ (0 : Int) + d2156 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4009, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d4009, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4009, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30281 p hg
    simpa only [d4009, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30283 (p : Pattern) (guard : d5843 p = 1) : d4010 p ≤ (0 : Int) + d2157 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4010, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30032 p hg
    simpa only [d4010, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4010, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30282 p hg
    simpa only [d4010, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30284 (p : Pattern) (guard : d5843 p = 1) : d4011 p ≤ (0 : Int) + d2158 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4011, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30283 p hg
    simpa only [d4011, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4011, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4011, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30285 (p : Pattern) (guard : d5843 p = 1) : d4012 p ≤ (0 : Int) + d3200 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4012, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30070 p hg
    simpa only [d4012, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4012, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30284 p hg
    simpa only [d4012, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30286 (p : Pattern) (guard : d5843 p = 1) : d4013 p ≤ (0 : Int) + d3201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4013, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30285 p hg
    simpa only [d4013, d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4013, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d4013, d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30287 (p : Pattern) (guard : d5843 p = 1) : d4014 p ≤ (0 : Int) + d3202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4014, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30286 p hg
    simpa only [d4014, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4014, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30225 p hg
    simpa only [d4014, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30288 (p : Pattern) (guard : d5843 p = 1) : d4015 p ≤ (0 : Int) + d3203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4015, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30287 p hg
    simpa only [d4015, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4015, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30119 p hg
    simpa only [d4015, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30289 (p : Pattern) (guard : d5843 p = 1) : d4016 p ≤ (0 : Int) + d3204 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4016, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29943 p hg
    simpa only [d4016, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4016, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4016, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30290 (p : Pattern) (guard : d5843 p = 1) : d4017 p ≤ (0 : Int) + d3205 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4017, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30289 p hg
    simpa only [d4017, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4017, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4017, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30291 (p : Pattern) (guard : d5843 p = 1) : d4018 p ≤ (0 : Int) + d3206 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4018, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30288 p hg
    simpa only [d4018, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4018, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30290 p hg
    simpa only [d4018, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30292 (p : Pattern) (guard : d5843 p = 1) : d4019 p ≤ (0 : Int) + d3207 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4019, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30279 p hg
    simpa only [d4019, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4019, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30291 p hg
    simpa only [d4019, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30293 (p : Pattern) (guard : d5843 p = 1) : d4020 p ≤ (0 : Int) + d3208 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4020, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30274 p hg
    simpa only [d4020, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4020, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30292 p hg
    simpa only [d4020, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30294 (p : Pattern) (guard : d5843 p = 1) : d4021 p ≤ (0 : Int) + d3209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4021, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d4021, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4021, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d4021, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30295 (p : Pattern) (guard : d5843 p = 1) : d4022 p ≤ (0 : Int) + d3210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4022, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30275 p hg
    simpa only [d4022, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4022, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30294 p hg
    simpa only [d4022, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30296 (p : Pattern) (guard : d5843 p = 1) : d4023 p ≤ (0 : Int) + d3211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4023, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d4023, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4023, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d4023, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30297 (p : Pattern) (guard : d5843 p = 1) : d4024 p ≤ (0 : Int) + d3212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4024, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30296 p hg
    simpa only [d4024, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4024, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4024, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30298 (p : Pattern) (guard : d5843 p = 1) : d4025 p ≤ (0 : Int) + d3213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4025, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30295 p hg
    simpa only [d4025, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4025, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30297 p hg
    simpa only [d4025, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30299 (p : Pattern) (guard : d5843 p = 1) : d4026 p ≤ (0 : Int) + d3214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4026, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30107 p hg
    simpa only [d4026, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4026, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d4026, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30300 (p : Pattern) (guard : d5843 p = 1) : d4027 p ≤ (0 : Int) + d3215 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4027, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30299 p hg
    simpa only [d4027, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4027, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4027, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30301 (p : Pattern) (guard : d5843 p = 1) : d4028 p ≤ (0 : Int) + d3216 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4028, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30300 p hg
    simpa only [d4028, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4028, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4028, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30302 (p : Pattern) (guard : d5843 p = 1) : d4029 p ≤ (0 : Int) + d3217 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4029, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30298 p hg
    simpa only [d4029, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4029, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30301 p hg
    simpa only [d4029, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30303 (p : Pattern) (guard : d5843 p = 1) : d4030 p ≤ (0 : Int) + d3218 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4030, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30302 p hg
    simpa only [d4030, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4030, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30291 p hg
    simpa only [d4030, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30304 (p : Pattern) (guard : d5843 p = 1) : d4031 p ≤ (0 : Int) + d3219 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4031, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30303 p hg
    simpa only [d4031, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4031, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d4031, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30305 (p : Pattern) (guard : d5843 p = 1) : d4032 p ≤ (0 : Int) + d3220 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4032, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30293 p hg
    simpa only [d4032, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4032, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30304 p hg
    simpa only [d4032, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30306 (p : Pattern) (guard : d5843 p = 1) : d4033 p ≤ (0 : Int) + d3221 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4033, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30233 p hg
    simpa only [d4033, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4033, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30305 p hg
    simpa only [d4033, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30307 (p : Pattern) (guard : d5843 p = 1) : d4034 p ≤ (0 : Int) + d3222 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4034, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29986 p hg
    simpa only [d4034, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4034, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30306 p hg
    simpa only [d4034, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30308 (p : Pattern) (guard : d5843 p = 1) : d4035 p ≤ (0 : Int) + d3223 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4035, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30214 p hg
    simpa only [d4035, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4035, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30307 p hg
    simpa only [d4035, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30309 (p : Pattern) (guard : d5843 p = 1) : d4036 p ≤ (0 : Int) + d3224 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d4036, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30139 p hg
    simpa only [d4036, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d4036, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30308 p hg
    simpa only [d4036, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30310 (p : Pattern) (guard : d5847 p = 1) : d3540 p ≤ (0 : Int) + d3225 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3540, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29205 p hg
    simpa only [d5847, d3540, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3540, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17642 p hg
    simpa only [d5847, d3540, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30311 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30312 (p : Pattern) (guard : d5847 p = 1) : d3541 p ≤ (0 : Int) + d3227 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3541, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30310 p hg
    simpa only [d3541, d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3541, d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3541, d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30313 (p : Pattern) (guard : d5847 p = 1) : d3542 p ≤ (0 : Int) + d3228 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3542, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30312 p hg
    simpa only [d3542, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3542, d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3542, d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30314 (p : Pattern) (guard : d5847 p = 1) : d3543 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3543, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3543, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3543, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d3543, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30315 (p : Pattern) (guard : d5847 p = 1) : d3544 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30316 (p : Pattern) (guard : d5847 p = 1) : d3545 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30315 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30317 (p : Pattern) (guard : d5847 p = 1) : d3546 p ≤ (0 : Int) + d3229 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3546, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30313 p hg
    simpa only [d3546, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3546, d3229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3546, d3229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30318 (p : Pattern) (guard : d5847 p = 1) : d3547 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3547, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3547, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3547, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d3547, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30319 (p : Pattern) (guard : d5847 p = 1) : d3548 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30318 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30320 (p : Pattern) (guard : d5847 p = 1) : d3549 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30319 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30318 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30321 (p : Pattern) (guard : d5847 p = 1) : d3550 p ≤ (0 : Int) + d3230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3550, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30320 p hg
    simpa only [d3550, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3550, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3550, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30322 (p : Pattern) (guard : d5847 p = 1) : d3551 p ≤ (0 : Int) + d3231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3551, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30317 p hg
    simpa only [d3551, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3551, d3231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d3551, d3231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30323 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d3232 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17652 p hg
    simpa only [d5847, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30324 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d3233 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30323 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30325 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d3234 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30324 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30326 (p : Pattern) (guard : d5847 p = 1) : d3552 p ≤ (0 : Int) + d3235 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3552, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30325 p hg
    simpa only [d3552, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3552, d3235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3552, d3235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30327 (p : Pattern) (guard : d5847 p = 1) : d3553 p ≤ (0 : Int) + d3236 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3553, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30326 p hg
    simpa only [d3553, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3553, d3236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d3553, d3236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30328 (p : Pattern) (guard : d5847 p = 1) : d3554 p ≤ (0 : Int) + d3237 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3554, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30322 p hg
    simpa only [d3554, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3554, d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30327 p hg
    simpa only [d3554, d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30329 (p : Pattern) (guard : d5847 p = 1) : d3552 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30330 (p : Pattern) (guard : d5847 p = 1) : d3553 p ≤ (0 : Int) + d3238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3553, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30329 p hg
    simpa only [d3553, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3553, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d3553, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30331 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30332 (p : Pattern) (guard : d5847 p = 1) : d3555 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3555, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3555, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3555, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3555, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30333 (p : Pattern) (guard : d5847 p = 1) : d3556 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30332 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30334 (p : Pattern) (guard : d5847 p = 1) : d3557 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30333 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30332 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30335 (p : Pattern) (guard : d5847 p = 1) : d3558 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30334 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30336 (p : Pattern) (guard : d5847 p = 1) : d3559 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3559, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3559, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3559, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3559, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30337 (p : Pattern) (guard : d5847 p = 1) : d3560 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30336 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30338 (p : Pattern) (guard : d5847 p = 1) : d3561 p ≤ (0 : Int) + d3239 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30337 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30336 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30339 (p : Pattern) (guard : d5847 p = 1) : d3562 p ≤ (0 : Int) + d3240 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3562, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30338 p hg
    simpa only [d3562, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3562, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3562, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30340 (p : Pattern) (guard : d5847 p = 1) : d3563 p ≤ (0 : Int) + d3241 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3563, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30335 p hg
    simpa only [d3563, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3563, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30339 p hg
    simpa only [d3563, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30341 (p : Pattern) (guard : d5847 p = 1) : d3564 p ≤ (0 : Int) + d3242 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3564, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30330 p hg
    simpa only [d3564, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3564, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30340 p hg
    simpa only [d3564, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30342 (p : Pattern) (guard : d5847 p = 1) : d3565 p ≤ (0 : Int) + d3243 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3565, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30328 p hg
    simpa only [d3565, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3565, d3243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d3565, d3243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30343 (p : Pattern) (guard : d5847 p = 1) : d23 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30344 (p : Pattern) (guard : d5847 p = 1) : d3566 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23419 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30345 (p : Pattern) (guard : d5847 p = 1) : d3567 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30344 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23419 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30346 (p : Pattern) (guard : d5847 p = 1) : d3568 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30345 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30347 (p : Pattern) (guard : d5847 p = 1) : d3569 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3569, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d3569, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3569, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d3569, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30348 (p : Pattern) (guard : d5847 p = 1) : d3570 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30347 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30349 (p : Pattern) (guard : d5847 p = 1) : d3571 p ≤ (0 : Int) + d3244 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30348 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30347 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30350 (p : Pattern) (guard : d5847 p = 1) : d3572 p ≤ (0 : Int) + d3245 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3572, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30349 p hg
    simpa only [d3572, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3572, d3245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3572, d3245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30351 (p : Pattern) (guard : d5847 p = 1) : d3573 p ≤ (0 : Int) + d3246 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3573, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30346 p hg
    simpa only [d3573, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3573, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30350 p hg
    simpa only [d3573, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30352 (p : Pattern) (guard : d5847 p = 1) : d3574 p ≤ (0 : Int) + d3247 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3574, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30351 p hg
    simpa only [d3574, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3574, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3574, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30353 (p : Pattern) (guard : d5847 p = 1) : d3575 p ≤ (0 : Int) + d3248 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3575, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d3575, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3575, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30352 p hg
    simpa only [d3575, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30354 (p : Pattern) (guard : d5847 p = 1) : d3576 p ≤ (0 : Int) + d3249 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3576, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30342 p hg
    simpa only [d3576, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3576, d3249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30353 p hg
    simpa only [d3576, d3249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30355 (p : Pattern) (guard : d5847 p = 1) : d3577 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3577, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3577, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3577, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3577, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30356 (p : Pattern) (guard : d5847 p = 1) : d3578 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30355 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30357 (p : Pattern) (guard : d5847 p = 1) : d3579 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3579, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3579, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3579, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3579, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30358 (p : Pattern) (guard : d5847 p = 1) : d3580 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30357 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30359 (p : Pattern) (guard : d5847 p = 1) : d3581 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30356 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30358 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30360 (p : Pattern) (guard : d5847 p = 1) : d3582 p ≤ (0 : Int) + d3226 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30359 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30361 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30362 (p : Pattern) (guard : d5847 p = 1) : d3583 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3583, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3583, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3583, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d3583, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30363 (p : Pattern) (guard : d5847 p = 1) : d3584 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30362 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30364 (p : Pattern) (guard : d5847 p = 1) : d3585 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3585, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3585, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3585, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3585, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30365 (p : Pattern) (guard : d5847 p = 1) : d1715 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1715, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d1715, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1715, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d1715, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30366 (p : Pattern) (guard : d5847 p = 1) : d3586 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30365 p hg
    simpa only [d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30367 (p : Pattern) (guard : d5847 p = 1) : d3587 p ≤ (0 : Int) + d3250 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30363 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30366 p hg
    simpa only [d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30368 (p : Pattern) (guard : d5847 p = 1) : d3588 p ≤ (0 : Int) + d3251 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3588, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30367 p hg
    simpa only [d3588, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3588, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3588, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30369 (p : Pattern) (guard : d5847 p = 1) : d3589 p ≤ (0 : Int) + d3252 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3589, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3589, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3589, d3252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30368 p hg
    simpa only [d3589, d3252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30370 (p : Pattern) (guard : d5847 p = 1) : d34 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30371 (p : Pattern) (guard : d5847 p = 1) : d364 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d5847, d364, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d364, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30372 (p : Pattern) (guard : d5847 p = 1) : d3590 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30370 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30371 p hg
    simpa only [d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30373 (p : Pattern) (guard : d5847 p = 1) : d3591 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3591, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d5847, d3591, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3591, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d3591, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30374 (p : Pattern) (guard : d5847 p = 1) : d3592 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30373 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30371 p hg
    simpa only [d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30375 (p : Pattern) (guard : d5847 p = 1) : d3593 p ≤ (0 : Int) + d3253 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30372 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30374 p hg
    simpa only [d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30376 (p : Pattern) (guard : d5847 p = 1) : d3594 p ≤ (0 : Int) + d3254 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3594, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30375 p hg
    simpa only [d3594, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3594, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3594, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30377 (p : Pattern) (guard : d5847 p = 1) : d3595 p ≤ (0 : Int) + d3255 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3595, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d3595, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3595, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30376 p hg
    simpa only [d3595, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30378 (p : Pattern) (guard : d5847 p = 1) : d3596 p ≤ (0 : Int) + d3256 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3596, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30369 p hg
    simpa only [d3596, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3596, d3256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30377 p hg
    simpa only [d3596, d3256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30379 (p : Pattern) (guard : d5847 p = 1) : d39 p ≤ (0 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
