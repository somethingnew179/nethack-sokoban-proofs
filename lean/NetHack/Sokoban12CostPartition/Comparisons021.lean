/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2940 (p : Pattern) (guard : d916 p = 1) : d188 p ≤ (2 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2939 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2941 (p : Pattern) (guard : d916 p = 1) : d145 p ≤ (2 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2942 (p : Pattern) (guard : d916 p = 1) : d147 p ≤ (2 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2943 (p : Pattern) (guard : d916 p = 1) : d249 p ≤ (2 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2942 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2944 (p : Pattern) (guard : d916 p = 1) : d250 p ≤ (2 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2943 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2945 (p : Pattern) (guard : d916 p = 1) : d251 p ≤ (2 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2946 (p : Pattern) (guard : d916 p = 1) : d252 p ≤ (2 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2945 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2947 (p : Pattern) (guard : d916 p = 1) : d191 p ≤ (2 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2929 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2948 (p : Pattern) (guard : d916 p = 1) : d253 p ≤ (2 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2949 (p : Pattern) (guard : d916 p = 1) : d254 p ≤ (2 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2947 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2948 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2950 (p : Pattern) (guard : d916 p = 1) : d255 p ≤ (2 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2949 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2951 (p : Pattern) (guard : d916 p = 1) : d256 p ≤ (2 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2952 (p : Pattern) (guard : d916 p = 1) : d257 p ≤ (2 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2946 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2951 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2953 (p : Pattern) (guard : d916 p = 1) : d258 p ≤ (2 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2952 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2954 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2955 (p : Pattern) (guard : d770 p = 1) : d12 p ≤ (0 : Int) + d22 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2954 p hg
    simpa only [d770, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2956 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d265 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2957 (p : Pattern) (guard : d770 p = 1) : d62 p ≤ (0 : Int) + d377 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d62, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d62, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d62, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2956 p hg
    simpa only [d770, d62, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2958 (p : Pattern) (guard : d770 p = 1) : d63 p ≤ (0 : Int) + d378 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d63, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d63, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d63, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d63, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2959 (p : Pattern) (guard : d770 p = 1) : d64 p ≤ (0 : Int) + d379 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d64, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d64, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d64, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d64, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2960 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2961 (p : Pattern) (guard : d770 p = 1) : d65 p ≤ (0 : Int) + d386 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d65, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d65, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d65, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d770, d65, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2962 (p : Pattern) (guard : d770 p = 1) : d109 p ≤ (0 : Int) + d387 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d109, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d109, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d109, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d109, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2963 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2964 (p : Pattern) (guard : d770 p = 1) : d127 p ≤ (0 : Int) + d388 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d127, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d127, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d127, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2963 p hg
    simpa only [d770, d127, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2965 (p : Pattern) (guard : d770 p = 1) : d128 p ≤ (0 : Int) + d389 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d128, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d128, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d128, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d128, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2966 (p : Pattern) (guard : d770 p = 1) : d129 p ≤ (0 : Int) + d390 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d129, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d129, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d129, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2965 p hg
    simpa only [d129, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2967 (p : Pattern) (guard : d770 p = 1) : d237 p ≤ (0 : Int) + d391 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d237, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d237, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d237, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2966 p hg
    simpa only [d237, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2968 (p : Pattern) (guard : d770 p = 1) : d238 p ≤ (0 : Int) + d392 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d238, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1261 p hg
    simpa only [d238, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d238, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2967 p hg
    simpa only [d238, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2969 (p : Pattern) (guard : d770 p = 1) : d239 p ≤ (0 : Int) + d393 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d239, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2959 p hg
    simpa only [d239, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d239, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2968 p hg
    simpa only [d239, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2970 (p : Pattern) (guard : d770 p = 1) : d69 p ≤ (0 : Int) + d395 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d69, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d69, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d69, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d69, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2971 (p : Pattern) (guard : d770 p = 1) : d70 p ≤ (0 : Int) + d396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d70, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d70, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d70, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2970 p hg
    simpa only [d70, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2972 (p : Pattern) (guard : d770 p = 1) : d240 p ≤ (0 : Int) + d398 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d240, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2966 p hg
    simpa only [d240, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d240, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d240, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2973 (p : Pattern) (guard : d770 p = 1) : d241 p ≤ (0 : Int) + d399 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d241, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1268 p hg
    simpa only [d241, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d241, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2972 p hg
    simpa only [d241, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2974 (p : Pattern) (guard : d770 p = 1) : d242 p ≤ (0 : Int) + d400 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d242, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2971 p hg
    simpa only [d242, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d242, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2973 p hg
    simpa only [d242, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2975 (p : Pattern) (guard : d770 p = 1) : d243 p ≤ (0 : Int) + d401 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d243, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2969 p hg
    simpa only [d243, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d243, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d243, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2976 (p : Pattern) (guard : d770 p = 1) : d66 p ≤ (0 : Int) + d402 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d66, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d66, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d66, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d66, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2977 (p : Pattern) (guard : d770 p = 1) : d244 p ≤ (0 : Int) + d403 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d244, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d244, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d244, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d244, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2978 (p : Pattern) (guard : d770 p = 1) : d245 p ≤ (0 : Int) + d404 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d245, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d245, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d245, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d245, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2979 (p : Pattern) (guard : d0 p = 1) : d143 p ≤ (0 : Int) + d291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2980 (p : Pattern) (guard : d770 p = 1) : d144 p ≤ (0 : Int) + d409 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d144, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d144, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d144, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2979 p hg
    simpa only [d770, d144, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2981 (p : Pattern) (guard : d770 p = 1) : d146 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d146, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d146, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d146, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d146, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2982 (p : Pattern) (guard : d770 p = 1) : d155 p ≤ (0 : Int) + d411 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d155, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d155, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d155, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2981 p hg
    simpa only [d155, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2983 (p : Pattern) (guard : d770 p = 1) : d246 p ≤ (0 : Int) + d412 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d246, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d246, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d246, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d246, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2984 (p : Pattern) (guard : d770 p = 1) : d247 p ≤ (0 : Int) + d413 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d247, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d247, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d247, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2983 p hg
    simpa only [d247, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2985 (p : Pattern) (guard : d770 p = 1) : d248 p ≤ (0 : Int) + d414 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d248, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2984 p hg
    simpa only [d248, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d248, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d248, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2986 (p : Pattern) (guard : d770 p = 1) : d145 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d145, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d145, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d145, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d145, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2987 (p : Pattern) (guard : d770 p = 1) : d147 p ≤ (0 : Int) + d419 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d147, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2986 p hg
    simpa only [d147, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d147, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2981 p hg
    simpa only [d147, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2988 (p : Pattern) (guard : d770 p = 1) : d249 p ≤ (0 : Int) + d420 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d249, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2987 p hg
    simpa only [d249, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d249, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d249, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2989 (p : Pattern) (guard : d770 p = 1) : d250 p ≤ (0 : Int) + d421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d250, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d250, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d250, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2988 p hg
    simpa only [d250, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2990 (p : Pattern) (guard : d770 p = 1) : d251 p ≤ (0 : Int) + d422 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d251, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2989 p hg
    simpa only [d251, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d251, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d251, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2991 (p : Pattern) (guard : d770 p = 1) : d252 p ≤ (0 : Int) + d423 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d252, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2985 p hg
    simpa only [d252, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d252, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d252, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2992 (p : Pattern) (guard : d770 p = 1) : d253 p ≤ (0 : Int) + d425 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d253, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d253, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d253, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d253, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2993 (p : Pattern) (guard : d770 p = 1) : d254 p ≤ (0 : Int) + d426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d254, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1293 p hg
    simpa only [d254, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d254, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2992 p hg
    simpa only [d254, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2994 (p : Pattern) (guard : d770 p = 1) : d255 p ≤ (0 : Int) + d427 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d255, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2993 p hg
    simpa only [d255, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d255, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d255, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2995 (p : Pattern) (guard : d770 p = 1) : d256 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d256, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2994 p hg
    simpa only [d256, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d256, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d256, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2996 (p : Pattern) (guard : d770 p = 1) : d257 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d257, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2991 p hg
    simpa only [d257, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d257, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d257, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2997 (p : Pattern) (guard : d770 p = 1) : d258 p ≤ (0 : Int) + d430 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d258, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d258, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d258, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d258, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2998 (p : Pattern) (guard : d769 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare2999 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (1 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3000 (p : Pattern) (guard : d769 p = 1) : d12 p ≤ (1 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d769, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2999 p hg
    simpa only [d769, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d769, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d769, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3001 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (1 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3002 (p : Pattern) (guard : d769 p = 1) : d62 p ≤ (1 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d769, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d769, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d769, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1020 p hg
    simpa only [d769, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3003 (p : Pattern) (guard : d769 p = 1) : d63 p ≤ (1 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3004 (p : Pattern) (guard : d769 p = 1) : d64 p ≤ (1 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3005 (p : Pattern) (guard : d769 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  omega
theorem compare3006 (p : Pattern) (guard : d769 p = 1) : d65 p ≤ (1 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d769, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d769, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d769, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d769, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3007 (p : Pattern) (guard : d769 p = 1) : d109 p ≤ (1 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3008 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (1 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3009 (p : Pattern) (guard : d769 p = 1) : d127 p ≤ (1 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d769, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d769, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d769, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d769, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3010 (p : Pattern) (guard : d769 p = 1) : d128 p ≤ (1 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3009 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3011 (p : Pattern) (guard : d769 p = 1) : d129 p ≤ (1 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3010 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3012 (p : Pattern) (guard : d769 p = 1) : d237 p ≤ (1 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3013 (p : Pattern) (guard : d769 p = 1) : d238 p ≤ (1 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3014 (p : Pattern) (guard : d769 p = 1) : d239 p ≤ (1 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3004 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3015 (p : Pattern) (guard : d769 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare3016 (p : Pattern) (guard : d769 p = 1) : d69 p ≤ (1 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3017 (p : Pattern) (guard : d769 p = 1) : d70 p ≤ (1 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3015 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3016 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3018 (p : Pattern) (guard : d769 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  omega
theorem compare3019 (p : Pattern) (guard : d769 p = 1) : d240 p ≤ (1 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3020 (p : Pattern) (guard : d769 p = 1) : d241 p ≤ (1 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3018 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3021 (p : Pattern) (guard : d769 p = 1) : d242 p ≤ (1 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3017 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3022 (p : Pattern) (guard : d769 p = 1) : d243 p ≤ (1 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3014 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3023 (p : Pattern) (guard : d769 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare3024 (p : Pattern) (guard : d769 p = 1) : d66 p ≤ (1 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3023 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3025 (p : Pattern) (guard : d769 p = 1) : d244 p ≤ (1 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3026 (p : Pattern) (guard : d769 p = 1) : d245 p ≤ (1 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3022 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3025 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3027 (p : Pattern) (guard : d769 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  omega
theorem compare3028 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (1 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3029 (p : Pattern) (guard : d769 p = 1) : d144 p ≤ (1 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d769, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3028 p hg
    simpa only [d769, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d769, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d769, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3030 (p : Pattern) (guard : d769 p = 1) : d146 p ≤ (1 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3009 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3029 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3031 (p : Pattern) (guard : d769 p = 1) : d155 p ≤ (1 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3032 (p : Pattern) (guard : d769 p = 1) : d246 p ≤ (1 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3031 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3033 (p : Pattern) (guard : d769 p = 1) : d247 p ≤ (1 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3027 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3032 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3034 (p : Pattern) (guard : d769 p = 1) : d248 p ≤ (1 : Int) + d187 p := by
  cases selected : p 134 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d248, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3035 (p : Pattern) (guard : d769 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  omega
theorem compare3036 (p : Pattern) (guard : d769 p = 1) : d145 p ≤ (1 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3029 p hg
    simpa only [d145, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3037 (p : Pattern) (guard : d769 p = 1) : d147 p ≤ (1 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3036 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d147, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3038 (p : Pattern) (guard : d769 p = 1) : d249 p ≤ (1 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3037 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d249, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3039 (p : Pattern) (guard : d769 p = 1) : d250 p ≤ (1 : Int) + d188 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3038 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3040 (p : Pattern) (guard : d769 p = 1) : d251 p ≤ (1 : Int) + d189 p := by
  cases selected : p 134 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3039 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d251, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3041 (p : Pattern) (guard : d769 p = 1) : d252 p ≤ (1 : Int) + d190 p := by
  cases selected : p 133 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3034 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d252, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3042 (p : Pattern) (guard : d769 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  omega
theorem compare3043 (p : Pattern) (guard : d769 p = 1) : d253 p ≤ (1 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3031 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d253, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3044 (p : Pattern) (guard : d769 p = 1) : d254 p ≤ (1 : Int) + d191 p := by
  cases selected : p 141 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3042 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3043 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3045 (p : Pattern) (guard : d769 p = 1) : d255 p ≤ (1 : Int) + d192 p := by
  cases selected : p 134 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3044 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d255, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3046 (p : Pattern) (guard : d769 p = 1) : d256 p ≤ (1 : Int) + d193 p := by
  cases selected : p 133 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3045 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d256, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3047 (p : Pattern) (guard : d769 p = 1) : d257 p ≤ (1 : Int) + d194 p := by
  cases selected : p 132 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3046 p hg
    simpa only [d257, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3048 (p : Pattern) (guard : d769 p = 1) : d258 p ≤ (1 : Int) + d195 p := by
  cases selected : p 108 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3026 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d769 p = 1 := by simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3047 p hg
    simpa only [d258, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3049 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3050 (p : Pattern) (guard : d770 p = 1) : d12 p ≤ (0 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3049 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3051 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3052 (p : Pattern) (guard : d770 p = 1) : d62 p ≤ (0 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3051 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3053 (p : Pattern) (guard : d770 p = 1) : d63 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3052 p hg
    simpa only [d63, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3054 (p : Pattern) (guard : d986 p = 1) : d64 p ≤ (0 : Int) + d57 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d986, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3055 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3056 (p : Pattern) (guard : d770 p = 1) : d65 p ≤ (0 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3055 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3057 (p : Pattern) (guard : d770 p = 1) : d109 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d109, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3058 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3059 (p : Pattern) (guard : d770 p = 1) : d127 p ≤ (0 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3058 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3060 (p : Pattern) (guard : d770 p = 1) : d128 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d128, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3061 (p : Pattern) (guard : d770 p = 1) : d129 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3060 p hg
    simpa only [d129, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3062 (p : Pattern) (guard : d770 p = 1) : d237 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d237, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3063 (p : Pattern) (guard : d986 p = 1) : d238 p ≤ (0 : Int) + d179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3062 p hg
    simpa only [d986, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3064 (p : Pattern) (guard : d986 p = 1) : d239 p ≤ (0 : Int) + d180 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3054 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3063 p hg
    simpa only [d239, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3065 (p : Pattern) (guard : d770 p = 1) : d69 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d69, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3066 (p : Pattern) (guard : d986 p = 1) : d70 p ≤ (0 : Int) + d68 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d986, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3067 (p : Pattern) (guard : d770 p = 1) : d240 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d240, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3068 (p : Pattern) (guard : d986 p = 1) : d241 p ≤ (0 : Int) + d181 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d986, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3069 (p : Pattern) (guard : d986 p = 1) : d242 p ≤ (0 : Int) + d182 p := by
  cases selected : p 134 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d242, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3070 (p : Pattern) (guard : d986 p = 1) : d243 p ≤ (0 : Int) + d183 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d243, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3071 (p : Pattern) (guard : d986 p = 1) : d66 p ≤ (0 : Int) + d55 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d986, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3072 (p : Pattern) (guard : d986 p = 1) : d244 p ≤ (0 : Int) + d184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d244, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3073 (p : Pattern) (guard : d986 p = 1) : d245 p ≤ (0 : Int) + d185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d986 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3070 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d245, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3074 (p : Pattern) (guard : d0 p = 1) : d143 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3075 (p : Pattern) (guard : d770 p = 1) : d144 p ≤ (0 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3076 (p : Pattern) (guard : d770 p = 1) : d146 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d146, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3077 (p : Pattern) (guard : d770 p = 1) : d155 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d155, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3078 (p : Pattern) (guard : d770 p = 1) : d246 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d246, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3079 (p : Pattern) (guard : d986 p = 1) : d247 p ≤ (0 : Int) + d186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3078 p hg
    simpa only [d986, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
