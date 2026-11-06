/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3080 (p : Pattern) (guard : d1175 p = 1) : d293 p ≤ (0 : Int) + d1185 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3079 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3081 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3082 (p : Pattern) (guard : d1175 p = 1) : d298 p ≤ (0 : Int) + d1186 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d298, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d298, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d298, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3081 p hg
    simpa only [d1175, d298, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3083 (p : Pattern) (guard : d1175 p = 1) : d299 p ≤ (0 : Int) + d1187 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d299, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d299, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d299, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3082 p hg
    simpa only [d299, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3084 (p : Pattern) (guard : d1175 p = 1) : d300 p ≤ (0 : Int) + d1188 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d300, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3080 p hg
    simpa only [d300, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d300, d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d300, d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3085 (p : Pattern) (guard : d1175 p = 1) : d294 p ≤ (0 : Int) + d1189 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d294, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d1175, d294, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d294, d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1175, d294, d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3086 (p : Pattern) (guard : d1175 p = 1) : d294 p ≤ (0 : Int) + d1190 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3085 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3087 (p : Pattern) (guard : d1175 p = 1) : d295 p ≤ (0 : Int) + d1191 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d295, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d1175, d295, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d295, d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1175, d295, d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3088 (p : Pattern) (guard : d1175 p = 1) : d295 p ≤ (0 : Int) + d1192 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3087 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3089 (p : Pattern) (guard : d1175 p = 1) : d296 p ≤ (0 : Int) + d1193 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d296, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3086 p hg
    simpa only [d296, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d296, d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3088 p hg
    simpa only [d296, d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3090 (p : Pattern) (guard : d1175 p = 1) : d301 p ≤ (0 : Int) + d1194 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d301, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3084 p hg
    simpa only [d301, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d301, d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d301, d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3091 (p : Pattern) (guard : d1175 p = 1) : d302 p ≤ (0 : Int) + d1195 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d302, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3077 p hg
    simpa only [d302, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d302, d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3090 p hg
    simpa only [d302, d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3092 (p : Pattern) (guard : d914 p = 1) : d86 p ≤ (0 : Int) + d86 p := by
  omega
theorem compare3093 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3094 (p : Pattern) (guard : d1175 p = 1) : d303 p ≤ (0 : Int) + d86 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1175, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3093 p hg
    simpa only [d1175, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3095 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3096 (p : Pattern) (guard : d1175 p = 1) : d304 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d304, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1175, d304, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d304, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3095 p hg
    simpa only [d1175, d304, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3097 (p : Pattern) (guard : d1175 p = 1) : d305 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d305, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3094 p hg
    simpa only [d305, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d305, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3096 p hg
    simpa only [d305, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3098 (p : Pattern) (guard : d1175 p = 1) : d306 p ≤ (0 : Int) + d1198 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d306, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d306, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d306, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3097 p hg
    simpa only [d306, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3099 (p : Pattern) (guard : d914 p = 1) : d98 p ≤ (0 : Int) + d98 p := by
  omega
theorem compare3100 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3101 (p : Pattern) (guard : d1175 p = 1) : d307 p ≤ (0 : Int) + d98 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d1175, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3100 p hg
    simpa only [d1175, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3102 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3103 (p : Pattern) (guard : d1175 p = 1) : d307 p ≤ (0 : Int) + d1199 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d307, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3099 p hg
    simpa only [d1175, d307, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d307, d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3102 p hg
    simpa only [d1175, d307, d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3104 (p : Pattern) (guard : d1175 p = 1) : d307 p ≤ (0 : Int) + d1200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3103 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3105 (p : Pattern) (guard : d1175 p = 1) : d308 p ≤ (0 : Int) + d1201 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d308, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3098 p hg
    simpa only [d308, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d308, d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d308, d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3106 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3107 (p : Pattern) (guard : d1175 p = 1) : d304 p ≤ (0 : Int) + d86 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1175, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3106 p hg
    simpa only [d1175, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3108 (p : Pattern) (guard : d1175 p = 1) : d309 p ≤ (0 : Int) + d1202 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d309, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1175, d309, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d309, d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1175, d309, d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3109 (p : Pattern) (guard : d1175 p = 1) : d310 p ≤ (0 : Int) + d1203 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d310, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d310, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d310, d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3108 p hg
    simpa only [d310, d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3110 (p : Pattern) (guard : d1175 p = 1) : d311 p ≤ (0 : Int) + d1204 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d311, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d311, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d311, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3109 p hg
    simpa only [d311, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3111 (p : Pattern) (guard : d1175 p = 1) : d307 p ≤ (0 : Int) + d307 p := by
  omega
theorem compare3112 (p : Pattern) (guard : d1175 p = 1) : d307 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3101 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3111 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3113 (p : Pattern) (guard : d914 p = 1) : d97 p ≤ (0 : Int) + d97 p := by
  omega
theorem compare3114 (p : Pattern) (guard : d1175 p = 1) : d312 p ≤ (0 : Int) + d97 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d1175, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d1175, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3115 (p : Pattern) (guard : d1175 p = 1) : d312 p ≤ (0 : Int) + d312 p := by
  omega
theorem compare3116 (p : Pattern) (guard : d1175 p = 1) : d312 p ≤ (0 : Int) + d1206 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3115 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3117 (p : Pattern) (guard : d1175 p = 1) : d313 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d313, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3112 p hg
    simpa only [d313, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d313, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d313, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3118 (p : Pattern) (guard : d1175 p = 1) : d314 p ≤ (0 : Int) + d1208 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d314, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3110 p hg
    simpa only [d314, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d314, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3117 p hg
    simpa only [d314, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3119 (p : Pattern) (guard : d1175 p = 1) : d315 p ≤ (0 : Int) + d1209 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d315, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3105 p hg
    simpa only [d315, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d315, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3118 p hg
    simpa only [d315, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3120 (p : Pattern) (guard : d1175 p = 1) : d316 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d316, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3091 p hg
    simpa only [d316, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d316, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3119 p hg
    simpa only [d316, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3121 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3122 (p : Pattern) (guard : d1175 p = 1) : d298 p ≤ (0 : Int) + d1176 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d298, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d298, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d298, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3121 p hg
    simpa only [d1175, d298, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3123 (p : Pattern) (guard : d1175 p = 1) : d299 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d299, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d299, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d299, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3122 p hg
    simpa only [d299, d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3124 (p : Pattern) (guard : d1175 p = 1) : d300 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3125 (p : Pattern) (guard : d1175 p = 1) : d301 p ≤ (0 : Int) + d1183 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d301, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3124 p hg
    simpa only [d301, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d301, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d301, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3126 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3127 (p : Pattern) (guard : d1175 p = 1) : d298 p ≤ (0 : Int) + d16 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3126 p hg
    simpa only [d1175, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3128 (p : Pattern) (guard : d1175 p = 1) : d317 p ≤ (0 : Int) + d1186 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d317, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d317, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d317, d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1175, d317, d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3129 (p : Pattern) (guard : d1175 p = 1) : d318 p ≤ (0 : Int) + d1187 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d318, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3127 p hg
    simpa only [d318, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d318, d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3128 p hg
    simpa only [d318, d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3130 (p : Pattern) (guard : d1175 p = 1) : d319 p ≤ (0 : Int) + d1187 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3083 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3131 (p : Pattern) (guard : d1175 p = 1) : d320 p ≤ (0 : Int) + d1211 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d320, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3130 p hg
    simpa only [d320, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d320, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3089 p hg
    simpa only [d320, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3132 (p : Pattern) (guard : d1175 p = 1) : d321 p ≤ (0 : Int) + d1212 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d321, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3125 p hg
    simpa only [d321, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d321, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3131 p hg
    simpa only [d321, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3133 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3134 (p : Pattern) (guard : d1175 p = 1) : d309 p ≤ (0 : Int) + d1196 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d309, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3092 p hg
    simpa only [d1175, d309, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d309, d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3133 p hg
    simpa only [d1175, d309, d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3135 (p : Pattern) (guard : d1175 p = 1) : d310 p ≤ (0 : Int) + d1197 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d310, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3107 p hg
    simpa only [d310, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d310, d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3134 p hg
    simpa only [d310, d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3136 (p : Pattern) (guard : d1175 p = 1) : d311 p ≤ (0 : Int) + d1198 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d311, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3123 p hg
    simpa only [d311, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d311, d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3135 p hg
    simpa only [d311, d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3137 (p : Pattern) (guard : d1175 p = 1) : d312 p ≤ (0 : Int) + d1213 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d312, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3113 p hg
    simpa only [d1175, d312, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d312, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1175, d312, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3138 (p : Pattern) (guard : d1175 p = 1) : d312 p ≤ (0 : Int) + d1214 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3114 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3137 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3139 (p : Pattern) (guard : d1175 p = 1) : d313 p ≤ (0 : Int) + d1215 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d313, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3104 p hg
    simpa only [d313, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d313, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3138 p hg
    simpa only [d313, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3140 (p : Pattern) (guard : d1175 p = 1) : d314 p ≤ (0 : Int) + d1216 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d314, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3136 p hg
    simpa only [d314, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d314, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3139 p hg
    simpa only [d314, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3141 (p : Pattern) (guard : d1175 p = 1) : d322 p ≤ (0 : Int) + d1217 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d322, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3129 p hg
    simpa only [d322, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d322, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3088 p hg
    simpa only [d322, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3142 (p : Pattern) (guard : d1175 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare3143 (p : Pattern) (guard : d1175 p = 1) : d323 p ≤ (0 : Int) + d1218 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d323, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3116 p hg
    simpa only [d323, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d323, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3142 p hg
    simpa only [d323, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3144 (p : Pattern) (guard : d1175 p = 1) : d324 p ≤ (0 : Int) + d1219 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d324, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3141 p hg
    simpa only [d324, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d324, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3143 p hg
    simpa only [d324, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3145 (p : Pattern) (guard : d1175 p = 1) : d325 p ≤ (0 : Int) + d1220 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d325, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3140 p hg
    simpa only [d325, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d325, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3144 p hg
    simpa only [d325, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3146 (p : Pattern) (guard : d1175 p = 1) : d326 p ≤ (0 : Int) + d1221 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d326, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3132 p hg
    simpa only [d326, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d326, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3145 p hg
    simpa only [d326, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3147 (p : Pattern) (guard : d1175 p = 1) : d327 p ≤ (0 : Int) + d1222 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d327, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3120 p hg
    simpa only [d327, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d327, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3146 p hg
    simpa only [d327, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3148 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3149 (p : Pattern) (guard : d910 p = 1) : d293 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3148 p hg
    simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3150 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3151 (p : Pattern) (guard : d912 p = 1) : d293 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3150 p hg
    simpa only [d912, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3152 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3153 (p : Pattern) (guard : d910 p = 1) : d294 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3152 p hg
    simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3154 (p : Pattern) (guard : d0 p = 1) : d294 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3155 (p : Pattern) (guard : d912 p = 1) : d294 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3154 p hg
    simpa only [d912, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3156 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3157 (p : Pattern) (guard : d910 p = 1) : d295 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3156 p hg
    simpa only [d910, d295, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3158 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3159 (p : Pattern) (guard : d912 p = 1) : d295 p ≤ (0 : Int) + d258 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3158 p hg
    simpa only [d912, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3160 (p : Pattern) (guard : d912 p = 1) : d296 p ≤ (0 : Int) + d259 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d296, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d296, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d296, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d296, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3161 (p : Pattern) (guard : d912 p = 1) : d297 p ≤ (0 : Int) + d260 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d297, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d297, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d297, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3160 p hg
    simpa only [d297, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3162 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3163 (p : Pattern) (guard : d912 p = 1) : d299 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d299, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3149 p hg
    simpa only [d912, d299, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d299, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3162 p hg
    simpa only [d912, d299, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3164 (p : Pattern) (guard : d912 p = 1) : d300 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d300, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d300, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d300, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d300, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3165 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3166 (p : Pattern) (guard : d912 p = 1) : d295 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3165 p hg
    simpa only [d912, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3167 (p : Pattern) (guard : d912 p = 1) : d296 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d296, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3155 p hg
    simpa only [d296, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d296, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3166 p hg
    simpa only [d296, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3168 (p : Pattern) (guard : d912 p = 1) : d301 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d301, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3164 p hg
    simpa only [d301, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d301, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3167 p hg
    simpa only [d301, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3169 (p : Pattern) (guard : d912 p = 1) : d302 p ≤ (0 : Int) + d266 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d302, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3161 p hg
    simpa only [d302, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d302, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d302, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3170 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3171 (p : Pattern) (guard : d910 p = 1) : d303 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d910, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3170 p hg
    simpa only [d910, d303, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3172 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3173 (p : Pattern) (guard : d912 p = 1) : d305 p ≤ (0 : Int) + d267 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d305, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3171 p hg
    simpa only [d912, d305, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d305, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3172 p hg
    simpa only [d912, d305, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3174 (p : Pattern) (guard : d912 p = 1) : d306 p ≤ (0 : Int) + d268 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d306, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3151 p hg
    simpa only [d306, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d306, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3173 p hg
    simpa only [d306, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3175 (p : Pattern) (guard : d910 p = 1) : d307 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2315 p hg
    simpa only [d910, d307, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3176 (p : Pattern) (guard : d0 p = 1) : d307 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3177 (p : Pattern) (guard : d912 p = 1) : d307 p ≤ (0 : Int) + d269 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3176 p hg
    simpa only [d912, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3178 (p : Pattern) (guard : d0 p = 1) : d307 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3179 (p : Pattern) (guard : d912 p = 1) : d307 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3175 p hg
    simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3178 p hg
    simpa only [d912, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3180 (p : Pattern) (guard : d912 p = 1) : d307 p ≤ (0 : Int) + d271 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3177 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3181 (p : Pattern) (guard : d912 p = 1) : d308 p ≤ (0 : Int) + d272 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d308, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3174 p hg
    simpa only [d308, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d308, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3180 p hg
    simpa only [d308, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3182 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3183 (p : Pattern) (guard : d910 p = 1) : d304 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3182 p hg
    simpa only [d910, d304, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3184 (p : Pattern) (guard : d0 p = 1) : d309 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3185 (p : Pattern) (guard : d912 p = 1) : d310 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d310, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3183 p hg
    simpa only [d912, d310, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d310, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3184 p hg
    simpa only [d912, d310, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3186 (p : Pattern) (guard : d912 p = 1) : d311 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d311, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d311, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d311, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3185 p hg
    simpa only [d311, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3187 (p : Pattern) (guard : d910 p = 1) : d312 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d910, d312, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3188 (p : Pattern) (guard : d0 p = 1) : d312 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3189 (p : Pattern) (guard : d912 p = 1) : d312 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3187 p hg
    simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3188 p hg
    simpa only [d912, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3190 (p : Pattern) (guard : d912 p = 1) : d313 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d313, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3179 p hg
    simpa only [d313, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d313, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3189 p hg
    simpa only [d313, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3191 (p : Pattern) (guard : d912 p = 1) : d314 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d314, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3186 p hg
    simpa only [d314, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d314, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3190 p hg
    simpa only [d314, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3192 (p : Pattern) (guard : d912 p = 1) : d315 p ≤ (0 : Int) + d278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d315, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3181 p hg
    simpa only [d315, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d315, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d315, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3193 (p : Pattern) (guard : d912 p = 1) : d316 p ≤ (0 : Int) + d279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d316, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3169 p hg
    simpa only [d316, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d316, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3192 p hg
    simpa only [d316, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3194 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3195 (p : Pattern) (guard : d910 p = 1) : d298 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3194 p hg
    simpa only [d910, d298, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3196 (p : Pattern) (guard : d0 p = 1) : d317 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3197 (p : Pattern) (guard : d912 p = 1) : d318 p ≤ (0 : Int) + d280 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3195 p hg
    simpa only [d912, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3196 p hg
    simpa only [d912, d318, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3198 (p : Pattern) (guard : d912 p = 1) : d319 p ≤ (0 : Int) + d281 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3163 p hg
    simpa only [d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d319, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3199 (p : Pattern) (guard : d0 p = 1) : d294 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3200 (p : Pattern) (guard : d912 p = 1) : d294 p ≤ (0 : Int) + d282 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3153 p hg
    simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d912, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3201 (p : Pattern) (guard : d0 p = 1) : d295 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3202 (p : Pattern) (guard : d912 p = 1) : d295 p ≤ (0 : Int) + d283 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3157 p hg
    simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3201 p hg
    simpa only [d912, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3203 (p : Pattern) (guard : d912 p = 1) : d296 p ≤ (0 : Int) + d284 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d296, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3200 p hg
    simpa only [d296, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d296, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3202 p hg
    simpa only [d296, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3204 (p : Pattern) (guard : d912 p = 1) : d320 p ≤ (0 : Int) + d285 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d320, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3198 p hg
    simpa only [d320, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d320, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3203 p hg
    simpa only [d320, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3205 (p : Pattern) (guard : d912 p = 1) : d321 p ≤ (0 : Int) + d286 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d321, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3168 p hg
    simpa only [d321, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d321, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d321, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3206 (p : Pattern) (guard : d912 p = 1) : d322 p ≤ (0 : Int) + d287 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d322, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3197 p hg
    simpa only [d322, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d322, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3202 p hg
    simpa only [d322, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3207 (p : Pattern) (guard : d912 p = 1) : d323 p ≤ (0 : Int) + d288 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d323, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3189 p hg
    simpa only [d323, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d323, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2678 p hg
    simpa only [d323, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3208 (p : Pattern) (guard : d912 p = 1) : d324 p ≤ (0 : Int) + d289 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d324, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3206 p hg
    simpa only [d324, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d324, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d324, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3209 (p : Pattern) (guard : d912 p = 1) : d325 p ≤ (0 : Int) + d290 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d325, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3191 p hg
    simpa only [d325, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d325, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3208 p hg
    simpa only [d325, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3210 (p : Pattern) (guard : d912 p = 1) : d326 p ≤ (0 : Int) + d291 p := by
  cases selected : p 86 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d326, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3205 p hg
    simpa only [d326, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d326, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3209 p hg
    simpa only [d326, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3211 (p : Pattern) (guard : d912 p = 1) : d327 p ≤ (0 : Int) + d292 p := by
  cases selected : p 80 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d327, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3193 p hg
    simpa only [d327, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d327, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3210 p hg
    simpa only [d327, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3212 (p : Pattern) (guard : d0 p = 1) : d293 p ≤ (1 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3213 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (1 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3214 (p : Pattern) (guard : d910 p = 1) : d293 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare109 p hg
    simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d910, d293, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3215 (p : Pattern) (guard : d1132 p = 1) : d293 p ≤ (1 : Int) + d28 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3212 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3216 (p : Pattern) (guard : d0 p = 1) : d294 p ≤ (1 : Int) + d47 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3217 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (1 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3218 (p : Pattern) (guard : d910 p = 1) : d294 p ≤ (1 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d910, d294, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3219 (p : Pattern) (guard : d1132 p = 1) : d294 p ≤ (1 : Int) + d47 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3216 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
