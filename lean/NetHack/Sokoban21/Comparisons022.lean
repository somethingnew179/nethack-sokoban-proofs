/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons021
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c3080 (pattern : Twelve) (guard : d1865 pattern = 1) : d831 pattern ≤ (0 : Int) + d1126 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d831, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3078 pattern childGuard
    simpa only [d831, d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d831, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3079 pattern childGuard
    simpa only [d831, d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3081 (pattern : Twelve) (guard : d1865 pattern = 1) : d845 pattern ≤ (0 : Int) + d1142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d845, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3077 pattern childGuard
    simpa only [d845, d1142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d845, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3080 pattern childGuard
    simpa only [d845, d1142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3082 (pattern : Twelve) (guard : d1865 pattern = 1) : d856 pattern ≤ (0 : Int) + d1157 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d856, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3076 pattern childGuard
    simpa only [d856, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d856, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3081 pattern childGuard
    simpa only [d856, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3083 (pattern : Twelve) (guard : d1865 pattern = 1) : d862 pattern ≤ (0 : Int) + d1166 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3071 pattern childGuard
    simpa only [d862, d1166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3082 pattern childGuard
    simpa only [d862, d1166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3084 (pattern : Twelve) (guard : d1865 pattern = 1) : d863 pattern ≤ (0 : Int) + d1167 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d863, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3064 pattern childGuard
    simpa only [d863, d1167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d863, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d863, d1167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3085 (pattern : Twelve) (guard : d1865 pattern = 1) : d867 pattern ≤ (0 : Int) + d1174 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3083 pattern childGuard
    simpa only [d867, d1174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3084 pattern childGuard
    simpa only [d867, d1174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3086 (pattern : Twelve) (guard : d1865 pattern = 1) : d869 pattern ≤ (0 : Int) + d1177 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3066 pattern childGuard
    simpa only [d869, d1177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3085 pattern childGuard
    simpa only [d869, d1177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3087 (pattern : Twelve) (guard : d1865 pattern = 1) : d838 pattern ≤ (0 : Int) + d1143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d838, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3059 pattern childGuard
    simpa only [d838, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3088 (pattern : Twelve) (guard : d1865 pattern = 1) : d853 pattern ≤ (0 : Int) + d1158 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3087 pattern childGuard
    simpa only [d853, d1158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3061 pattern childGuard
    simpa only [d853, d1158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3089 (pattern : Twelve) (guard : d1865 pattern = 1) : d861 pattern ≤ (0 : Int) + d1168 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3088 pattern childGuard
    simpa only [d861, d1168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3064 pattern childGuard
    simpa only [d861, d1168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3090 (pattern : Twelve) (guard : d1865 pattern = 1) : d842 pattern ≤ (0 : Int) + d1144 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d842, d1144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3068 pattern childGuard
    simpa only [d842, d1144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3091 (pattern : Twelve) (guard : d1865 pattern = 1) : d855 pattern ≤ (0 : Int) + d1159 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3090 pattern childGuard
    simpa only [d855, d1159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3070 pattern childGuard
    simpa only [d855, d1159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3092 (pattern : Twelve) (guard : d1865 pattern = 1) : d862 pattern ≤ (0 : Int) + d1169 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3091 pattern childGuard
    simpa only [d862, d1169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3082 pattern childGuard
    simpa only [d862, d1169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3093 (pattern : Twelve) (guard : d1865 pattern = 1) : d867 pattern ≤ (0 : Int) + d1175 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3092 pattern childGuard
    simpa only [d867, d1175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3084 pattern childGuard
    simpa only [d867, d1175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3094 (pattern : Twelve) (guard : d1865 pattern = 1) : d869 pattern ≤ (0 : Int) + d1178 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3089 pattern childGuard
    simpa only [d869, d1178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3093 pattern childGuard
    simpa only [d869, d1178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3095 (pattern : Twelve) (guard : d1865 pattern = 1) : d869 pattern ≤ (0 : Int) + d1180 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3086 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3094 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3096 (pattern : Twelve) (guard : d1865 pattern = 1) : d869 pattern ≤ (0 : Int) + d1181 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3095 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3094 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3097 (pattern : Twelve) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3098 (pattern : Twelve) (guard : d1865 pattern = 1) : d872 pattern ≤ (0 : Int) + d479 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d872, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d872, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d872, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3097 pattern childGuard
    simpa only [d1865, d872, d479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3099 (pattern : Twelve) (guard : d1865 pattern = 1) : d874 pattern ≤ (0 : Int) + d513 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d874, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d874, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d874, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d874, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3100 (pattern : Twelve) (guard : d1865 pattern = 1) : d875 pattern ≤ (0 : Int) + d1108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d875, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d875, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d875, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d875, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3101 (pattern : Twelve) (guard : d1865 pattern = 1) : d882 pattern ≤ (0 : Int) + d1123 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3099 pattern childGuard
    simpa only [d882, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3100 pattern childGuard
    simpa only [d882, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3102 (pattern : Twelve) (guard : d1865 pattern = 1) : d890 pattern ≤ (0 : Int) + d1143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d890, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d890, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d890, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3101 pattern childGuard
    simpa only [d890, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3103 (pattern : Twelve) (guard : d1865 pattern = 1) : d876 pattern ≤ (0 : Int) + d1114 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d876, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d876, d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d876, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d876, d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3104 (pattern : Twelve) (guard : d1865 pattern = 1) : d883 pattern ≤ (0 : Int) + d1127 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d883, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3103 pattern childGuard
    simpa only [d883, d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d883, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2949 pattern childGuard
    simpa only [d883, d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3105 (pattern : Twelve) (guard : d1865 pattern = 1) : d891 pattern ≤ (0 : Int) + d1145 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d891, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d891, d1145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d891, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3104 pattern childGuard
    simpa only [d891, d1145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3106 (pattern : Twelve) (guard : d1865 pattern = 1) : d898 pattern ≤ (0 : Int) + d1160 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d898, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3102 pattern childGuard
    simpa only [d898, d1160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d898, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3105 pattern childGuard
    simpa only [d898, d1160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3107 (pattern : Twelve) (guard : d1865 pattern = 1) : d877 pattern ≤ (0 : Int) + d1115 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d877, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d877, d1115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d877, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3073 pattern childGuard
    simpa only [d877, d1115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3108 (pattern : Twelve) (guard : d1865 pattern = 1) : d884 pattern ≤ (0 : Int) + d1128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d884, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3107 pattern childGuard
    simpa only [d884, d1128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d884, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3052 pattern childGuard
    simpa only [d884, d1128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3109 (pattern : Twelve) (guard : d1865 pattern = 1) : d892 pattern ≤ (0 : Int) + d1146 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d892, d1146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3108 pattern childGuard
    simpa only [d892, d1146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3110 (pattern : Twelve) (guard : d1865 pattern = 1) : d893 pattern ≤ (0 : Int) + d1147 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d893, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3055 pattern childGuard
    simpa only [d893, d1147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d893, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3104 pattern childGuard
    simpa only [d893, d1147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3111 (pattern : Twelve) (guard : d1865 pattern = 1) : d899 pattern ≤ (0 : Int) + d1161 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d899, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3109 pattern childGuard
    simpa only [d899, d1161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d899, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3110 pattern childGuard
    simpa only [d899, d1161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3112 (pattern : Twelve) (guard : d1865 pattern = 1) : d902 pattern ≤ (0 : Int) + d1170 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d902, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3106 pattern childGuard
    simpa only [d902, d1170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d902, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3111 pattern childGuard
    simpa only [d902, d1170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3113 (pattern : Twelve) (guard : d1865 pattern = 1) : d878 pattern ≤ (0 : Int) + d1116 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d878, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d878, d1116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d878, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2944 pattern childGuard
    simpa only [d878, d1116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3114 (pattern : Twelve) (guard : d1865 pattern = 1) : d885 pattern ≤ (0 : Int) + d1129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d885, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3107 pattern childGuard
    simpa only [d885, d1129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d885, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3113 pattern childGuard
    simpa only [d885, d1129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3115 (pattern : Twelve) (guard : d1865 pattern = 1) : d894 pattern ≤ (0 : Int) + d1148 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d894, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d894, d1148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d894, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3114 pattern childGuard
    simpa only [d894, d1148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3116 (pattern : Twelve) (guard : d1865 pattern = 1) : d879 pattern ≤ (0 : Int) + d518 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d879, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d879, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d879, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3021 pattern childGuard
    simpa only [d879, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3117 (pattern : Twelve) (guard : d1865 pattern = 1) : d886 pattern ≤ (0 : Int) + d556 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d886, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d886, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d886, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3116 pattern childGuard
    simpa only [d886, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3118 (pattern : Twelve) (guard : d1865 pattern = 1) : d895 pattern ≤ (0 : Int) + d1149 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d895, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3117 pattern childGuard
    simpa only [d895, d1149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d895, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3104 pattern childGuard
    simpa only [d895, d1149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3119 (pattern : Twelve) (guard : d1865 pattern = 1) : d900 pattern ≤ (0 : Int) + d1162 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d900, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3115 pattern childGuard
    simpa only [d900, d1162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d900, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3118 pattern childGuard
    simpa only [d900, d1162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3120 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (0 : Int) + d117 pattern := by
  omega
theorem c3121 (pattern : Twelve) (guard : d1865 pattern = 1) : d873 pattern ≤ (0 : Int) + d1107 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d873, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3120 pattern childGuard
    simpa only [d1865, d873, d1107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d873, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2943 pattern childGuard
    simpa only [d1865, d873, d1107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3122 (pattern : Twelve) (guard : d1865 pattern = 1) : d880 pattern ≤ (0 : Int) + d1117 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d880, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3121 pattern childGuard
    simpa only [d880, d1117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d880, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d880, d1117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3123 (pattern : Twelve) (guard : d1865 pattern = 1) : d887 pattern ≤ (0 : Int) + d1130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d887, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3030 pattern childGuard
    simpa only [d887, d1130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d887, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3122 pattern childGuard
    simpa only [d887, d1130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3124 (pattern : Twelve) (guard : d1865 pattern = 1) : d896 pattern ≤ (0 : Int) + d1150 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d896, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d896, d1150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d896, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3123 pattern childGuard
    simpa only [d896, d1150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3125 (pattern : Twelve) (guard : d1865 pattern = 1) : d881 pattern ≤ (0 : Int) + d528 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d881, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d881, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d881, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3018 pattern childGuard
    simpa only [d881, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3126 (pattern : Twelve) (guard : d1865 pattern = 1) : d888 pattern ≤ (0 : Int) + d559 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d888, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3125 pattern childGuard
    simpa only [d888, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d888, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3022 pattern childGuard
    simpa only [d888, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3127 (pattern : Twelve) (guard : d1865 pattern = 1) : d889 pattern ≤ (0 : Int) + d1131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d889, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2949 pattern childGuard
    simpa only [d889, d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d889, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d889, d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3128 (pattern : Twelve) (guard : d1865 pattern = 1) : d897 pattern ≤ (0 : Int) + d1151 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d897, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3126 pattern childGuard
    simpa only [d897, d1151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d897, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3127 pattern childGuard
    simpa only [d897, d1151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3129 (pattern : Twelve) (guard : d1865 pattern = 1) : d901 pattern ≤ (0 : Int) + d1163 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d901, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3124 pattern childGuard
    simpa only [d901, d1163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d901, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3128 pattern childGuard
    simpa only [d901, d1163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3130 (pattern : Twelve) (guard : d1865 pattern = 1) : d903 pattern ≤ (0 : Int) + d1171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d903, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3119 pattern childGuard
    simpa only [d903, d1171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d903, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3129 pattern childGuard
    simpa only [d903, d1171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3131 (pattern : Twelve) (guard : d1865 pattern = 1) : d904 pattern ≤ (0 : Int) + d1172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d904, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3111 pattern childGuard
    simpa only [d904, d1172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d904, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d904, d1172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3132 (pattern : Twelve) (guard : d1865 pattern = 1) : d905 pattern ≤ (0 : Int) + d1176 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d905, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3130 pattern childGuard
    simpa only [d905, d1176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d905, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3131 pattern childGuard
    simpa only [d905, d1176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3133 (pattern : Twelve) (guard : d1865 pattern = 1) : d906 pattern ≤ (0 : Int) + d1179 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d906, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3112 pattern childGuard
    simpa only [d906, d1179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d906, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3132 pattern childGuard
    simpa only [d906, d1179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3134 (pattern : Twelve) (guard : d1865 pattern = 1) : d907 pattern ≤ (0 : Int) + d1182 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d907, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3096 pattern childGuard
    simpa only [d907, d1182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d907, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3133 pattern childGuard
    simpa only [d907, d1182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3135 (pattern : Twelve) (guard : d1865 pattern = 1) : d1275 pattern ≤ (0 : Int) + d1105 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1275, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3040 pattern childGuard
    simpa only [d1865, d1275, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1275, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3097 pattern childGuard
    simpa only [d1865, d1275, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3136 (pattern : Twelve) (guard : d1865 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1278, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3135 pattern childGuard
    simpa only [d1278, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1278, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1278, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3137 (pattern : Twelve) (guard : d1865 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1505 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1284, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3136 pattern childGuard
    simpa only [d1284, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1284, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1284, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3138 (pattern : Twelve) (guard : d1865 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1517 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3046 pattern childGuard
    simpa only [d1293, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3137 pattern childGuard
    simpa only [d1293, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3139 (pattern : Twelve) (guard : d1865 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1518 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1294, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d1294, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1294, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1294, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3140 (pattern : Twelve) (guard : d1865 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1532 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3138 pattern childGuard
    simpa only [d1305, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3139 pattern childGuard
    simpa only [d1305, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3141 (pattern : Twelve) (guard : d1865 pattern = 1) : d1276 pattern ≤ (0 : Int) + d1106 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1276, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3072 pattern childGuard
    simpa only [d1865, d1276, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1276, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3020 pattern childGuard
    simpa only [d1865, d1276, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3142 (pattern : Twelve) (guard : d1865 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1495 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1279, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3135 pattern childGuard
    simpa only [d1279, d1495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1279, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3141 pattern childGuard
    simpa only [d1279, d1495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3143 (pattern : Twelve) (guard : d1865 pattern = 1) : d1280 pattern ≤ (0 : Int) + d1496 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1280, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1280, d1496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1280, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1280, d1496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3144 (pattern : Twelve) (guard : d1865 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1506 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1285, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3142 pattern childGuard
    simpa only [d1285, d1506, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1285, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3143 pattern childGuard
    simpa only [d1285, d1506, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3145 (pattern : Twelve) (guard : d1865 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1519 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1295, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3055 pattern childGuard
    simpa only [d1295, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1295, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3144 pattern childGuard
    simpa only [d1295, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3146 (pattern : Twelve) (guard : d1865 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1507 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1286, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d1286, d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1286, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d1286, d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3147 (pattern : Twelve) (guard : d1865 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1520 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1296, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3146 pattern childGuard
    simpa only [d1296, d1520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1296, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1296, d1520, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3148 (pattern : Twelve) (guard : d1865 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1533 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1306, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3145 pattern childGuard
    simpa only [d1306, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1306, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3147 pattern childGuard
    simpa only [d1306, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3149 (pattern : Twelve) (guard : d1865 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1541 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3140 pattern childGuard
    simpa only [d1313, d1541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3148 pattern childGuard
    simpa only [d1313, d1541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3150 (pattern : Twelve) (guard : d1865 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1521 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d1293, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3137 pattern childGuard
    simpa only [d1293, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3151 (pattern : Twelve) (guard : d1865 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1534 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3150 pattern childGuard
    simpa only [d1305, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3139 pattern childGuard
    simpa only [d1305, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3152 (pattern : Twelve) (guard : d1865 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1542 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3151 pattern childGuard
    simpa only [d1313, d1542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3148 pattern childGuard
    simpa only [d1313, d1542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3153 (pattern : Twelve) (guard : d1865 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1548 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3149 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3152 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3154 (pattern : Twelve) (guard : d1865 pattern = 1) : d1281 pattern ≤ (0 : Int) + d1497 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1281, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1281, d1497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1281, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3021 pattern childGuard
    simpa only [d1281, d1497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3155 (pattern : Twelve) (guard : d1865 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1508 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1287, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3142 pattern childGuard
    simpa only [d1287, d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1287, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3154 pattern childGuard
    simpa only [d1287, d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3156 (pattern : Twelve) (guard : d1865 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1522 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1297, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d1297, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1297, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3155 pattern childGuard
    simpa only [d1297, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3157 (pattern : Twelve) (guard : d1865 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1523 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1298, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d1298, d1523, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1298, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1298, d1523, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3158 (pattern : Twelve) (guard : d1865 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1535 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1307, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3156 pattern childGuard
    simpa only [d1307, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1307, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3157 pattern childGuard
    simpa only [d1307, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3159 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (0 : Int) + d15 pattern := by
  omega
theorem c3160 (pattern : Twelve) (guard : d1865 pattern = 1) : d1277 pattern ≤ (0 : Int) + d1493 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1277, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3159 pattern childGuard
    simpa only [d1865, d1277, d1493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1277, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1865, d1277, d1493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3161 (pattern : Twelve) (guard : d1865 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1498 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1282, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3141 pattern childGuard
    simpa only [d1282, d1498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1282, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3160 pattern childGuard
    simpa only [d1282, d1498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3162 (pattern : Twelve) (guard : d1865 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1509 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1288, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3161 pattern childGuard
    simpa only [d1288, d1509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1288, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3022 pattern childGuard
    simpa only [d1288, d1509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3163 (pattern : Twelve) (guard : d1865 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1524 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1299, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3077 pattern childGuard
    simpa only [d1299, d1524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1299, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3162 pattern childGuard
    simpa only [d1299, d1524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3164 (pattern : Twelve) (guard : d1865 pattern = 1) : d1289 pattern ≤ (0 : Int) + d1510 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1289, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3078 pattern childGuard
    simpa only [d1289, d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1289, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2949 pattern childGuard
    simpa only [d1289, d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3165 (pattern : Twelve) (guard : d1865 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1525 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1300, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3164 pattern childGuard
    simpa only [d1300, d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1300, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1300, d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3166 (pattern : Twelve) (guard : d1865 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1536 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1308, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3163 pattern childGuard
    simpa only [d1308, d1536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1308, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3165 pattern childGuard
    simpa only [d1308, d1536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3167 (pattern : Twelve) (guard : d1865 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1543 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1314, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d1314, d1543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1314, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3166 pattern childGuard
    simpa only [d1314, d1543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3168 (pattern : Twelve) (guard : d1865 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1544 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1315, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3148 pattern childGuard
    simpa only [d1315, d1544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1315, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1315, d1544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3169 (pattern : Twelve) (guard : d1865 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1549 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1319, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3167 pattern childGuard
    simpa only [d1319, d1549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1319, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3168 pattern childGuard
    simpa only [d1319, d1549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3170 (pattern : Twelve) (guard : d1865 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1551 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3153 pattern childGuard
    simpa only [d1321, d1551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3169 pattern childGuard
    simpa only [d1321, d1551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3171 (pattern : Twelve) (guard : d1865 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1552 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3152 pattern childGuard
    simpa only [d1321, d1552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1321, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3169 pattern childGuard
    simpa only [d1321, d1552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3172 (pattern : Twelve) (guard : d1865 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1554 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3170 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3171 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3173 (pattern : Twelve) (guard : d1865 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1555 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3172 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3171 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3174 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d11 pattern := by
  omega
theorem c3175 (pattern : Twelve) (guard : d0 pattern = 1) : d16 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3176 (pattern : Twelve) (guard : d1865 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1494 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1324, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3174 pattern childGuard
    simpa only [d1865, d1324, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1324, d1494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3175 pattern childGuard
    simpa only [d1865, d1324, d1494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3177 (pattern : Twelve) (guard : d1865 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1499 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1325, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3135 pattern childGuard
    simpa only [d1325, d1499, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1325, d1499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1325, d1499, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3178 (pattern : Twelve) (guard : d1865 pattern = 1) : d1326 pattern ≤ (0 : Int) + d1500 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1326, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1326, d1500, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1326, d1500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1326, d1500, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3179 (pattern : Twelve) (guard : d1865 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1511 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1333, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3177 pattern childGuard
    simpa only [d1333, d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1333, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3178 pattern childGuard
    simpa only [d1333, d1511, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3180 (pattern : Twelve) (guard : d1865 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1526 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1339, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d1339, d1526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1339, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3179 pattern childGuard
    simpa only [d1339, d1526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3181 (pattern : Twelve) (guard : d1865 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1537 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1345, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3180 pattern childGuard
    simpa only [d1345, d1537, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1345, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3139 pattern childGuard
    simpa only [d1345, d1537, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3182 (pattern : Twelve) (guard : d1865 pattern = 1) : d1327 pattern ≤ (0 : Int) + d1111 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1327, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3135 pattern childGuard
    simpa only [d1327, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1327, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3021 pattern childGuard
    simpa only [d1327, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3183 (pattern : Twelve) (guard : d1865 pattern = 1) : d1334 pattern ≤ (0 : Int) + d1512 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1334, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3182 pattern childGuard
    simpa only [d1334, d1512, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1334, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3143 pattern childGuard
    simpa only [d1334, d1512, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3184 (pattern : Twelve) (guard : d1865 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1527 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1340, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3055 pattern childGuard
    simpa only [d1340, d1527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1340, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3183 pattern childGuard
    simpa only [d1340, d1527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3185 (pattern : Twelve) (guard : d1865 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1538 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1346, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3184 pattern childGuard
    simpa only [d1346, d1538, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1346, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3147 pattern childGuard
    simpa only [d1346, d1538, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3186 (pattern : Twelve) (guard : d1865 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1545 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1349, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3181 pattern childGuard
    simpa only [d1349, d1545, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1349, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3185 pattern childGuard
    simpa only [d1349, d1545, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3187 (pattern : Twelve) (guard : d1865 pattern = 1) : d1328 pattern ≤ (0 : Int) + d1501 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1328, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d1328, d1501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1328, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3160 pattern childGuard
    simpa only [d1328, d1501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3188 (pattern : Twelve) (guard : d1865 pattern = 1) : d1335 pattern ≤ (0 : Int) + d1513 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1335, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3182 pattern childGuard
    simpa only [d1335, d1513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1335, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3187 pattern childGuard
    simpa only [d1335, d1513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3189 (pattern : Twelve) (guard : d1865 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1528 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1341, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d1341, d1528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1341, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3188 pattern childGuard
    simpa only [d1341, d1528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3190 (pattern : Twelve) (guard : d1865 pattern = 1) : d1329 pattern ≤ (0 : Int) + d1502 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1329, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d1329, d1502, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1329, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d1329, d1502, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3191 (pattern : Twelve) (guard : d1865 pattern = 1) : d1336 pattern ≤ (0 : Int) + d1514 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1336, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d1336, d1514, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1336, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3190 pattern childGuard
    simpa only [d1336, d1514, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3192 (pattern : Twelve) (guard : d1865 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1529 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1342, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3191 pattern childGuard
    simpa only [d1342, d1529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1342, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1342, d1529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3193 (pattern : Twelve) (guard : d1865 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1539 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1347, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3189 pattern childGuard
    simpa only [d1347, d1539, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1347, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3192 pattern childGuard
    simpa only [d1347, d1539, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3194 (pattern : Twelve) (guard : d1865 pattern = 1) : d1330 pattern ≤ (0 : Int) + d1112 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1330, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3141 pattern childGuard
    simpa only [d1330, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1330, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1330, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3195 (pattern : Twelve) (guard : d1865 pattern = 1) : d1331 pattern ≤ (0 : Int) + d1503 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1331, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3160 pattern childGuard
    simpa only [d1331, d1503, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1331, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1331, d1503, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3196 (pattern : Twelve) (guard : d1865 pattern = 1) : d1337 pattern ≤ (0 : Int) + d1515 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1337, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3194 pattern childGuard
    simpa only [d1337, d1515, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1337, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3195 pattern childGuard
    simpa only [d1337, d1515, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3197 (pattern : Twelve) (guard : d1865 pattern = 1) : d1343 pattern ≤ (0 : Int) + d1530 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1343, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3077 pattern childGuard
    simpa only [d1343, d1530, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1343, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3196 pattern childGuard
    simpa only [d1343, d1530, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3198 (pattern : Twelve) (guard : d1865 pattern = 1) : d1332 pattern ≤ (0 : Int) + d1504 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1332, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d1332, d1504, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1332, d1504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1332, d1504, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3199 (pattern : Twelve) (guard : d1865 pattern = 1) : d1338 pattern ≤ (0 : Int) + d1516 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1338, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3198 pattern childGuard
    simpa only [d1338, d1516, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1338, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3031 pattern childGuard
    simpa only [d1338, d1516, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3200 (pattern : Twelve) (guard : d1865 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1531 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1344, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3199 pattern childGuard
    simpa only [d1344, d1531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1344, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1344, d1531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3201 (pattern : Twelve) (guard : d1865 pattern = 1) : d1348 pattern ≤ (0 : Int) + d1540 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1348, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3197 pattern childGuard
    simpa only [d1348, d1540, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1348, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3200 pattern childGuard
    simpa only [d1348, d1540, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3202 (pattern : Twelve) (guard : d1865 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1546 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1350, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3193 pattern childGuard
    simpa only [d1350, d1546, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1350, d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3201 pattern childGuard
    simpa only [d1350, d1546, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3203 (pattern : Twelve) (guard : d1865 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1547 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1351, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3185 pattern childGuard
    simpa only [d1351, d1547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1351, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1351, d1547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3204 (pattern : Twelve) (guard : d1865 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1550 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1352, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3202 pattern childGuard
    simpa only [d1352, d1550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1352, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3203 pattern childGuard
    simpa only [d1352, d1550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3205 (pattern : Twelve) (guard : d1865 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1553 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1353, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3186 pattern childGuard
    simpa only [d1353, d1553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1353, d1553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3204 pattern childGuard
    simpa only [d1353, d1553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3206 (pattern : Twelve) (guard : d1865 pattern = 1) : d1354 pattern ≤ (0 : Int) + d1556 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1354, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3173 pattern childGuard
    simpa only [d1354, d1556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1354, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3205 pattern childGuard
    simpa only [d1354, d1556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3207 (pattern : Twelve) (guard : d1865 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1753 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1649, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d1649, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1649, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1649, d1753, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3208 (pattern : Twelve) (guard : d1865 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1754 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1650, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d1650, d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1650, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1650, d1754, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3209 (pattern : Twelve) (guard : d1865 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1763 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1656, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3207 pattern childGuard
    simpa only [d1656, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1656, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3208 pattern childGuard
    simpa only [d1656, d1763, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3210 (pattern : Twelve) (guard : d1865 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1745 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1644, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1644, d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1644, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d1644, d1745, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3211 (pattern : Twelve) (guard : d1865 pattern = 1) : d1645 pattern ≤ (0 : Int) + d1746 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1645, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d1645, d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1645, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1645, d1746, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3212 (pattern : Twelve) (guard : d1865 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1749 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1647, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3210 pattern childGuard
    simpa only [d1647, d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1647, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3211 pattern childGuard
    simpa only [d1647, d1749, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3213 (pattern : Twelve) (guard : d1865 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1755 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1651, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3146 pattern childGuard
    simpa only [d1651, d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1651, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3212 pattern childGuard
    simpa only [d1651, d1755, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3214 (pattern : Twelve) (guard : d1865 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1764 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1657, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3213 pattern childGuard
    simpa only [d1657, d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1657, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3165 pattern childGuard
    simpa only [d1657, d1764, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3215 (pattern : Twelve) (guard : d1865 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1770 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1660, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3209 pattern childGuard
    simpa only [d1660, d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1660, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3214 pattern childGuard
    simpa only [d1660, d1770, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3216 (pattern : Twelve) (guard : d1865 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1756 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1652, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d1652, d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1652, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3210 pattern childGuard
    simpa only [d1652, d1756, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3217 (pattern : Twelve) (guard : d1865 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1757 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1653, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3078 pattern childGuard
    simpa only [d1653, d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1653, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1653, d1757, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3218 (pattern : Twelve) (guard : d1865 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1765 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1658, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3216 pattern childGuard
    simpa only [d1658, d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1658, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3217 pattern childGuard
    simpa only [d1658, d1765, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3219 (pattern : Twelve) (guard : d1865 pattern = 1) : d1646 pattern ≤ (0 : Int) + d1747 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1646, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d1646, d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1646, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d1646, d1747, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
