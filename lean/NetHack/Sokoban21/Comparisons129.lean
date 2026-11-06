/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons128
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c18060 (pattern : Twelve) (guard : d1865 pattern = 1) : d178 pattern ≤ (1 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17912 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18061 (pattern : Twelve) (guard : d1865 pattern = 1) : d1126 pattern ≤ (1 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18059 pattern childGuard
    simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18060 pattern childGuard
    simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18062 (pattern : Twelve) (guard : d1865 pattern = 1) : d1142 pattern ≤ (1 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18061 pattern childGuard
    simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18063 (pattern : Twelve) (guard : d1865 pattern = 1) : d1157 pattern ≤ (1 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18058 pattern childGuard
    simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18062 pattern childGuard
    simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18064 (pattern : Twelve) (guard : d1865 pattern = 1) : d1166 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18054 pattern childGuard
    simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18063 pattern childGuard
    simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18065 (pattern : Twelve) (guard : d1865 pattern = 1) : d1167 pattern ≤ (1 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18047 pattern childGuard
    simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18066 (pattern : Twelve) (guard : d1865 pattern = 1) : d1174 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18064 pattern childGuard
    simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18065 pattern childGuard
    simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18067 (pattern : Twelve) (guard : d1865 pattern = 1) : d1177 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18049 pattern childGuard
    simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18066 pattern childGuard
    simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18068 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18042 pattern childGuard
    simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18069 (pattern : Twelve) (guard : d1865 pattern = 1) : d1158 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18068 pattern childGuard
    simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18044 pattern childGuard
    simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18070 (pattern : Twelve) (guard : d1865 pattern = 1) : d1168 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18069 pattern childGuard
    simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18047 pattern childGuard
    simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18071 (pattern : Twelve) (guard : d1865 pattern = 1) : d1144 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18051 pattern childGuard
    simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18072 (pattern : Twelve) (guard : d1865 pattern = 1) : d1159 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18071 pattern childGuard
    simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18053 pattern childGuard
    simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18073 (pattern : Twelve) (guard : d1865 pattern = 1) : d1169 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18072 pattern childGuard
    simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18063 pattern childGuard
    simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18074 (pattern : Twelve) (guard : d1865 pattern = 1) : d1175 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18073 pattern childGuard
    simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18065 pattern childGuard
    simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18075 (pattern : Twelve) (guard : d1865 pattern = 1) : d1178 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18070 pattern childGuard
    simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18074 pattern childGuard
    simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18076 (pattern : Twelve) (guard : d1865 pattern = 1) : d1180 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18067 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18075 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18077 (pattern : Twelve) (guard : d1865 pattern = 1) : d1181 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18076 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18075 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18078 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18026 pattern childGuard
    simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18079 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (1 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12399 pattern childGuard
    simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18078 pattern childGuard
    simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18080 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (1 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18079 pattern childGuard
    simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18081 (pattern : Twelve) (guard : d1865 pattern = 1) : d1114 pattern ≤ (1 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17912 pattern childGuard
    simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18082 (pattern : Twelve) (guard : d1865 pattern = 1) : d1127 pattern ≤ (1 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18081 pattern childGuard
    simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17945 pattern childGuard
    simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18083 (pattern : Twelve) (guard : d1865 pattern = 1) : d1145 pattern ≤ (1 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18082 pattern childGuard
    simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18084 (pattern : Twelve) (guard : d1865 pattern = 1) : d1160 pattern ≤ (1 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18080 pattern childGuard
    simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18083 pattern childGuard
    simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18085 (pattern : Twelve) (guard : d1865 pattern = 1) : d1115 pattern ≤ (1 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18055 pattern childGuard
    simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18086 (pattern : Twelve) (guard : d1865 pattern = 1) : d1128 pattern ≤ (1 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18085 pattern childGuard
    simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18036 pattern childGuard
    simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18087 (pattern : Twelve) (guard : d1865 pattern = 1) : d1146 pattern ≤ (1 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18086 pattern childGuard
    simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18088 (pattern : Twelve) (guard : d1865 pattern = 1) : d1147 pattern ≤ (1 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18082 pattern childGuard
    simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18089 (pattern : Twelve) (guard : d1865 pattern = 1) : d1161 pattern ≤ (1 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18087 pattern childGuard
    simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18088 pattern childGuard
    simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18090 (pattern : Twelve) (guard : d1865 pattern = 1) : d1170 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18084 pattern childGuard
    simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18089 pattern childGuard
    simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18091 (pattern : Twelve) (guard : d1865 pattern = 1) : d1116 pattern ≤ (1 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18026 pattern childGuard
    simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12333 pattern childGuard
    simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18092 (pattern : Twelve) (guard : d1865 pattern = 1) : d1129 pattern ≤ (1 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18085 pattern childGuard
    simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18091 pattern childGuard
    simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18093 (pattern : Twelve) (guard : d1865 pattern = 1) : d1148 pattern ≤ (1 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18092 pattern childGuard
    simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18094 (pattern : Twelve) (guard : d1865 pattern = 1) : d1149 pattern ≤ (1 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12423 pattern childGuard
    simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18082 pattern childGuard
    simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18095 (pattern : Twelve) (guard : d1865 pattern = 1) : d1162 pattern ≤ (1 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18093 pattern childGuard
    simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18094 pattern childGuard
    simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18096 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (1 : Int) + d117 pattern := by
  omega
theorem c18097 (pattern : Twelve) (guard : d1865 pattern = 1) : d1107 pattern ≤ (1 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18096 pattern childGuard
    simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12332 pattern childGuard
    simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18098 (pattern : Twelve) (guard : d1865 pattern = 1) : d1117 pattern ≤ (1 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18097 pattern childGuard
    simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18099 (pattern : Twelve) (guard : d1865 pattern = 1) : d1130 pattern ≤ (1 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18016 pattern childGuard
    simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18098 pattern childGuard
    simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18100 (pattern : Twelve) (guard : d1865 pattern = 1) : d1150 pattern ≤ (1 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18099 pattern childGuard
    simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18101 (pattern : Twelve) (guard : d1865 pattern = 1) : d1131 pattern ≤ (1 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17945 pattern childGuard
    simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18102 (pattern : Twelve) (guard : d1865 pattern = 1) : d1151 pattern ≤ (1 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12436 pattern childGuard
    simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18101 pattern childGuard
    simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18103 (pattern : Twelve) (guard : d1865 pattern = 1) : d1163 pattern ≤ (1 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18100 pattern childGuard
    simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18102 pattern childGuard
    simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18104 (pattern : Twelve) (guard : d1865 pattern = 1) : d1171 pattern ≤ (1 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18095 pattern childGuard
    simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18103 pattern childGuard
    simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18105 (pattern : Twelve) (guard : d1865 pattern = 1) : d1172 pattern ≤ (1 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18089 pattern childGuard
    simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18106 (pattern : Twelve) (guard : d1865 pattern = 1) : d1176 pattern ≤ (1 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18104 pattern childGuard
    simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18105 pattern childGuard
    simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18107 (pattern : Twelve) (guard : d1865 pattern = 1) : d1179 pattern ≤ (1 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18090 pattern childGuard
    simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18106 pattern childGuard
    simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18108 (pattern : Twelve) (guard : d1865 pattern = 1) : d1182 pattern ≤ (1 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18077 pattern childGuard
    simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18107 pattern childGuard
    simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18109 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (1 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11211 pattern childGuard
    simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12397 pattern childGuard
    simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18110 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18109 pattern childGuard
    simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18111 (pattern : Twelve) (guard : d1865 pattern = 1) : d1505 pattern ≤ (1 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18110 pattern childGuard
    simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18112 (pattern : Twelve) (guard : d1865 pattern = 1) : d1517 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18030 pattern childGuard
    simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18111 pattern childGuard
    simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18113 (pattern : Twelve) (guard : d1865 pattern = 1) : d1518 pattern ≤ (1 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18114 (pattern : Twelve) (guard : d1865 pattern = 1) : d1532 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18112 pattern childGuard
    simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18113 pattern childGuard
    simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18115 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (1 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11266 pattern childGuard
    simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12420 pattern childGuard
    simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18116 (pattern : Twelve) (guard : d1865 pattern = 1) : d1495 pattern ≤ (1 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18109 pattern childGuard
    simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18115 pattern childGuard
    simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18117 (pattern : Twelve) (guard : d1865 pattern = 1) : d1496 pattern ≤ (1 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1496, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18118 (pattern : Twelve) (guard : d1865 pattern = 1) : d1506 pattern ≤ (1 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18116 pattern childGuard
    simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18117 pattern childGuard
    simpa only [d1506, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18119 (pattern : Twelve) (guard : d1865 pattern = 1) : d1519 pattern ≤ (1 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18118 pattern childGuard
    simpa only [d1519, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18120 (pattern : Twelve) (guard : d1865 pattern = 1) : d1507 pattern ≤ (1 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18031 pattern childGuard
    simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17902 pattern childGuard
    simpa only [d1507, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18121 (pattern : Twelve) (guard : d1865 pattern = 1) : d1520 pattern ≤ (1 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18120 pattern childGuard
    simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1520, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18122 (pattern : Twelve) (guard : d1865 pattern = 1) : d1533 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18119 pattern childGuard
    simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18121 pattern childGuard
    simpa only [d1533, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18123 (pattern : Twelve) (guard : d1865 pattern = 1) : d1541 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18114 pattern childGuard
    simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18122 pattern childGuard
    simpa only [d1541, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18124 (pattern : Twelve) (guard : d1865 pattern = 1) : d1521 pattern ≤ (1 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18111 pattern childGuard
    simpa only [d1521, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18125 (pattern : Twelve) (guard : d1865 pattern = 1) : d1534 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18124 pattern childGuard
    simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18113 pattern childGuard
    simpa only [d1534, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18126 (pattern : Twelve) (guard : d1865 pattern = 1) : d1542 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18125 pattern childGuard
    simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18122 pattern childGuard
    simpa only [d1542, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18127 (pattern : Twelve) (guard : d1865 pattern = 1) : d1548 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18123 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18126 pattern childGuard
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18128 (pattern : Twelve) (guard : d1865 pattern = 1) : d1497 pattern ≤ (1 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12421 pattern childGuard
    simpa only [d1497, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18129 (pattern : Twelve) (guard : d1865 pattern = 1) : d1508 pattern ≤ (1 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18116 pattern childGuard
    simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18128 pattern childGuard
    simpa only [d1508, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18130 (pattern : Twelve) (guard : d1865 pattern = 1) : d1522 pattern ≤ (1 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18129 pattern childGuard
    simpa only [d1522, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18131 (pattern : Twelve) (guard : d1865 pattern = 1) : d1523 pattern ≤ (1 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18031 pattern childGuard
    simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1523, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18132 (pattern : Twelve) (guard : d1865 pattern = 1) : d1535 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18130 pattern childGuard
    simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18131 pattern childGuard
    simpa only [d1535, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18133 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (1 : Int) + d15 pattern := by
  omega
theorem c18134 (pattern : Twelve) (guard : d1865 pattern = 1) : d1493 pattern ≤ (1 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18133 pattern childGuard
    simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d1493, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18135 (pattern : Twelve) (guard : d1865 pattern = 1) : d1498 pattern ≤ (1 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18115 pattern childGuard
    simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18134 pattern childGuard
    simpa only [d1498, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18136 (pattern : Twelve) (guard : d1865 pattern = 1) : d1509 pattern ≤ (1 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18135 pattern childGuard
    simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12435 pattern childGuard
    simpa only [d1509, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18137 (pattern : Twelve) (guard : d1865 pattern = 1) : d1524 pattern ≤ (1 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18136 pattern childGuard
    simpa only [d1524, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18138 (pattern : Twelve) (guard : d1865 pattern = 1) : d1510 pattern ≤ (1 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18059 pattern childGuard
    simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17945 pattern childGuard
    simpa only [d1510, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18139 (pattern : Twelve) (guard : d1865 pattern = 1) : d1525 pattern ≤ (1 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18138 pattern childGuard
    simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1525, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18140 (pattern : Twelve) (guard : d1865 pattern = 1) : d1536 pattern ≤ (1 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18137 pattern childGuard
    simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18139 pattern childGuard
    simpa only [d1536, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18141 (pattern : Twelve) (guard : d1865 pattern = 1) : d1543 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18132 pattern childGuard
    simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18140 pattern childGuard
    simpa only [d1543, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18142 (pattern : Twelve) (guard : d1865 pattern = 1) : d1544 pattern ≤ (1 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18122 pattern childGuard
    simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1544, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18143 (pattern : Twelve) (guard : d1865 pattern = 1) : d1549 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18141 pattern childGuard
    simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18142 pattern childGuard
    simpa only [d1549, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18144 (pattern : Twelve) (guard : d1865 pattern = 1) : d1551 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18127 pattern childGuard
    simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18143 pattern childGuard
    simpa only [d1551, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18145 (pattern : Twelve) (guard : d1865 pattern = 1) : d1552 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18126 pattern childGuard
    simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18143 pattern childGuard
    simpa only [d1552, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18146 (pattern : Twelve) (guard : d1865 pattern = 1) : d1554 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18144 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18145 pattern childGuard
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18147 (pattern : Twelve) (guard : d1865 pattern = 1) : d1555 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18146 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18145 pattern childGuard
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18148 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (1 : Int) + d11 pattern := by
  omega
theorem c18149 (pattern : Twelve) (guard : d1865 pattern = 1) : d1494 pattern ≤ (1 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18148 pattern childGuard
    simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12517 pattern childGuard
    simpa only [d1865, d1494, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18150 (pattern : Twelve) (guard : d1865 pattern = 1) : d1499 pattern ≤ (1 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18109 pattern childGuard
    simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18149 pattern childGuard
    simpa only [d1499, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18151 (pattern : Twelve) (guard : d1865 pattern = 1) : d1500 pattern ≤ (1 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18149 pattern childGuard
    simpa only [d1500, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18152 (pattern : Twelve) (guard : d1865 pattern = 1) : d1511 pattern ≤ (1 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18150 pattern childGuard
    simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18151 pattern childGuard
    simpa only [d1511, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18153 (pattern : Twelve) (guard : d1865 pattern = 1) : d1526 pattern ≤ (1 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18152 pattern childGuard
    simpa only [d1526, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18154 (pattern : Twelve) (guard : d1865 pattern = 1) : d1537 pattern ≤ (1 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18153 pattern childGuard
    simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18113 pattern childGuard
    simpa only [d1537, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18155 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (1 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18109 pattern childGuard
    simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12421 pattern childGuard
    simpa only [d1111, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18156 (pattern : Twelve) (guard : d1865 pattern = 1) : d1512 pattern ≤ (1 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18155 pattern childGuard
    simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18117 pattern childGuard
    simpa only [d1512, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18157 (pattern : Twelve) (guard : d1865 pattern = 1) : d1527 pattern ≤ (1 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18156 pattern childGuard
    simpa only [d1527, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18158 (pattern : Twelve) (guard : d1865 pattern = 1) : d1538 pattern ≤ (1 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18157 pattern childGuard
    simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18121 pattern childGuard
    simpa only [d1538, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18159 (pattern : Twelve) (guard : d1865 pattern = 1) : d1545 pattern ≤ (1 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18154 pattern childGuard
    simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18158 pattern childGuard
    simpa only [d1545, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18160 (pattern : Twelve) (guard : d1865 pattern = 1) : d1501 pattern ≤ (1 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12398 pattern childGuard
    simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18134 pattern childGuard
    simpa only [d1501, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18161 (pattern : Twelve) (guard : d1865 pattern = 1) : d1513 pattern ≤ (1 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18155 pattern childGuard
    simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18160 pattern childGuard
    simpa only [d1513, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18162 (pattern : Twelve) (guard : d1865 pattern = 1) : d1528 pattern ≤ (1 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18161 pattern childGuard
    simpa only [d1528, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18163 (pattern : Twelve) (guard : d1865 pattern = 1) : d1502 pattern ≤ (1 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d1502, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18164 (pattern : Twelve) (guard : d1865 pattern = 1) : d1514 pattern ≤ (1 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18031 pattern childGuard
    simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18163 pattern childGuard
    simpa only [d1514, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18165 (pattern : Twelve) (guard : d1865 pattern = 1) : d1529 pattern ≤ (1 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18164 pattern childGuard
    simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1529, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18166 (pattern : Twelve) (guard : d1865 pattern = 1) : d1539 pattern ≤ (1 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18162 pattern childGuard
    simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18165 pattern childGuard
    simpa only [d1539, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18167 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (1 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18115 pattern childGuard
    simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1112, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18168 (pattern : Twelve) (guard : d1865 pattern = 1) : d1503 pattern ≤ (1 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18134 pattern childGuard
    simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1503, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18169 (pattern : Twelve) (guard : d1865 pattern = 1) : d1515 pattern ≤ (1 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18167 pattern childGuard
    simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18168 pattern childGuard
    simpa only [d1515, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18170 (pattern : Twelve) (guard : d1865 pattern = 1) : d1530 pattern ≤ (1 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12340 pattern childGuard
    simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18169 pattern childGuard
    simpa only [d1530, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18171 (pattern : Twelve) (guard : d1865 pattern = 1) : d1504 pattern ≤ (1 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17916 pattern childGuard
    simpa only [d1504, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18172 (pattern : Twelve) (guard : d1865 pattern = 1) : d1516 pattern ≤ (1 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18171 pattern childGuard
    simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18017 pattern childGuard
    simpa only [d1516, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18173 (pattern : Twelve) (guard : d1865 pattern = 1) : d1531 pattern ≤ (1 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18172 pattern childGuard
    simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1531, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18174 (pattern : Twelve) (guard : d1865 pattern = 1) : d1540 pattern ≤ (1 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18170 pattern childGuard
    simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18173 pattern childGuard
    simpa only [d1540, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18175 (pattern : Twelve) (guard : d1865 pattern = 1) : d1546 pattern ≤ (1 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18166 pattern childGuard
    simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18174 pattern childGuard
    simpa only [d1546, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18176 (pattern : Twelve) (guard : d1865 pattern = 1) : d1547 pattern ≤ (1 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18158 pattern childGuard
    simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1547, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18177 (pattern : Twelve) (guard : d1865 pattern = 1) : d1550 pattern ≤ (1 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18175 pattern childGuard
    simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18176 pattern childGuard
    simpa only [d1550, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18178 (pattern : Twelve) (guard : d1865 pattern = 1) : d1553 pattern ≤ (1 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18159 pattern childGuard
    simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18177 pattern childGuard
    simpa only [d1553, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18179 (pattern : Twelve) (guard : d1865 pattern = 1) : d1556 pattern ≤ (1 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18147 pattern childGuard
    simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18178 pattern childGuard
    simpa only [d1556, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18180 (pattern : Twelve) (guard : d1865 pattern = 1) : d1753 pattern ≤ (1 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18149 pattern childGuard
    simpa only [d1753, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18181 (pattern : Twelve) (guard : d1865 pattern = 1) : d1754 pattern ≤ (1 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1754, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18182 (pattern : Twelve) (guard : d1865 pattern = 1) : d1763 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18180 pattern childGuard
    simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18181 pattern childGuard
    simpa only [d1763, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18183 (pattern : Twelve) (guard : d1865 pattern = 1) : d1745 pattern ≤ (1 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18149 pattern childGuard
    simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d1745, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18184 (pattern : Twelve) (guard : d1865 pattern = 1) : d1746 pattern ≤ (1 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18149 pattern childGuard
    simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1746, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18185 (pattern : Twelve) (guard : d1865 pattern = 1) : d1749 pattern ≤ (1 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18183 pattern childGuard
    simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18184 pattern childGuard
    simpa only [d1749, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18186 (pattern : Twelve) (guard : d1865 pattern = 1) : d1755 pattern ≤ (1 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18120 pattern childGuard
    simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18185 pattern childGuard
    simpa only [d1755, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18187 (pattern : Twelve) (guard : d1865 pattern = 1) : d1764 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18186 pattern childGuard
    simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18139 pattern childGuard
    simpa only [d1764, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18188 (pattern : Twelve) (guard : d1865 pattern = 1) : d1770 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18182 pattern childGuard
    simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18187 pattern childGuard
    simpa only [d1770, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18189 (pattern : Twelve) (guard : d1865 pattern = 1) : d1756 pattern ≤ (1 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18031 pattern childGuard
    simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18183 pattern childGuard
    simpa only [d1756, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18190 (pattern : Twelve) (guard : d1865 pattern = 1) : d1757 pattern ≤ (1 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18059 pattern childGuard
    simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1757, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18191 (pattern : Twelve) (guard : d1865 pattern = 1) : d1765 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18189 pattern childGuard
    simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18190 pattern childGuard
    simpa only [d1765, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18192 (pattern : Twelve) (guard : d1865 pattern = 1) : d1747 pattern ≤ (1 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17916 pattern childGuard
    simpa only [d1747, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18193 (pattern : Twelve) (guard : d1865 pattern = 1) : d1750 pattern ≤ (1 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18192 pattern childGuard
    simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18017 pattern childGuard
    simpa only [d1750, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18194 (pattern : Twelve) (guard : d1865 pattern = 1) : d1758 pattern ≤ (1 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18138 pattern childGuard
    simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18193 pattern childGuard
    simpa only [d1758, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18195 (pattern : Twelve) (guard : d1865 pattern = 1) : d1759 pattern ≤ (1 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18060 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1759, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18196 (pattern : Twelve) (guard : d1865 pattern = 1) : d1766 pattern ≤ (1 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18194 pattern childGuard
    simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18195 pattern childGuard
    simpa only [d1766, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18197 (pattern : Twelve) (guard : d1865 pattern = 1) : d1771 pattern ≤ (1 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18191 pattern childGuard
    simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18196 pattern childGuard
    simpa only [d1771, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18198 (pattern : Twelve) (guard : d1865 pattern = 1) : d1772 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18187 pattern childGuard
    simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1772, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18199 (pattern : Twelve) (guard : d1865 pattern = 1) : d1775 pattern ≤ (1 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18197 pattern childGuard
    simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18198 pattern childGuard
    simpa only [d1775, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
