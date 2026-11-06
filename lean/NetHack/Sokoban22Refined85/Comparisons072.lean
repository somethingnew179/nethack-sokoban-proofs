/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons071
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10080 (p : Pattern) (guard : d0 p = 1) : d1152 p ≤ (0 : Int) + d346 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10081 (p : Pattern) (guard : d4397 p = 1) : d1153 p ≤ (0 : Int) + d949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1153, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9319 p hg
    simpa only [d4397, d1153, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1153, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10080 p hg
    simpa only [d4397, d1153, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10082 (p : Pattern) (guard : d4397 p = 1) : d1155 p ≤ (0 : Int) + d951 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1155, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9799 p hg
    simpa only [d4397, d1155, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1155, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d4397, d1155, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10083 (p : Pattern) (guard : d4397 p = 1) : d1156 p ≤ (0 : Int) + d952 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1156, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10081 p hg
    simpa only [d1156, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1156, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10082 p hg
    simpa only [d1156, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10084 (p : Pattern) (guard : d0 p = 1) : d1158 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10085 (p : Pattern) (guard : d4397 p = 1) : d1159 p ≤ (0 : Int) + d953 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1159, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9803 p hg
    simpa only [d4397, d1159, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1159, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10084 p hg
    simpa only [d4397, d1159, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10086 (p : Pattern) (guard : d4397 p = 1) : d1161 p ≤ (0 : Int) + d954 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1161, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9332 p hg
    simpa only [d4397, d1161, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1161, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d4397, d1161, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10087 (p : Pattern) (guard : d4397 p = 1) : d1162 p ≤ (0 : Int) + d955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1162, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d1162, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1162, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d1162, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10088 (p : Pattern) (guard : d4397 p = 1) : d1163 p ≤ (0 : Int) + d956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1163, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10083 p hg
    simpa only [d1163, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1163, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d1163, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10089 (p : Pattern) (guard : d0 p = 1) : d1165 p ≤ (0 : Int) + d369 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10090 (p : Pattern) (guard : d4397 p = 1) : d1166 p ≤ (0 : Int) + d957 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1166, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9808 p hg
    simpa only [d4397, d1166, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1166, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d4397, d1166, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10091 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10092 (p : Pattern) (guard : d4397 p = 1) : d1168 p ≤ (0 : Int) + d958 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1168, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9812 p hg
    simpa only [d4397, d1168, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1168, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d4397, d1168, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10093 (p : Pattern) (guard : d4397 p = 1) : d1169 p ≤ (0 : Int) + d959 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1169, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d1169, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1169, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d1169, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10094 (p : Pattern) (guard : d0 p = 1) : d1171 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10095 (p : Pattern) (guard : d4397 p = 1) : d1172 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1172, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d4397, d1172, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1172, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d4397, d1172, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10096 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10097 (p : Pattern) (guard : d4397 p = 1) : d1173 p ≤ (0 : Int) + d961 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1173, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9820 p hg
    simpa only [d4397, d1173, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1173, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d4397, d1173, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10098 (p : Pattern) (guard : d4397 p = 1) : d1174 p ≤ (0 : Int) + d962 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1174, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10095 p hg
    simpa only [d1174, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1174, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10097 p hg
    simpa only [d1174, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10099 (p : Pattern) (guard : d4397 p = 1) : d1175 p ≤ (0 : Int) + d963 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1175, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10093 p hg
    simpa only [d1175, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1175, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10098 p hg
    simpa only [d1175, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10100 (p : Pattern) (guard : d4397 p = 1) : d1176 p ≤ (0 : Int) + d964 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1176, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d1176, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1176, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10099 p hg
    simpa only [d1176, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10101 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10102 (p : Pattern) (guard : d4397 p = 1) : d1178 p ≤ (0 : Int) + d965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1178, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9339 p hg
    simpa only [d4397, d1178, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1178, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10101 p hg
    simpa only [d4397, d1178, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10103 (p : Pattern) (guard : d4397 p = 1) : d1179 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1179, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4397, d1179, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1179, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4397, d1179, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10104 (p : Pattern) (guard : d4397 p = 1) : d1180 p ≤ (0 : Int) + d967 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1180, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10102 p hg
    simpa only [d1180, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1180, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1180, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10105 (p : Pattern) (guard : d4397 p = 1) : d1182 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1182, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9830 p hg
    simpa only [d4397, d1182, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1182, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d1182, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10106 (p : Pattern) (guard : d4397 p = 1) : d1183 p ≤ (0 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1183, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10105 p hg
    simpa only [d1183, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1183, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1183, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10107 (p : Pattern) (guard : d4397 p = 1) : d1184 p ≤ (0 : Int) + d970 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1184, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10104 p hg
    simpa only [d1184, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1184, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1184, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10108 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10109 (p : Pattern) (guard : d4397 p = 1) : d1186 p ≤ (0 : Int) + d971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1186, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9835 p hg
    simpa only [d4397, d1186, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1186, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d4397, d1186, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10110 (p : Pattern) (guard : d4397 p = 1) : d1182 p ≤ (0 : Int) + d972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1182, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4397, d1182, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1182, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d1182, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10111 (p : Pattern) (guard : d4397 p = 1) : d1187 p ≤ (0 : Int) + d973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1187, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10109 p hg
    simpa only [d1187, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1187, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1187, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10112 (p : Pattern) (guard : d4397 p = 1) : d1188 p ≤ (0 : Int) + d972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9838 p hg
    simpa only [d4397, d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1188, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10113 (p : Pattern) (guard : d4397 p = 1) : d1189 p ≤ (0 : Int) + d974 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10112 p hg
    simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1189, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10114 (p : Pattern) (guard : d4397 p = 1) : d1190 p ≤ (0 : Int) + d975 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1190, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10111 p hg
    simpa only [d1190, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1190, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d1190, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10115 (p : Pattern) (guard : d4397 p = 1) : d1191 p ≤ (0 : Int) + d976 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1191, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10107 p hg
    simpa only [d1191, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1191, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10114 p hg
    simpa only [d1191, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10116 (p : Pattern) (guard : d4397 p = 1) : d1192 p ≤ (0 : Int) + d977 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1192, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d1192, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1192, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10115 p hg
    simpa only [d1192, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10117 (p : Pattern) (guard : d0 p = 1) : d1193 p ≤ (0 : Int) + d389 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10118 (p : Pattern) (guard : d4397 p = 1) : d1194 p ≤ (0 : Int) + d978 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1194, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9353 p hg
    simpa only [d4397, d1194, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1194, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d4397, d1194, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10119 (p : Pattern) (guard : d4397 p = 1) : d1195 p ≤ (0 : Int) + d979 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1195, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10118 p hg
    simpa only [d1195, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1195, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1195, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10120 (p : Pattern) (guard : d4397 p = 1) : d1196 p ≤ (0 : Int) + d980 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1196, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10119 p hg
    simpa only [d1196, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1196, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1196, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10121 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10122 (p : Pattern) (guard : d4397 p = 1) : d1198 p ≤ (0 : Int) + d981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1198, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9849 p hg
    simpa only [d4397, d1198, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1198, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10121 p hg
    simpa only [d4397, d1198, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10123 (p : Pattern) (guard : d4397 p = 1) : d1199 p ≤ (0 : Int) + d982 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1199, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10122 p hg
    simpa only [d1199, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1199, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1199, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10124 (p : Pattern) (guard : d4397 p = 1) : d1200 p ≤ (0 : Int) + d983 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1200, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10123 p hg
    simpa only [d1200, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1200, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d1200, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10125 (p : Pattern) (guard : d4397 p = 1) : d1201 p ≤ (0 : Int) + d984 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1201, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10120 p hg
    simpa only [d1201, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1201, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10124 p hg
    simpa only [d1201, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10126 (p : Pattern) (guard : d4397 p = 1) : d1202 p ≤ (0 : Int) + d985 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1202, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9361 p hg
    simpa only [d4397, d1202, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1202, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d1202, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10127 (p : Pattern) (guard : d4397 p = 1) : d1203 p ≤ (0 : Int) + d986 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1203, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10126 p hg
    simpa only [d1203, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1203, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d1203, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10128 (p : Pattern) (guard : d4397 p = 1) : d1204 p ≤ (0 : Int) + d987 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1204, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10127 p hg
    simpa only [d1204, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1204, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d1204, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10129 (p : Pattern) (guard : d4397 p = 1) : d1205 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1205, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10128 p hg
    simpa only [d1205, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1205, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8107 p hg
    simpa only [d1205, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10130 (p : Pattern) (guard : d4397 p = 1) : d1206 p ≤ (0 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1206, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10125 p hg
    simpa only [d1206, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1206, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10129 p hg
    simpa only [d1206, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10131 (p : Pattern) (guard : d4397 p = 1) : d1207 p ≤ (0 : Int) + d990 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1207, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10116 p hg
    simpa only [d1207, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1207, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10130 p hg
    simpa only [d1207, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10132 (p : Pattern) (guard : d0 p = 1) : d1185 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10133 (p : Pattern) (guard : d4397 p = 1) : d1209 p ≤ (0 : Int) + d991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1209, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9369 p hg
    simpa only [d4397, d1209, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1209, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10132 p hg
    simpa only [d4397, d1209, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10134 (p : Pattern) (guard : d4397 p = 1) : d1210 p ≤ (0 : Int) + d992 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1210, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9859 p hg
    simpa only [d4397, d1210, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1210, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4397, d1210, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10135 (p : Pattern) (guard : d4397 p = 1) : d1211 p ≤ (0 : Int) + d993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1211, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10133 p hg
    simpa only [d1211, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1211, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10134 p hg
    simpa only [d1211, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10136 (p : Pattern) (guard : d0 p = 1) : d1158 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10137 (p : Pattern) (guard : d4397 p = 1) : d1213 p ≤ (0 : Int) + d994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1213, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9863 p hg
    simpa only [d4397, d1213, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1213, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10136 p hg
    simpa only [d4397, d1213, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10138 (p : Pattern) (guard : d4397 p = 1) : d1214 p ≤ (0 : Int) + d995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1214, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10137 p hg
    simpa only [d1214, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1214, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d1214, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10139 (p : Pattern) (guard : d4397 p = 1) : d1215 p ≤ (0 : Int) + d996 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1215, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10135 p hg
    simpa only [d1215, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1215, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10138 p hg
    simpa only [d1215, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10140 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10141 (p : Pattern) (guard : d4397 p = 1) : d1216 p ≤ (0 : Int) + d997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1216, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9868 p hg
    simpa only [d4397, d1216, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1216, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d4397, d1216, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10142 (p : Pattern) (guard : d4397 p = 1) : d1182 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1182, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d4397, d1182, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1182, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d1182, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10143 (p : Pattern) (guard : d4397 p = 1) : d1217 p ≤ (0 : Int) + d998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1217, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10141 p hg
    simpa only [d1217, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1217, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10142 p hg
    simpa only [d1217, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10144 (p : Pattern) (guard : d4397 p = 1) : d1218 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1218, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9871 p hg
    simpa only [d4397, d1218, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1218, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d4397, d1218, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10145 (p : Pattern) (guard : d4397 p = 1) : d1219 p ≤ (0 : Int) + d962 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1219, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10144 p hg
    simpa only [d1219, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1219, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10097 p hg
    simpa only [d1219, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10146 (p : Pattern) (guard : d4397 p = 1) : d1220 p ≤ (0 : Int) + d999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1220, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10143 p hg
    simpa only [d1220, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1220, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10145 p hg
    simpa only [d1220, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10147 (p : Pattern) (guard : d4397 p = 1) : d1221 p ≤ (0 : Int) + d1000 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1221, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10139 p hg
    simpa only [d1221, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1221, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10146 p hg
    simpa only [d1221, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10148 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10149 (p : Pattern) (guard : d4397 p = 1) : d1222 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1222, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d4397, d1222, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1222, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10148 p hg
    simpa only [d4397, d1222, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10150 (p : Pattern) (guard : d4397 p = 1) : d1223 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1223, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10149 p hg
    simpa only [d1223, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1223, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1223, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10151 (p : Pattern) (guard : d4397 p = 1) : d1224 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1224, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10150 p hg
    simpa only [d1224, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1224, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1224, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10152 (p : Pattern) (guard : d0 p = 1) : d1181 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10153 (p : Pattern) (guard : d4397 p = 1) : d1225 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1225, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9827 p hg
    simpa only [d4397, d1225, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1225, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4397, d1225, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10154 (p : Pattern) (guard : d4397 p = 1) : d1226 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1226, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10153 p hg
    simpa only [d1226, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1226, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1226, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10155 (p : Pattern) (guard : d4397 p = 1) : d1227 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1227, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10154 p hg
    simpa only [d1227, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1227, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d1227, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10156 (p : Pattern) (guard : d4397 p = 1) : d1228 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1228, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10151 p hg
    simpa only [d1228, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1228, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d1228, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10157 (p : Pattern) (guard : d4397 p = 1) : d1229 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1229, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10147 p hg
    simpa only [d1229, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1229, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d1229, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10158 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10159 (p : Pattern) (guard : d4397 p = 1) : d1230 p ≤ (0 : Int) + d1008 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1230, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9391 p hg
    simpa only [d4397, d1230, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1230, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10158 p hg
    simpa only [d4397, d1230, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10160 (p : Pattern) (guard : d4397 p = 1) : d1231 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1231, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10159 p hg
    simpa only [d1231, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1231, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1231, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10161 (p : Pattern) (guard : d4397 p = 1) : d1232 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1232, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10160 p hg
    simpa only [d1232, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1232, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1232, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10162 (p : Pattern) (guard : d4397 p = 1) : d1233 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1233, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10161 p hg
    simpa only [d1233, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1233, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d1233, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10163 (p : Pattern) (guard : d4397 p = 1) : d1234 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1234, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10162 p hg
    simpa only [d1234, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1234, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1234, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10164 (p : Pattern) (guard : d4397 p = 1) : d1235 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1235, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10157 p hg
    simpa only [d1235, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1235, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10163 p hg
    simpa only [d1235, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10165 (p : Pattern) (guard : d4397 p = 1) : d1236 p ≤ (0 : Int) + d1014 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1236, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10131 p hg
    simpa only [d1236, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1236, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10164 p hg
    simpa only [d1236, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10166 (p : Pattern) (guard : d0 p = 1) : d1154 p ≤ (0 : Int) + d355 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10167 (p : Pattern) (guard : d4397 p = 1) : d1238 p ≤ (0 : Int) + d1015 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1238, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9401 p hg
    simpa only [d4397, d1238, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1238, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10166 p hg
    simpa only [d4397, d1238, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10168 (p : Pattern) (guard : d4397 p = 1) : d1239 p ≤ (0 : Int) + d1016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1239, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9891 p hg
    simpa only [d4397, d1239, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1239, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d4397, d1239, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10169 (p : Pattern) (guard : d4397 p = 1) : d1240 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1240, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10167 p hg
    simpa only [d1240, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1240, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10168 p hg
    simpa only [d1240, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10170 (p : Pattern) (guard : d0 p = 1) : d1158 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10171 (p : Pattern) (guard : d4397 p = 1) : d1242 p ≤ (0 : Int) + d1018 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1242, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9895 p hg
    simpa only [d4397, d1242, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1242, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10170 p hg
    simpa only [d4397, d1242, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10172 (p : Pattern) (guard : d4397 p = 1) : d1243 p ≤ (0 : Int) + d1019 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1243, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10171 p hg
    simpa only [d1243, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1243, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d1243, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10173 (p : Pattern) (guard : d4397 p = 1) : d1244 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1244, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10169 p hg
    simpa only [d1244, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1244, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10172 p hg
    simpa only [d1244, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10174 (p : Pattern) (guard : d0 p = 1) : d1167 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10175 (p : Pattern) (guard : d4397 p = 1) : d1245 p ≤ (0 : Int) + d1021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1245, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9900 p hg
    simpa only [d4397, d1245, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1245, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10174 p hg
    simpa only [d4397, d1245, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10176 (p : Pattern) (guard : d4397 p = 1) : d1246 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1246, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9816 p hg
    simpa only [d4397, d1246, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1246, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4397, d1246, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10177 (p : Pattern) (guard : d4397 p = 1) : d1247 p ≤ (0 : Int) + d1022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1247, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10175 p hg
    simpa only [d1247, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1247, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10176 p hg
    simpa only [d1247, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10178 (p : Pattern) (guard : d4397 p = 1) : d1248 p ≤ (0 : Int) + d1023 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1248, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10177 p hg
    simpa only [d1248, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1248, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10145 p hg
    simpa only [d1248, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10179 (p : Pattern) (guard : d4397 p = 1) : d1249 p ≤ (0 : Int) + d1024 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1249, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10173 p hg
    simpa only [d1249, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1249, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10178 p hg
    simpa only [d1249, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10180 (p : Pattern) (guard : d0 p = 1) : d1177 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10181 (p : Pattern) (guard : d4397 p = 1) : d1250 p ≤ (0 : Int) + d1025 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1250, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d4397, d1250, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1250, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10180 p hg
    simpa only [d4397, d1250, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10182 (p : Pattern) (guard : d4397 p = 1) : d1251 p ≤ (0 : Int) + d1026 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1251, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10181 p hg
    simpa only [d1251, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1251, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1251, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10183 (p : Pattern) (guard : d4397 p = 1) : d1252 p ≤ (0 : Int) + d1027 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1252, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10182 p hg
    simpa only [d1252, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1252, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1252, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10184 (p : Pattern) (guard : d4397 p = 1) : d1253 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1253, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9910 p hg
    simpa only [d4397, d1253, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1253, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4397, d1253, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10185 (p : Pattern) (guard : d4397 p = 1) : d1254 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1254, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10184 p hg
    simpa only [d1254, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1254, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d1254, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10186 (p : Pattern) (guard : d4397 p = 1) : d1255 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1255, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10185 p hg
    simpa only [d1255, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1255, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d1255, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10187 (p : Pattern) (guard : d4397 p = 1) : d1256 p ≤ (0 : Int) + d1028 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1256, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10183 p hg
    simpa only [d1256, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1256, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10186 p hg
    simpa only [d1256, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10188 (p : Pattern) (guard : d4397 p = 1) : d1257 p ≤ (0 : Int) + d1029 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1257, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10179 p hg
    simpa only [d1257, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1257, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10187 p hg
    simpa only [d1257, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10189 (p : Pattern) (guard : d4397 p = 1) : d1258 p ≤ (0 : Int) + d1030 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1258, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10115 p hg
    simpa only [d1258, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1258, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10129 p hg
    simpa only [d1258, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10190 (p : Pattern) (guard : d4397 p = 1) : d1259 p ≤ (0 : Int) + d1031 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1259, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10188 p hg
    simpa only [d1259, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1259, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10189 p hg
    simpa only [d1259, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10191 (p : Pattern) (guard : d4397 p = 1) : d1179 p ≤ (0 : Int) + d992 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1179, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9918 p hg
    simpa only [d4397, d1179, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1179, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4397, d1179, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10192 (p : Pattern) (guard : d4397 p = 1) : d1195 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1195, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10118 p hg
    simpa only [d1195, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1195, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10191 p hg
    simpa only [d1195, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10193 (p : Pattern) (guard : d4397 p = 1) : d1260 p ≤ (0 : Int) + d1033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1260, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10192 p hg
    simpa only [d1260, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1260, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10138 p hg
    simpa only [d1260, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10194 (p : Pattern) (guard : d4397 p = 1) : d1199 p ≤ (0 : Int) + d1034 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1199, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10122 p hg
    simpa only [d1199, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1199, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10142 p hg
    simpa only [d1199, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10195 (p : Pattern) (guard : d4397 p = 1) : d1261 p ≤ (0 : Int) + d1035 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1261, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10194 p hg
    simpa only [d1261, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1261, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10145 p hg
    simpa only [d1261, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10196 (p : Pattern) (guard : d4397 p = 1) : d1262 p ≤ (0 : Int) + d1036 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1262, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10193 p hg
    simpa only [d1262, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1262, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10195 p hg
    simpa only [d1262, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10197 (p : Pattern) (guard : d4397 p = 1) : d1177 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9429 p hg
    simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10148 p hg
    simpa only [d4397, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10198 (p : Pattern) (guard : d4397 p = 1) : d1263 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1263, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10197 p hg
    simpa only [d1263, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1263, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d1263, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10199 (p : Pattern) (guard : d4397 p = 1) : d1264 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1264, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10198 p hg
    simpa only [d1264, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1264, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d1264, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10200 (p : Pattern) (guard : d4397 p = 1) : d1265 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1265, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10199 p hg
    simpa only [d1265, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1265, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d1265, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10201 (p : Pattern) (guard : d4397 p = 1) : d1266 p ≤ (0 : Int) + d1037 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1266, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10196 p hg
    simpa only [d1266, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1266, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10200 p hg
    simpa only [d1266, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10202 (p : Pattern) (guard : d4397 p = 1) : d1267 p ≤ (0 : Int) + d1038 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1267, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d1267, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1267, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1267, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10203 (p : Pattern) (guard : d4397 p = 1) : d1268 p ≤ (0 : Int) + d1039 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1268, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10201 p hg
    simpa only [d1268, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1268, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10202 p hg
    simpa only [d1268, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10204 (p : Pattern) (guard : d4397 p = 1) : d1269 p ≤ (0 : Int) + d1040 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1269, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d1269, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1269, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10203 p hg
    simpa only [d1269, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10205 (p : Pattern) (guard : d4397 p = 1) : d1270 p ≤ (0 : Int) + d1041 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1270, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d1270, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1270, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10204 p hg
    simpa only [d1270, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10206 (p : Pattern) (guard : d0 p = 1) : d1272 p ≤ (0 : Int) + d355 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10207 (p : Pattern) (guard : d4397 p = 1) : d1273 p ≤ (0 : Int) + d1042 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1273, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9441 p hg
    simpa only [d4397, d1273, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1273, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10206 p hg
    simpa only [d4397, d1273, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10208 (p : Pattern) (guard : d4397 p = 1) : d1275 p ≤ (0 : Int) + d1044 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1275, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9934 p hg
    simpa only [d4397, d1275, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1275, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d4397, d1275, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10209 (p : Pattern) (guard : d4397 p = 1) : d1276 p ≤ (0 : Int) + d1045 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1276, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10207 p hg
    simpa only [d1276, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1276, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10208 p hg
    simpa only [d1276, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10210 (p : Pattern) (guard : d0 p = 1) : d1278 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10211 (p : Pattern) (guard : d4397 p = 1) : d1279 p ≤ (0 : Int) + d1046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1279, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9938 p hg
    simpa only [d4397, d1279, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1279, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d4397, d1279, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10212 (p : Pattern) (guard : d4397 p = 1) : d1280 p ≤ (0 : Int) + d1047 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1280, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d4397, d1280, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1280, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d4397, d1280, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10213 (p : Pattern) (guard : d4397 p = 1) : d1281 p ≤ (0 : Int) + d1048 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1281, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10211 p hg
    simpa only [d1281, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1281, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10212 p hg
    simpa only [d1281, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10214 (p : Pattern) (guard : d4397 p = 1) : d1282 p ≤ (0 : Int) + d1049 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1282, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10209 p hg
    simpa only [d1282, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1282, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10213 p hg
    simpa only [d1282, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10215 (p : Pattern) (guard : d0 p = 1) : d1284 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10216 (p : Pattern) (guard : d4397 p = 1) : d1285 p ≤ (0 : Int) + d1050 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1285, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9943 p hg
    simpa only [d4397, d1285, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1285, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10215 p hg
    simpa only [d4397, d1285, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10217 (p : Pattern) (guard : d4397 p = 1) : d1287 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9947 p hg
    simpa only [d4397, d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1287, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10218 (p : Pattern) (guard : d4397 p = 1) : d1288 p ≤ (0 : Int) + d1052 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1288, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10216 p hg
    simpa only [d1288, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1288, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10217 p hg
    simpa only [d1288, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10219 (p : Pattern) (guard : d0 p = 1) : d1290 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
