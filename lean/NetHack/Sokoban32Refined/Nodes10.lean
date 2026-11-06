/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1200 (p : Pattern) : Int := if p 132 then d1199 p else d98 p
theorem agree1200 (p q : Pattern) (h : Agree support p q) : d1200 p = d1200 q := by
  simp only [d1200, h 132 (by decide), agree1199 p q h, agree98 p q h]
theorem nonnegative1200 (p : Pattern) : 0 ≤ d1200 p :=
  nonnegative_ite (p 132) (nonnegative1199 p) (nonnegative98 p)
def d1201 (p : Pattern) : Int := if p 112 then d1200 p else d1198 p
theorem agree1201 (p q : Pattern) (h : Agree support p q) : d1201 p = d1201 q := by
  simp only [d1201, h 112 (by decide), agree1200 p q h, agree1198 p q h]
theorem nonnegative1201 (p : Pattern) : 0 ≤ d1201 p :=
  nonnegative_ite (p 112) (nonnegative1200 p) (nonnegative1198 p)
def d1202 (p : Pattern) : Int := if p 133 then d68 p else d86 p
theorem agree1202 (p q : Pattern) (h : Agree support p q) : d1202 p = d1202 q := by
  simp only [d1202, h 133 (by decide), agree68 p q h, agree86 p q h]
theorem nonnegative1202 (p : Pattern) : 0 ≤ d1202 p :=
  nonnegative_ite (p 133) (nonnegative68 p) (nonnegative86 p)
def d1203 (p : Pattern) : Int := if p 132 then d1202 p else d86 p
theorem agree1203 (p q : Pattern) (h : Agree support p q) : d1203 p = d1203 q := by
  simp only [d1203, h 132 (by decide), agree1202 p q h, agree86 p q h]
theorem nonnegative1203 (p : Pattern) : 0 ≤ d1203 p :=
  nonnegative_ite (p 132) (nonnegative1202 p) (nonnegative86 p)
def d1204 (p : Pattern) : Int := if p 113 then d1203 p else d1187 p
theorem agree1204 (p q : Pattern) (h : Agree support p q) : d1204 p = d1204 q := by
  simp only [d1204, h 113 (by decide), agree1203 p q h, agree1187 p q h]
theorem nonnegative1204 (p : Pattern) : 0 ≤ d1204 p :=
  nonnegative_ite (p 113) (nonnegative1203 p) (nonnegative1187 p)
def d1205 (p : Pattern) : Int := if p 132 then d307 p else d98 p
theorem agree1205 (p q : Pattern) (h : Agree support p q) : d1205 p = d1205 q := by
  simp only [d1205, h 132 (by decide), agree307 p q h, agree98 p q h]
theorem nonnegative1205 (p : Pattern) : 0 ≤ d1205 p :=
  nonnegative_ite (p 132) (nonnegative307 p) (nonnegative98 p)
def d1206 (p : Pattern) : Int := if p 132 then d312 p else d97 p
theorem agree1206 (p q : Pattern) (h : Agree support p q) : d1206 p = d1206 q := by
  simp only [d1206, h 132 (by decide), agree312 p q h, agree97 p q h]
theorem nonnegative1206 (p : Pattern) : 0 ≤ d1206 p :=
  nonnegative_ite (p 132) (nonnegative312 p) (nonnegative97 p)
def d1207 (p : Pattern) : Int := if p 113 then d1206 p else d1205 p
theorem agree1207 (p q : Pattern) (h : Agree support p q) : d1207 p = d1207 q := by
  simp only [d1207, h 113 (by decide), agree1206 p q h, agree1205 p q h]
theorem nonnegative1207 (p : Pattern) : 0 ≤ d1207 p :=
  nonnegative_ite (p 113) (nonnegative1206 p) (nonnegative1205 p)
def d1208 (p : Pattern) : Int := if p 112 then d1207 p else d1204 p
theorem agree1208 (p q : Pattern) (h : Agree support p q) : d1208 p = d1208 q := by
  simp only [d1208, h 112 (by decide), agree1207 p q h, agree1204 p q h]
theorem nonnegative1208 (p : Pattern) : 0 ≤ d1208 p :=
  nonnegative_ite (p 112) (nonnegative1207 p) (nonnegative1204 p)
def d1209 (p : Pattern) : Int := if p 106 then d1208 p else d1201 p
theorem agree1209 (p q : Pattern) (h : Agree support p q) : d1209 p = d1209 q := by
  simp only [d1209, h 106 (by decide), agree1208 p q h, agree1201 p q h]
theorem nonnegative1209 (p : Pattern) : 0 ≤ d1209 p :=
  nonnegative_ite (p 106) (nonnegative1208 p) (nonnegative1201 p)
def d1210 (p : Pattern) : Int := if p 86 then d1209 p else d1195 p
theorem agree1210 (p q : Pattern) (h : Agree support p q) : d1210 p = d1210 q := by
  simp only [d1210, h 86 (by decide), agree1209 p q h, agree1195 p q h]
theorem nonnegative1210 (p : Pattern) : 0 ≤ d1210 p :=
  nonnegative_ite (p 86) (nonnegative1209 p) (nonnegative1195 p)
def d1211 (p : Pattern) : Int := if p 112 then d1193 p else d1187 p
theorem agree1211 (p q : Pattern) (h : Agree support p q) : d1211 p = d1211 q := by
  simp only [d1211, h 112 (by decide), agree1193 p q h, agree1187 p q h]
theorem nonnegative1211 (p : Pattern) : 0 ≤ d1211 p :=
  nonnegative_ite (p 112) (nonnegative1193 p) (nonnegative1187 p)
def d1212 (p : Pattern) : Int := if p 106 then d1211 p else d1183 p
theorem agree1212 (p q : Pattern) (h : Agree support p q) : d1212 p = d1212 q := by
  simp only [d1212, h 106 (by decide), agree1211 p q h, agree1183 p q h]
theorem nonnegative1212 (p : Pattern) : 0 ≤ d1212 p :=
  nonnegative_ite (p 106) (nonnegative1211 p) (nonnegative1183 p)
def d1213 (p : Pattern) : Int := if p 133 then d68 p else d97 p
theorem agree1213 (p q : Pattern) (h : Agree support p q) : d1213 p = d1213 q := by
  simp only [d1213, h 133 (by decide), agree68 p q h, agree97 p q h]
theorem nonnegative1213 (p : Pattern) : 0 ≤ d1213 p :=
  nonnegative_ite (p 133) (nonnegative68 p) (nonnegative97 p)
def d1214 (p : Pattern) : Int := if p 132 then d1213 p else d97 p
theorem agree1214 (p q : Pattern) (h : Agree support p q) : d1214 p = d1214 q := by
  simp only [d1214, h 132 (by decide), agree1213 p q h, agree97 p q h]
theorem nonnegative1214 (p : Pattern) : 0 ≤ d1214 p :=
  nonnegative_ite (p 132) (nonnegative1213 p) (nonnegative97 p)
def d1215 (p : Pattern) : Int := if p 113 then d1214 p else d1200 p
theorem agree1215 (p q : Pattern) (h : Agree support p q) : d1215 p = d1215 q := by
  simp only [d1215, h 113 (by decide), agree1214 p q h, agree1200 p q h]
theorem nonnegative1215 (p : Pattern) : 0 ≤ d1215 p :=
  nonnegative_ite (p 113) (nonnegative1214 p) (nonnegative1200 p)
def d1216 (p : Pattern) : Int := if p 112 then d1215 p else d1198 p
theorem agree1216 (p q : Pattern) (h : Agree support p q) : d1216 p = d1216 q := by
  simp only [d1216, h 112 (by decide), agree1215 p q h, agree1198 p q h]
theorem nonnegative1216 (p : Pattern) : 0 ≤ d1216 p :=
  nonnegative_ite (p 112) (nonnegative1215 p) (nonnegative1198 p)
def d1217 (p : Pattern) : Int := if p 113 then d1192 p else d1187 p
theorem agree1217 (p q : Pattern) (h : Agree support p q) : d1217 p = d1217 q := by
  simp only [d1217, h 113 (by decide), agree1192 p q h, agree1187 p q h]
theorem nonnegative1217 (p : Pattern) : 0 ≤ d1217 p :=
  nonnegative_ite (p 113) (nonnegative1192 p) (nonnegative1187 p)
def d1218 (p : Pattern) : Int := if p 113 then d2 p else d1206 p
theorem agree1218 (p q : Pattern) (h : Agree support p q) : d1218 p = d1218 q := by
  simp only [d1218, h 113 (by decide), agree2 p q h, agree1206 p q h]
theorem nonnegative1218 (p : Pattern) : 0 ≤ d1218 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1206 p)
def d1219 (p : Pattern) : Int := if p 112 then d1218 p else d1217 p
theorem agree1219 (p q : Pattern) (h : Agree support p q) : d1219 p = d1219 q := by
  simp only [d1219, h 112 (by decide), agree1218 p q h, agree1217 p q h]
theorem nonnegative1219 (p : Pattern) : 0 ≤ d1219 p :=
  nonnegative_ite (p 112) (nonnegative1218 p) (nonnegative1217 p)
def d1220 (p : Pattern) : Int := if p 106 then d1219 p else d1216 p
theorem agree1220 (p q : Pattern) (h : Agree support p q) : d1220 p = d1220 q := by
  simp only [d1220, h 106 (by decide), agree1219 p q h, agree1216 p q h]
theorem nonnegative1220 (p : Pattern) : 0 ≤ d1220 p :=
  nonnegative_ite (p 106) (nonnegative1219 p) (nonnegative1216 p)
def d1221 (p : Pattern) : Int := if p 86 then d1220 p else d1212 p
theorem agree1221 (p q : Pattern) (h : Agree support p q) : d1221 p = d1221 q := by
  simp only [d1221, h 86 (by decide), agree1220 p q h, agree1212 p q h]
theorem nonnegative1221 (p : Pattern) : 0 ≤ d1221 p :=
  nonnegative_ite (p 86) (nonnegative1220 p) (nonnegative1212 p)
def d1222 (p : Pattern) : Int := if p 80 then d1221 p else d1210 p
theorem agree1222 (p q : Pattern) (h : Agree support p q) : d1222 p = d1222 q := by
  simp only [d1222, h 80 (by decide), agree1221 p q h, agree1210 p q h]
theorem nonnegative1222 (p : Pattern) : 0 ≤ d1222 p :=
  nonnegative_ite (p 80) (nonnegative1221 p) (nonnegative1210 p)
def d1223 (p : Pattern) : Int := if p 113 then d57 p else d47 p
theorem agree1223 (p q : Pattern) (h : Agree support p q) : d1223 p = d1223 q := by
  simp only [d1223, h 113 (by decide), agree57 p q h, agree47 p q h]
theorem nonnegative1223 (p : Pattern) : 0 ≤ d1223 p :=
  nonnegative_ite (p 113) (nonnegative57 p) (nonnegative47 p)
def d1224 (p : Pattern) : Int := if p 112 then d1223 p else d28 p
theorem agree1224 (p q : Pattern) (h : Agree support p q) : d1224 p = d1224 q := by
  simp only [d1224, h 112 (by decide), agree1223 p q h, agree28 p q h]
theorem nonnegative1224 (p : Pattern) : 0 ≤ d1224 p :=
  nonnegative_ite (p 112) (nonnegative1223 p) (nonnegative28 p)
def d1225 (p : Pattern) : Int := if p 113 then d89 p else d28 p
theorem agree1225 (p q : Pattern) (h : Agree support p q) : d1225 p = d1225 q := by
  simp only [d1225, h 113 (by decide), agree89 p q h, agree28 p q h]
theorem nonnegative1225 (p : Pattern) : 0 ≤ d1225 p :=
  nonnegative_ite (p 113) (nonnegative89 p) (nonnegative28 p)
def d1226 (p : Pattern) : Int := if p 112 then d100 p else d1225 p
theorem agree1226 (p q : Pattern) (h : Agree support p q) : d1226 p = d1226 q := by
  simp only [d1226, h 112 (by decide), agree100 p q h, agree1225 p q h]
theorem nonnegative1226 (p : Pattern) : 0 ≤ d1226 p :=
  nonnegative_ite (p 112) (nonnegative100 p) (nonnegative1225 p)
def d1227 (p : Pattern) : Int := if p 113 then d110 p else d100 p
theorem agree1227 (p q : Pattern) (h : Agree support p q) : d1227 p = d1227 q := by
  simp only [d1227, h 113 (by decide), agree110 p q h, agree100 p q h]
theorem nonnegative1227 (p : Pattern) : 0 ≤ d1227 p :=
  nonnegative_ite (p 113) (nonnegative110 p) (nonnegative100 p)
def d1228 (p : Pattern) : Int := if p 112 then d1227 p else d1225 p
theorem agree1228 (p q : Pattern) (h : Agree support p q) : d1228 p = d1228 q := by
  simp only [d1228, h 112 (by decide), agree1227 p q h, agree1225 p q h]
theorem nonnegative1228 (p : Pattern) : 0 ≤ d1228 p :=
  nonnegative_ite (p 112) (nonnegative1227 p) (nonnegative1225 p)
def d1229 (p : Pattern) : Int := if p 106 then d1228 p else d1226 p
theorem agree1229 (p q : Pattern) (h : Agree support p q) : d1229 p = d1229 q := by
  simp only [d1229, h 106 (by decide), agree1228 p q h, agree1226 p q h]
theorem nonnegative1229 (p : Pattern) : 0 ≤ d1229 p :=
  nonnegative_ite (p 106) (nonnegative1228 p) (nonnegative1226 p)
def d1230 (p : Pattern) : Int := if p 86 then d1229 p else d1224 p
theorem agree1230 (p q : Pattern) (h : Agree support p q) : d1230 p = d1230 q := by
  simp only [d1230, h 86 (by decide), agree1229 p q h, agree1224 p q h]
theorem nonnegative1230 (p : Pattern) : 0 ≤ d1230 p :=
  nonnegative_ite (p 86) (nonnegative1229 p) (nonnegative1224 p)
def d1231 (p : Pattern) : Int := if p 113 then d57 p else d28 p
theorem agree1231 (p q : Pattern) (h : Agree support p q) : d1231 p = d1231 q := by
  simp only [d1231, h 113 (by decide), agree57 p q h, agree28 p q h]
theorem nonnegative1231 (p : Pattern) : 0 ≤ d1231 p :=
  nonnegative_ite (p 113) (nonnegative57 p) (nonnegative28 p)
def d1232 (p : Pattern) : Int := if p 113 then d2 p else d110 p
theorem agree1232 (p q : Pattern) (h : Agree support p q) : d1232 p = d1232 q := by
  simp only [d1232, h 113 (by decide), agree2 p q h, agree110 p q h]
theorem nonnegative1232 (p : Pattern) : 0 ≤ d1232 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative110 p)
def d1233 (p : Pattern) : Int := if p 112 then d1232 p else d1231 p
theorem agree1233 (p q : Pattern) (h : Agree support p q) : d1233 p = d1233 q := by
  simp only [d1233, h 112 (by decide), agree1232 p q h, agree1231 p q h]
theorem nonnegative1233 (p : Pattern) : 0 ≤ d1233 p :=
  nonnegative_ite (p 112) (nonnegative1232 p) (nonnegative1231 p)
def d1234 (p : Pattern) : Int := if p 106 then d1233 p else d1228 p
theorem agree1234 (p q : Pattern) (h : Agree support p q) : d1234 p = d1234 q := by
  simp only [d1234, h 106 (by decide), agree1233 p q h, agree1228 p q h]
theorem nonnegative1234 (p : Pattern) : 0 ≤ d1234 p :=
  nonnegative_ite (p 106) (nonnegative1233 p) (nonnegative1228 p)
def d1235 (p : Pattern) : Int := if p 86 then d1234 p else d1224 p
theorem agree1235 (p q : Pattern) (h : Agree support p q) : d1235 p = d1235 q := by
  simp only [d1235, h 86 (by decide), agree1234 p q h, agree1224 p q h]
theorem nonnegative1235 (p : Pattern) : 0 ≤ d1235 p :=
  nonnegative_ite (p 86) (nonnegative1234 p) (nonnegative1224 p)
def d1236 (p : Pattern) : Int := if p 80 then d1235 p else d1230 p
theorem agree1236 (p q : Pattern) (h : Agree support p q) : d1236 p = d1236 q := by
  simp only [d1236, h 80 (by decide), agree1235 p q h, agree1230 p q h]
theorem nonnegative1236 (p : Pattern) : 0 ≤ d1236 p :=
  nonnegative_ite (p 80) (nonnegative1235 p) (nonnegative1230 p)
def d1237 (p : Pattern) : Int := if p 133 then d0 p else d917 p
theorem agree1237 (p q : Pattern) (h : Agree support p q) : d1237 p = d1237 q := by
  simp only [d1237, h 133 (by decide), agree0 p q h, agree917 p q h]
theorem nonnegative1237 (p : Pattern) : 0 ≤ d1237 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative917 p)
def d1238 (p : Pattern) : Int := if p 134 then d1166 p else d0 p
theorem agree1238 (p q : Pattern) (h : Agree support p q) : d1238 p = d1238 q := by
  simp only [d1238, h 134 (by decide), agree1166 p q h, agree0 p q h]
theorem nonnegative1238 (p : Pattern) : 0 ≤ d1238 p :=
  nonnegative_ite (p 134) (nonnegative1166 p) (nonnegative0 p)
def d1239 (p : Pattern) : Int := if p 134 then d1167 p else d1 p
theorem agree1239 (p q : Pattern) (h : Agree support p q) : d1239 p = d1239 q := by
  simp only [d1239, h 134 (by decide), agree1167 p q h, agree1 p q h]
theorem nonnegative1239 (p : Pattern) : 0 ≤ d1239 p :=
  nonnegative_ite (p 134) (nonnegative1167 p) (nonnegative1 p)
def d1240 (p : Pattern) : Int := if p 159 then d0 p else d917 p
theorem agree1240 (p q : Pattern) (h : Agree support p q) : d1240 p = d1240 q := by
  simp only [d1240, h 159 (by decide), agree0 p q h, agree917 p q h]
theorem nonnegative1240 (p : Pattern) : 0 ≤ d1240 p :=
  nonnegative_ite (p 159) (nonnegative0 p) (nonnegative917 p)
def d1241 (p : Pattern) : Int := if p 134 then d1240 p else d917 p
theorem agree1241 (p q : Pattern) (h : Agree support p q) : d1241 p = d1241 q := by
  simp only [d1241, h 134 (by decide), agree1240 p q h, agree917 p q h]
theorem nonnegative1241 (p : Pattern) : 0 ≤ d1241 p :=
  nonnegative_ite (p 134) (nonnegative1240 p) (nonnegative917 p)
def d1242 (p : Pattern) : Int := if p 133 then d0 p else d1241 p
theorem agree1242 (p q : Pattern) (h : Agree support p q) : d1242 p = d1242 q := by
  simp only [d1242, h 133 (by decide), agree0 p q h, agree1241 p q h]
theorem nonnegative1242 (p : Pattern) : 0 ≤ d1242 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1241 p)
def d1243 (p : Pattern) : Int := if p 133 then d0 p else d873 p
theorem agree1243 (p q : Pattern) (h : Agree support p q) : d1243 p = d1243 q := by
  simp only [d1243, h 133 (by decide), agree0 p q h, agree873 p q h]
theorem nonnegative1243 (p : Pattern) : 0 ≤ d1243 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative873 p)
def d1244 (p : Pattern) : Int := if p 132 then d1166 p else d0 p
theorem agree1244 (p q : Pattern) (h : Agree support p q) : d1244 p = d1244 q := by
  simp only [d1244, h 132 (by decide), agree1166 p q h, agree0 p q h]
theorem nonnegative1244 (p : Pattern) : 0 ≤ d1244 p :=
  nonnegative_ite (p 132) (nonnegative1166 p) (nonnegative0 p)
def d1245 (p : Pattern) : Int := if p 132 then d1167 p else d1 p
theorem agree1245 (p q : Pattern) (h : Agree support p q) : d1245 p = d1245 q := by
  simp only [d1245, h 132 (by decide), agree1167 p q h, agree1 p q h]
theorem nonnegative1245 (p : Pattern) : 0 ≤ d1245 p :=
  nonnegative_ite (p 132) (nonnegative1167 p) (nonnegative1 p)
def d1246 (p : Pattern) : Int := if p 133 then d0 p else d1171 p
theorem agree1246 (p q : Pattern) (h : Agree support p q) : d1246 p = d1246 q := by
  simp only [d1246, h 133 (by decide), agree0 p q h, agree1171 p q h]
theorem nonnegative1246 (p : Pattern) : 0 ≤ d1246 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative1171 p)
def d1247 (p : Pattern) : Int := if p 132 then d1246 p else d1243 p
theorem agree1247 (p q : Pattern) (h : Agree support p q) : d1247 p = d1247 q := by
  simp only [d1247, h 132 (by decide), agree1246 p q h, agree1243 p q h]
theorem nonnegative1247 (p : Pattern) : 0 ≤ d1247 p :=
  nonnegative_ite (p 132) (nonnegative1246 p) (nonnegative1243 p)
def d1248 (p : Pattern) : Int := if p 134 then d0 p else d917 p
theorem agree1248 (p q : Pattern) (h : Agree support p q) : d1248 p = d1248 q := by
  simp only [d1248, h 134 (by decide), agree0 p q h, agree917 p q h]
theorem nonnegative1248 (p : Pattern) : 0 ≤ d1248 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative917 p)
def d1249 (p : Pattern) : Int := if p 134 then d0 p else d985 p
theorem agree1249 (p q : Pattern) (h : Agree support p q) : d1249 p = d1249 q := by
  simp only [d1249, h 134 (by decide), agree0 p q h, agree985 p q h]
theorem nonnegative1249 (p : Pattern) : 0 ≤ d1249 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative985 p)
def d1250 (p : Pattern) : Int := if p 134 then d0 p else d1167 p
theorem agree1250 (p q : Pattern) (h : Agree support p q) : d1250 p = d1250 q := by
  simp only [d1250, h 134 (by decide), agree0 p q h, agree1167 p q h]
theorem nonnegative1250 (p : Pattern) : 0 ≤ d1250 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative1167 p)
def d1251 (p : Pattern) : Int := if p 133 then d916 p else d0 p
theorem agree1251 (p q : Pattern) (h : Agree support p q) : d1251 p = d1251 q := by
  simp only [d1251, h 133 (by decide), agree916 p q h, agree0 p q h]
theorem nonnegative1251 (p : Pattern) : 0 ≤ d1251 p :=
  nonnegative_ite (p 133) (nonnegative916 p) (nonnegative0 p)
def d1252 (p : Pattern) : Int := if p 133 then d917 p else d1 p
theorem agree1252 (p q : Pattern) (h : Agree support p q) : d1252 p = d1252 q := by
  simp only [d1252, h 133 (by decide), agree917 p q h, agree1 p q h]
theorem nonnegative1252 (p : Pattern) : 0 ≤ d1252 p :=
  nonnegative_ite (p 133) (nonnegative917 p) (nonnegative1 p)
def d1253 (p : Pattern) : Int := if p 134 then d0 p else d1240 p
theorem agree1253 (p q : Pattern) (h : Agree support p q) : d1253 p = d1253 q := by
  simp only [d1253, h 134 (by decide), agree0 p q h, agree1240 p q h]
theorem nonnegative1253 (p : Pattern) : 0 ≤ d1253 p :=
  nonnegative_ite (p 134) (nonnegative0 p) (nonnegative1240 p)
def d1254 (p : Pattern) : Int := if p 133 then d1253 p else d1250 p
theorem agree1254 (p q : Pattern) (h : Agree support p q) : d1254 p = d1254 q := by
  simp only [d1254, h 133 (by decide), agree1253 p q h, agree1250 p q h]
theorem nonnegative1254 (p : Pattern) : 0 ≤ d1254 p :=
  nonnegative_ite (p 133) (nonnegative1253 p) (nonnegative1250 p)
def d1255 (p : Pattern) : Int := if p 132 then d42 p else d16 p
theorem agree1255 (p q : Pattern) (h : Agree support p q) : d1255 p = d1255 q := by
  simp only [d1255, h 132 (by decide), agree42 p q h, agree16 p q h]
theorem nonnegative1255 (p : Pattern) : 0 ≤ d1255 p :=
  nonnegative_ite (p 132) (nonnegative42 p) (nonnegative16 p)
def d1256 (p : Pattern) : Int := if p 132 then d41 p else d15 p
theorem agree1256 (p q : Pattern) (h : Agree support p q) : d1256 p = d1256 q := by
  simp only [d1256, h 132 (by decide), agree41 p q h, agree15 p q h]
theorem nonnegative1256 (p : Pattern) : 0 ≤ d1256 p :=
  nonnegative_ite (p 132) (nonnegative41 p) (nonnegative15 p)
def d1257 (p : Pattern) : Int := if p 132 then d62 p else d53 p
theorem agree1257 (p q : Pattern) (h : Agree support p q) : d1257 p = d1257 q := by
  simp only [d1257, h 132 (by decide), agree62 p q h, agree53 p q h]
theorem nonnegative1257 (p : Pattern) : 0 ≤ d1257 p :=
  nonnegative_ite (p 132) (nonnegative62 p) (nonnegative53 p)
def d1258 (p : Pattern) : Int := if p 113 then d1257 p else d1256 p
theorem agree1258 (p q : Pattern) (h : Agree support p q) : d1258 p = d1258 q := by
  simp only [d1258, h 113 (by decide), agree1257 p q h, agree1256 p q h]
theorem nonnegative1258 (p : Pattern) : 0 ≤ d1258 p :=
  nonnegative_ite (p 113) (nonnegative1257 p) (nonnegative1256 p)
def d1259 (p : Pattern) : Int := if p 112 then d1258 p else d1255 p
theorem agree1259 (p q : Pattern) (h : Agree support p q) : d1259 p = d1259 q := by
  simp only [d1259, h 112 (by decide), agree1258 p q h, agree1255 p q h]
theorem nonnegative1259 (p : Pattern) : 0 ≤ d1259 p :=
  nonnegative_ite (p 112) (nonnegative1258 p) (nonnegative1255 p)
def d1260 (p : Pattern) : Int := if p 132 then d69 p else d16 p
theorem agree1260 (p q : Pattern) (h : Agree support p q) : d1260 p = d1260 q := by
  simp only [d1260, h 132 (by decide), agree69 p q h, agree16 p q h]
theorem nonnegative1260 (p : Pattern) : 0 ≤ d1260 p :=
  nonnegative_ite (p 132) (nonnegative69 p) (nonnegative16 p)
def d1261 (p : Pattern) : Int := if p 132 then d68 p else d16 p
theorem agree1261 (p q : Pattern) (h : Agree support p q) : d1261 p = d1261 q := by
  simp only [d1261, h 132 (by decide), agree68 p q h, agree16 p q h]
theorem nonnegative1261 (p : Pattern) : 0 ≤ d1261 p :=
  nonnegative_ite (p 132) (nonnegative68 p) (nonnegative16 p)
def d1262 (p : Pattern) : Int := if p 113 then d1261 p else d1260 p
theorem agree1262 (p q : Pattern) (h : Agree support p q) : d1262 p = d1262 q := by
  simp only [d1262, h 113 (by decide), agree1261 p q h, agree1260 p q h]
theorem nonnegative1262 (p : Pattern) : 0 ≤ d1262 p :=
  nonnegative_ite (p 113) (nonnegative1261 p) (nonnegative1260 p)
def d1263 (p : Pattern) : Int := if p 132 then d68 p else d15 p
theorem agree1263 (p q : Pattern) (h : Agree support p q) : d1263 p = d1263 q := by
  simp only [d1263, h 132 (by decide), agree68 p q h, agree15 p q h]
theorem nonnegative1263 (p : Pattern) : 0 ≤ d1263 p :=
  nonnegative_ite (p 132) (nonnegative68 p) (nonnegative15 p)
def d1264 (p : Pattern) : Int := if p 132 then d68 p else d53 p
theorem agree1264 (p q : Pattern) (h : Agree support p q) : d1264 p = d1264 q := by
  simp only [d1264, h 132 (by decide), agree68 p q h, agree53 p q h]
theorem nonnegative1264 (p : Pattern) : 0 ≤ d1264 p :=
  nonnegative_ite (p 132) (nonnegative68 p) (nonnegative53 p)
def d1265 (p : Pattern) : Int := if p 113 then d1264 p else d1263 p
theorem agree1265 (p q : Pattern) (h : Agree support p q) : d1265 p = d1265 q := by
  simp only [d1265, h 113 (by decide), agree1264 p q h, agree1263 p q h]
theorem nonnegative1265 (p : Pattern) : 0 ≤ d1265 p :=
  nonnegative_ite (p 113) (nonnegative1264 p) (nonnegative1263 p)
def d1266 (p : Pattern) : Int := if p 112 then d1265 p else d1262 p
theorem agree1266 (p q : Pattern) (h : Agree support p q) : d1266 p = d1266 q := by
  simp only [d1266, h 112 (by decide), agree1265 p q h, agree1262 p q h]
theorem nonnegative1266 (p : Pattern) : 0 ≤ d1266 p :=
  nonnegative_ite (p 112) (nonnegative1265 p) (nonnegative1262 p)
def d1267 (p : Pattern) : Int := if p 106 then d1266 p else d1259 p
theorem agree1267 (p q : Pattern) (h : Agree support p q) : d1267 p = d1267 q := by
  simp only [d1267, h 106 (by decide), agree1266 p q h, agree1259 p q h]
theorem nonnegative1267 (p : Pattern) : 0 ≤ d1267 p :=
  nonnegative_ite (p 106) (nonnegative1266 p) (nonnegative1259 p)
def d1268 (p : Pattern) : Int := if p 132 then d92 p else d86 p
theorem agree1268 (p q : Pattern) (h : Agree support p q) : d1268 p = d1268 q := by
  simp only [d1268, h 132 (by decide), agree92 p q h, agree86 p q h]
theorem nonnegative1268 (p : Pattern) : 0 ≤ d1268 p :=
  nonnegative_ite (p 132) (nonnegative92 p) (nonnegative86 p)
def d1269 (p : Pattern) : Int := if p 113 then d1268 p else d1255 p
theorem agree1269 (p q : Pattern) (h : Agree support p q) : d1269 p = d1269 q := by
  simp only [d1269, h 113 (by decide), agree1268 p q h, agree1255 p q h]
theorem nonnegative1269 (p : Pattern) : 0 ≤ d1269 p :=
  nonnegative_ite (p 113) (nonnegative1268 p) (nonnegative1255 p)
def d1270 (p : Pattern) : Int := if p 132 then d69 p else d98 p
theorem agree1270 (p q : Pattern) (h : Agree support p q) : d1270 p = d1270 q := by
  simp only [d1270, h 132 (by decide), agree69 p q h, agree98 p q h]
theorem nonnegative1270 (p : Pattern) : 0 ≤ d1270 p :=
  nonnegative_ite (p 132) (nonnegative69 p) (nonnegative98 p)
def d1271 (p : Pattern) : Int := if p 112 then d1270 p else d1269 p
theorem agree1271 (p q : Pattern) (h : Agree support p q) : d1271 p = d1271 q := by
  simp only [d1271, h 112 (by decide), agree1270 p q h, agree1269 p q h]
theorem nonnegative1271 (p : Pattern) : 0 ≤ d1271 p :=
  nonnegative_ite (p 112) (nonnegative1270 p) (nonnegative1269 p)
def d1272 (p : Pattern) : Int := if p 132 then d68 p else d86 p
theorem agree1272 (p q : Pattern) (h : Agree support p q) : d1272 p = d1272 q := by
  simp only [d1272, h 132 (by decide), agree68 p q h, agree86 p q h]
theorem nonnegative1272 (p : Pattern) : 0 ≤ d1272 p :=
  nonnegative_ite (p 132) (nonnegative68 p) (nonnegative86 p)
def d1273 (p : Pattern) : Int := if p 113 then d1272 p else d1261 p
theorem agree1273 (p q : Pattern) (h : Agree support p q) : d1273 p = d1273 q := by
  simp only [d1273, h 113 (by decide), agree1272 p q h, agree1261 p q h]
theorem nonnegative1273 (p : Pattern) : 0 ≤ d1273 p :=
  nonnegative_ite (p 113) (nonnegative1272 p) (nonnegative1261 p)
def d1274 (p : Pattern) : Int := if p 132 then d2 p else d98 p
theorem agree1274 (p q : Pattern) (h : Agree support p q) : d1274 p = d1274 q := by
  simp only [d1274, h 132 (by decide), agree2 p q h, agree98 p q h]
theorem nonnegative1274 (p : Pattern) : 0 ≤ d1274 p :=
  nonnegative_ite (p 132) (nonnegative2 p) (nonnegative98 p)
def d1275 (p : Pattern) : Int := if p 132 then d2 p else d97 p
theorem agree1275 (p q : Pattern) (h : Agree support p q) : d1275 p = d1275 q := by
  simp only [d1275, h 132 (by decide), agree2 p q h, agree97 p q h]
theorem nonnegative1275 (p : Pattern) : 0 ≤ d1275 p :=
  nonnegative_ite (p 132) (nonnegative2 p) (nonnegative97 p)
def d1276 (p : Pattern) : Int := if p 113 then d1275 p else d1274 p
theorem agree1276 (p q : Pattern) (h : Agree support p q) : d1276 p = d1276 q := by
  simp only [d1276, h 113 (by decide), agree1275 p q h, agree1274 p q h]
theorem nonnegative1276 (p : Pattern) : 0 ≤ d1276 p :=
  nonnegative_ite (p 113) (nonnegative1275 p) (nonnegative1274 p)
def d1277 (p : Pattern) : Int := if p 112 then d1276 p else d1273 p
theorem agree1277 (p q : Pattern) (h : Agree support p q) : d1277 p = d1277 q := by
  simp only [d1277, h 112 (by decide), agree1276 p q h, agree1273 p q h]
theorem nonnegative1277 (p : Pattern) : 0 ≤ d1277 p :=
  nonnegative_ite (p 112) (nonnegative1276 p) (nonnegative1273 p)
def d1278 (p : Pattern) : Int := if p 106 then d1277 p else d1271 p
theorem agree1278 (p q : Pattern) (h : Agree support p q) : d1278 p = d1278 q := by
  simp only [d1278, h 106 (by decide), agree1277 p q h, agree1271 p q h]
theorem nonnegative1278 (p : Pattern) : 0 ≤ d1278 p :=
  nonnegative_ite (p 106) (nonnegative1277 p) (nonnegative1271 p)
def d1279 (p : Pattern) : Int := if p 86 then d1278 p else d1267 p
theorem agree1279 (p q : Pattern) (h : Agree support p q) : d1279 p = d1279 q := by
  simp only [d1279, h 86 (by decide), agree1278 p q h, agree1267 p q h]
theorem nonnegative1279 (p : Pattern) : 0 ≤ d1279 p :=
  nonnegative_ite (p 86) (nonnegative1278 p) (nonnegative1267 p)
def d1280 (p : Pattern) : Int := if p 112 then d1265 p else d1261 p
theorem agree1280 (p q : Pattern) (h : Agree support p q) : d1280 p = d1280 q := by
  simp only [d1280, h 112 (by decide), agree1265 p q h, agree1261 p q h]
theorem nonnegative1280 (p : Pattern) : 0 ≤ d1280 p :=
  nonnegative_ite (p 112) (nonnegative1265 p) (nonnegative1261 p)
def d1281 (p : Pattern) : Int := if p 106 then d1280 p else d1259 p
theorem agree1281 (p q : Pattern) (h : Agree support p q) : d1281 p = d1281 q := by
  simp only [d1281, h 106 (by decide), agree1280 p q h, agree1259 p q h]
theorem nonnegative1281 (p : Pattern) : 0 ≤ d1281 p :=
  nonnegative_ite (p 106) (nonnegative1280 p) (nonnegative1259 p)
def d1282 (p : Pattern) : Int := if p 132 then d68 p else d97 p
theorem agree1282 (p q : Pattern) (h : Agree support p q) : d1282 p = d1282 q := by
  simp only [d1282, h 132 (by decide), agree68 p q h, agree97 p q h]
theorem nonnegative1282 (p : Pattern) : 0 ≤ d1282 p :=
  nonnegative_ite (p 132) (nonnegative68 p) (nonnegative97 p)
def d1283 (p : Pattern) : Int := if p 113 then d1282 p else d1270 p
theorem agree1283 (p q : Pattern) (h : Agree support p q) : d1283 p = d1283 q := by
  simp only [d1283, h 113 (by decide), agree1282 p q h, agree1270 p q h]
theorem nonnegative1283 (p : Pattern) : 0 ≤ d1283 p :=
  nonnegative_ite (p 113) (nonnegative1282 p) (nonnegative1270 p)
def d1284 (p : Pattern) : Int := if p 112 then d1283 p else d1269 p
theorem agree1284 (p q : Pattern) (h : Agree support p q) : d1284 p = d1284 q := by
  simp only [d1284, h 112 (by decide), agree1283 p q h, agree1269 p q h]
theorem nonnegative1284 (p : Pattern) : 0 ≤ d1284 p :=
  nonnegative_ite (p 112) (nonnegative1283 p) (nonnegative1269 p)
def d1285 (p : Pattern) : Int := if p 113 then d1264 p else d1261 p
theorem agree1285 (p q : Pattern) (h : Agree support p q) : d1285 p = d1285 q := by
  simp only [d1285, h 113 (by decide), agree1264 p q h, agree1261 p q h]
theorem nonnegative1285 (p : Pattern) : 0 ≤ d1285 p :=
  nonnegative_ite (p 113) (nonnegative1264 p) (nonnegative1261 p)
def d1286 (p : Pattern) : Int := if p 113 then d2 p else d1275 p
theorem agree1286 (p q : Pattern) (h : Agree support p q) : d1286 p = d1286 q := by
  simp only [d1286, h 113 (by decide), agree2 p q h, agree1275 p q h]
theorem nonnegative1286 (p : Pattern) : 0 ≤ d1286 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1275 p)
def d1287 (p : Pattern) : Int := if p 112 then d1286 p else d1285 p
theorem agree1287 (p q : Pattern) (h : Agree support p q) : d1287 p = d1287 q := by
  simp only [d1287, h 112 (by decide), agree1286 p q h, agree1285 p q h]
theorem nonnegative1287 (p : Pattern) : 0 ≤ d1287 p :=
  nonnegative_ite (p 112) (nonnegative1286 p) (nonnegative1285 p)
def d1288 (p : Pattern) : Int := if p 106 then d1287 p else d1284 p
theorem agree1288 (p q : Pattern) (h : Agree support p q) : d1288 p = d1288 q := by
  simp only [d1288, h 106 (by decide), agree1287 p q h, agree1284 p q h]
theorem nonnegative1288 (p : Pattern) : 0 ≤ d1288 p :=
  nonnegative_ite (p 106) (nonnegative1287 p) (nonnegative1284 p)
def d1289 (p : Pattern) : Int := if p 86 then d1288 p else d1281 p
theorem agree1289 (p q : Pattern) (h : Agree support p q) : d1289 p = d1289 q := by
  simp only [d1289, h 86 (by decide), agree1288 p q h, agree1281 p q h]
theorem nonnegative1289 (p : Pattern) : 0 ≤ d1289 p :=
  nonnegative_ite (p 86) (nonnegative1288 p) (nonnegative1281 p)
def d1290 (p : Pattern) : Int := if p 80 then d1289 p else d1279 p
theorem agree1290 (p q : Pattern) (h : Agree support p q) : d1290 p = d1290 q := by
  simp only [d1290, h 80 (by decide), agree1289 p q h, agree1279 p q h]
theorem nonnegative1290 (p : Pattern) : 0 ≤ d1290 p :=
  nonnegative_ite (p 80) (nonnegative1289 p) (nonnegative1279 p)
def d1291 (p : Pattern) : Int := if p 134 then d29 p else d0 p
theorem agree1291 (p q : Pattern) (h : Agree support p q) : d1291 p = d1291 q := by
  simp only [d1291, h 134 (by decide), agree29 p q h, agree0 p q h]
theorem nonnegative1291 (p : Pattern) : 0 ≤ d1291 p :=
  nonnegative_ite (p 134) (nonnegative29 p) (nonnegative0 p)
def d1292 (p : Pattern) : Int := if p 134 then d985 p else d1 p
theorem agree1292 (p q : Pattern) (h : Agree support p q) : d1292 p = d1292 q := by
  simp only [d1292, h 134 (by decide), agree985 p q h, agree1 p q h]
theorem nonnegative1292 (p : Pattern) : 0 ≤ d1292 p :=
  nonnegative_ite (p 134) (nonnegative985 p) (nonnegative1 p)
def d1293 (p : Pattern) : Int := if p 160 then d0 p else d985 p
theorem agree1293 (p q : Pattern) (h : Agree support p q) : d1293 p = d1293 q := by
  simp only [d1293, h 160 (by decide), agree0 p q h, agree985 p q h]
theorem nonnegative1293 (p : Pattern) : 0 ≤ d1293 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative985 p)
def d1294 (p : Pattern) : Int := if p 134 then d1293 p else d917 p
theorem agree1294 (p q : Pattern) (h : Agree support p q) : d1294 p = d1294 q := by
  simp only [d1294, h 134 (by decide), agree1293 p q h, agree917 p q h]
theorem nonnegative1294 (p : Pattern) : 0 ≤ d1294 p :=
  nonnegative_ite (p 134) (nonnegative1293 p) (nonnegative917 p)
def d1295 (p : Pattern) : Int := if p 132 then d520 p else d524 p
theorem agree1295 (p q : Pattern) (h : Agree support p q) : d1295 p = d1295 q := by
  simp only [d1295, h 132 (by decide), agree520 p q h, agree524 p q h]
theorem nonnegative1295 (p : Pattern) : 0 ≤ d1295 p :=
  nonnegative_ite (p 132) (nonnegative520 p) (nonnegative524 p)
def d1296 (p : Pattern) : Int := if p 113 then d1295 p else d51 p
theorem agree1296 (p q : Pattern) (h : Agree support p q) : d1296 p = d1296 q := by
  simp only [d1296, h 113 (by decide), agree1295 p q h, agree51 p q h]
theorem nonnegative1296 (p : Pattern) : 0 ≤ d1296 p :=
  nonnegative_ite (p 113) (nonnegative1295 p) (nonnegative51 p)
def d1297 (p : Pattern) : Int := if p 112 then d1296 p else d51 p
theorem agree1297 (p q : Pattern) (h : Agree support p q) : d1297 p = d1297 q := by
  simp only [d1297, h 112 (by decide), agree1296 p q h, agree51 p q h]
theorem nonnegative1297 (p : Pattern) : 0 ≤ d1297 p :=
  nonnegative_ite (p 112) (nonnegative1296 p) (nonnegative51 p)
def d1298 (p : Pattern) : Int := if p 113 then d525 p else d80 p
theorem agree1298 (p q : Pattern) (h : Agree support p q) : d1298 p = d1298 q := by
  simp only [d1298, h 113 (by decide), agree525 p q h, agree80 p q h]
theorem nonnegative1298 (p : Pattern) : 0 ≤ d1298 p :=
  nonnegative_ite (p 113) (nonnegative525 p) (nonnegative80 p)
def d1299 (p : Pattern) : Int := if p 112 then d1298 p else d80 p
theorem agree1299 (p q : Pattern) (h : Agree support p q) : d1299 p = d1299 q := by
  simp only [d1299, h 112 (by decide), agree1298 p q h, agree80 p q h]
theorem nonnegative1299 (p : Pattern) : 0 ≤ d1299 p :=
  nonnegative_ite (p 112) (nonnegative1298 p) (nonnegative80 p)
def d1300 (p : Pattern) : Int := if p 106 then d1299 p else d1297 p
theorem agree1300 (p q : Pattern) (h : Agree support p q) : d1300 p = d1300 q := by
  simp only [d1300, h 106 (by decide), agree1299 p q h, agree1297 p q h]
theorem nonnegative1300 (p : Pattern) : 0 ≤ d1300 p :=
  nonnegative_ite (p 106) (nonnegative1299 p) (nonnegative1297 p)
def d1301 (p : Pattern) : Int := if p 112 then d126 p else d1296 p
theorem agree1301 (p q : Pattern) (h : Agree support p q) : d1301 p = d1301 q := by
  simp only [d1301, h 112 (by decide), agree126 p q h, agree1296 p q h]
theorem nonnegative1301 (p : Pattern) : 0 ≤ d1301 p :=
  nonnegative_ite (p 112) (nonnegative126 p) (nonnegative1296 p)
def d1302 (p : Pattern) : Int := if p 112 then d112 p else d1298 p
theorem agree1302 (p q : Pattern) (h : Agree support p q) : d1302 p = d1302 q := by
  simp only [d1302, h 112 (by decide), agree112 p q h, agree1298 p q h]
theorem nonnegative1302 (p : Pattern) : 0 ≤ d1302 p :=
  nonnegative_ite (p 112) (nonnegative112 p) (nonnegative1298 p)
def d1303 (p : Pattern) : Int := if p 106 then d1302 p else d1301 p
theorem agree1303 (p q : Pattern) (h : Agree support p q) : d1303 p = d1303 q := by
  simp only [d1303, h 106 (by decide), agree1302 p q h, agree1301 p q h]
theorem nonnegative1303 (p : Pattern) : 0 ≤ d1303 p :=
  nonnegative_ite (p 106) (nonnegative1302 p) (nonnegative1301 p)
def d1304 (p : Pattern) : Int := if p 86 then d1303 p else d1300 p
theorem agree1304 (p q : Pattern) (h : Agree support p q) : d1304 p = d1304 q := by
  simp only [d1304, h 86 (by decide), agree1303 p q h, agree1300 p q h]
theorem nonnegative1304 (p : Pattern) : 0 ≤ d1304 p :=
  nonnegative_ite (p 86) (nonnegative1303 p) (nonnegative1300 p)
def d1305 (p : Pattern) : Int := if p 112 then d130 p else d1298 p
theorem agree1305 (p q : Pattern) (h : Agree support p q) : d1305 p = d1305 q := by
  simp only [d1305, h 112 (by decide), agree130 p q h, agree1298 p q h]
theorem nonnegative1305 (p : Pattern) : 0 ≤ d1305 p :=
  nonnegative_ite (p 112) (nonnegative130 p) (nonnegative1298 p)
def d1306 (p : Pattern) : Int := if p 106 then d1305 p else d1301 p
theorem agree1306 (p q : Pattern) (h : Agree support p q) : d1306 p = d1306 q := by
  simp only [d1306, h 106 (by decide), agree1305 p q h, agree1301 p q h]
theorem nonnegative1306 (p : Pattern) : 0 ≤ d1306 p :=
  nonnegative_ite (p 106) (nonnegative1305 p) (nonnegative1301 p)
def d1307 (p : Pattern) : Int := if p 86 then d1306 p else d1300 p
theorem agree1307 (p q : Pattern) (h : Agree support p q) : d1307 p = d1307 q := by
  simp only [d1307, h 86 (by decide), agree1306 p q h, agree1300 p q h]
theorem nonnegative1307 (p : Pattern) : 0 ≤ d1307 p :=
  nonnegative_ite (p 86) (nonnegative1306 p) (nonnegative1300 p)
def d1308 (p : Pattern) : Int := if p 80 then d1307 p else d1304 p
theorem agree1308 (p q : Pattern) (h : Agree support p q) : d1308 p = d1308 q := by
  simp only [d1308, h 80 (by decide), agree1307 p q h, agree1304 p q h]
theorem nonnegative1308 (p : Pattern) : 0 ≤ d1308 p :=
  nonnegative_ite (p 80) (nonnegative1307 p) (nonnegative1304 p)
def d1309 (p : Pattern) : Int := if p 133 then d26 p else d16 p
theorem agree1309 (p q : Pattern) (h : Agree support p q) : d1309 p = d1309 q := by
  simp only [d1309, h 133 (by decide), agree26 p q h, agree16 p q h]
theorem nonnegative1309 (p : Pattern) : 0 ≤ d1309 p :=
  nonnegative_ite (p 133) (nonnegative26 p) (nonnegative16 p)
def d1310 (p : Pattern) : Int := if p 133 then d26 p else d35 p
theorem agree1310 (p q : Pattern) (h : Agree support p q) : d1310 p = d1310 q := by
  simp only [d1310, h 133 (by decide), agree26 p q h, agree35 p q h]
theorem nonnegative1310 (p : Pattern) : 0 ≤ d1310 p :=
  nonnegative_ite (p 133) (nonnegative26 p) (nonnegative35 p)
def d1311 (p : Pattern) : Int := if p 132 then d1310 p else d1309 p
theorem agree1311 (p q : Pattern) (h : Agree support p q) : d1311 p = d1311 q := by
  simp only [d1311, h 132 (by decide), agree1310 p q h, agree1309 p q h]
theorem nonnegative1311 (p : Pattern) : 0 ≤ d1311 p :=
  nonnegative_ite (p 132) (nonnegative1310 p) (nonnegative1309 p)
def d1312 (p : Pattern) : Int := if p 133 then d25 p else d15 p
theorem agree1312 (p q : Pattern) (h : Agree support p q) : d1312 p = d1312 q := by
  simp only [d1312, h 133 (by decide), agree25 p q h, agree15 p q h]
theorem nonnegative1312 (p : Pattern) : 0 ≤ d1312 p :=
  nonnegative_ite (p 133) (nonnegative25 p) (nonnegative15 p)
def d1313 (p : Pattern) : Int := if p 133 then d25 p else d34 p
theorem agree1313 (p q : Pattern) (h : Agree support p q) : d1313 p = d1313 q := by
  simp only [d1313, h 133 (by decide), agree25 p q h, agree34 p q h]
theorem nonnegative1313 (p : Pattern) : 0 ≤ d1313 p :=
  nonnegative_ite (p 133) (nonnegative25 p) (nonnegative34 p)
def d1314 (p : Pattern) : Int := if p 132 then d1313 p else d1312 p
theorem agree1314 (p q : Pattern) (h : Agree support p q) : d1314 p = d1314 q := by
  simp only [d1314, h 132 (by decide), agree1313 p q h, agree1312 p q h]
theorem nonnegative1314 (p : Pattern) : 0 ≤ d1314 p :=
  nonnegative_ite (p 132) (nonnegative1313 p) (nonnegative1312 p)
def d1315 (p : Pattern) : Int := if p 133 then d55 p else d53 p
theorem agree1315 (p q : Pattern) (h : Agree support p q) : d1315 p = d1315 q := by
  simp only [d1315, h 133 (by decide), agree55 p q h, agree53 p q h]
theorem nonnegative1315 (p : Pattern) : 0 ≤ d1315 p :=
  nonnegative_ite (p 133) (nonnegative55 p) (nonnegative53 p)
def d1316 (p : Pattern) : Int := if p 133 then d55 p else d59 p
theorem agree1316 (p q : Pattern) (h : Agree support p q) : d1316 p = d1316 q := by
  simp only [d1316, h 133 (by decide), agree55 p q h, agree59 p q h]
theorem nonnegative1316 (p : Pattern) : 0 ≤ d1316 p :=
  nonnegative_ite (p 133) (nonnegative55 p) (nonnegative59 p)
def d1317 (p : Pattern) : Int := if p 132 then d1316 p else d1315 p
theorem agree1317 (p q : Pattern) (h : Agree support p q) : d1317 p = d1317 q := by
  simp only [d1317, h 132 (by decide), agree1316 p q h, agree1315 p q h]
theorem nonnegative1317 (p : Pattern) : 0 ≤ d1317 p :=
  nonnegative_ite (p 132) (nonnegative1316 p) (nonnegative1315 p)
def d1318 (p : Pattern) : Int := if p 113 then d1317 p else d1314 p
theorem agree1318 (p q : Pattern) (h : Agree support p q) : d1318 p = d1318 q := by
  simp only [d1318, h 113 (by decide), agree1317 p q h, agree1314 p q h]
theorem nonnegative1318 (p : Pattern) : 0 ≤ d1318 p :=
  nonnegative_ite (p 113) (nonnegative1317 p) (nonnegative1314 p)
def d1319 (p : Pattern) : Int := if p 112 then d1318 p else d1311 p
theorem agree1319 (p q : Pattern) (h : Agree support p q) : d1319 p = d1319 q := by
  simp only [d1319, h 112 (by decide), agree1318 p q h, agree1311 p q h]
theorem nonnegative1319 (p : Pattern) : 0 ≤ d1319 p :=
  nonnegative_ite (p 112) (nonnegative1318 p) (nonnegative1311 p)
end NetHack.Sokoban32Refined
