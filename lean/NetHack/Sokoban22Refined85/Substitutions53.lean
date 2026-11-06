/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions52
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6360 (p : Pattern) : d1229 (change p 163 (some 162)) = d4864 p := by
  change (if p 138 then d1228 (change p 163 (some 162)) else d1221 (change p 163 (some 162))) = d4864 p
  rw [sub6359, sub6352]
  rfl
theorem sub6361 (p : Pattern) : d1230 (change p 163 (some 162)) = d16 p := by
  change d1177 (change p 163 (some 162)) = d16 p
  exact sub6308 p
theorem sub6362 (p : Pattern) : d1231 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1230 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6361]
  rfl
theorem sub6363 (p : Pattern) : d1232 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1231 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6362]
  rfl
theorem sub6364 (p : Pattern) : d1233 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1227 (change p 163 (some 162)) else d1232 (change p 163 (some 162))) = d4863 p
  rw [sub6358, sub6363]
  rfl
theorem sub6365 (p : Pattern) : d1234 (change p 163 (some 162)) = d4867 p := by
  change (if p 138 then d12 (change p 163 (some 162)) else d1233 (change p 163 (some 162))) = d4867 p
  rw [sub6261, sub6364]
  rfl
theorem sub6366 (p : Pattern) : d1235 (change p 163 (some 162)) = d4868 p := by
  change (if p 116 then d1234 (change p 163 (some 162)) else d1229 (change p 163 (some 162))) = d4868 p
  rw [sub6365, sub6360]
  rfl
theorem sub6367 (p : Pattern) : d1236 (change p 163 (some 162)) = d4869 p := by
  change (if p 115 then d1235 (change p 163 (some 162)) else d1207 (change p 163 (some 162))) = d4869 p
  rw [sub6366, sub6339]
  rfl
theorem sub6368 (p : Pattern) : d1154 (change p 163 (some 162)) = d16 p := by
  change d16 (change p 163 (some 162)) = d16 p
  exact sub6265 p
theorem sub6369 (p : Pattern) : d1238 (change p 163 (some 162)) = d16 p := by
  change d1154 (change p 163 (some 162)) = d16 p
  exact sub6368 p
theorem sub6370 (p : Pattern) : d1239 (change p 163 (some 162)) = d26 p := by
  change d27 (change p 163 (some 162)) = d26 p
  exact sub6273 p
theorem sub6371 (p : Pattern) : d1240 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1239 (change p 163 (some 162)) else d1238 (change p 163 (some 162))) = d4854 p
  rw [sub6370, sub6369]
  rfl
theorem sub6372 (p : Pattern) : d1242 (change p 163 (some 162)) = d42 p := by
  change d1158 (change p 163 (some 162)) = d42 p
  exact sub6281 p
theorem sub6373 (p : Pattern) : d1243 (change p 163 (some 162)) = d4855 p := by
  change (if p 161 then d1161 (change p 163 (some 162)) else d1242 (change p 163 (some 162))) = d4855 p
  rw [sub6285, sub6372]
  rfl
theorem sub6374 (p : Pattern) : d1244 (change p 163 (some 162)) = d4856 p := by
  change (if p 160 then d1243 (change p 163 (some 162)) else d1240 (change p 163 (some 162))) = d4856 p
  rw [sub6373, sub6371]
  rfl
theorem sub6375 (p : Pattern) : d1167 (change p 163 (some 162)) = d53 p := by
  change d53 (change p 163 (some 162)) = d53 p
  exact sub6292 p
theorem sub6376 (p : Pattern) : d1245 (change p 163 (some 162)) = d53 p := by
  change d1167 (change p 163 (some 162)) = d53 p
  exact sub6375 p
theorem sub6377 (p : Pattern) : d1246 (change p 163 (some 162)) = d62 p := by
  change d63 (change p 163 (some 162)) = d62 p
  exact sub6296 p
theorem sub6378 (p : Pattern) : d1247 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1246 (change p 163 (some 162)) else d1245 (change p 163 (some 162))) = d4857 p
  rw [sub6377, sub6376]
  rfl
theorem sub6379 (p : Pattern) : d1248 (change p 163 (some 162)) = d4859 p := by
  change (if p 160 then d1219 (change p 163 (some 162)) else d1247 (change p 163 (some 162))) = d4859 p
  rw [sub6350, sub6378]
  rfl
theorem sub6380 (p : Pattern) : d1249 (change p 163 (some 162)) = d4860 p := by
  change (if p 141 then d1248 (change p 163 (some 162)) else d1244 (change p 163 (some 162))) = d4860 p
  rw [sub6379, sub6374]
  rfl
theorem sub6381 (p : Pattern) : d1250 (change p 163 (some 162)) = d16 p := by
  change d1177 (change p 163 (some 162)) = d16 p
  exact sub6308 p
theorem sub6382 (p : Pattern) : d1251 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1250 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6381]
  rfl
theorem sub6383 (p : Pattern) : d1252 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1251 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6382]
  rfl
theorem sub6384 (p : Pattern) : d1253 (change p 163 (some 162)) = d53 p := by
  change d1181 (change p 163 (some 162)) = d53 p
  exact sub6315 p
theorem sub6385 (p : Pattern) : d1254 (change p 163 (some 162)) = d4857 p := by
  change (if p 161 then d1182 (change p 163 (some 162)) else d1253 (change p 163 (some 162))) = d4857 p
  rw [sub6312, sub6384]
  rfl
theorem sub6386 (p : Pattern) : d1255 (change p 163 (some 162)) = d4862 p := by
  change (if p 160 then d1189 (change p 163 (some 162)) else d1254 (change p 163 (some 162))) = d4862 p
  rw [sub6319, sub6385]
  rfl
theorem sub6387 (p : Pattern) : d1256 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1255 (change p 163 (some 162)) else d1252 (change p 163 (some 162))) = d4863 p
  rw [sub6386, sub6383]
  rfl
theorem sub6388 (p : Pattern) : d1257 (change p 163 (some 162)) = d4864 p := by
  change (if p 138 then d1256 (change p 163 (some 162)) else d1249 (change p 163 (some 162))) = d4864 p
  rw [sub6387, sub6380]
  rfl
theorem sub6389 (p : Pattern) : d1258 (change p 163 (some 162)) = d4865 p := by
  change (if p 138 then d1205 (change p 163 (some 162)) else d1191 (change p 163 (some 162))) = d4865 p
  rw [sub6337, sub6321]
  rfl
theorem sub6390 (p : Pattern) : d1259 (change p 163 (some 162)) = d4866 p := by
  change (if p 116 then d1258 (change p 163 (some 162)) else d1257 (change p 163 (some 162))) = d4866 p
  rw [sub6389, sub6388]
  rfl
theorem sub6391 (p : Pattern) : d1260 (change p 163 (some 162)) = d4856 p := by
  change (if p 160 then d1214 (change p 163 (some 162)) else d1195 (change p 163 (some 162))) = d4856 p
  rw [sub6345, sub6325]
  rfl
theorem sub6392 (p : Pattern) : d1261 (change p 163 (some 162)) = d4859 p := by
  change (if p 160 then d1219 (change p 163 (some 162)) else d1199 (change p 163 (some 162))) = d4859 p
  rw [sub6350, sub6328]
  rfl
theorem sub6393 (p : Pattern) : d1262 (change p 163 (some 162)) = d4860 p := by
  change (if p 141 then d1261 (change p 163 (some 162)) else d1260 (change p 163 (some 162))) = d4860 p
  rw [sub6392, sub6391]
  rfl
theorem sub6394 (p : Pattern) : d1263 (change p 163 (some 162)) = d4854 p := by
  change (if p 161 then d1179 (change p 163 (some 162)) else d1177 (change p 163 (some 162))) = d4854 p
  rw [sub6310, sub6308]
  rfl
theorem sub6395 (p : Pattern) : d1264 (change p 163 (some 162)) = d4861 p := by
  change (if p 160 then d1183 (change p 163 (some 162)) else d1263 (change p 163 (some 162))) = d4861 p
  rw [sub6313, sub6394]
  rfl
theorem sub6396 (p : Pattern) : d1265 (change p 163 (some 162)) = d4863 p := by
  change (if p 141 then d1227 (change p 163 (some 162)) else d1264 (change p 163 (some 162))) = d4863 p
  rw [sub6358, sub6395]
  rfl
theorem sub6397 (p : Pattern) : d1266 (change p 163 (some 162)) = d4864 p := by
  change (if p 138 then d1265 (change p 163 (some 162)) else d1262 (change p 163 (some 162))) = d4864 p
  rw [sub6396, sub6393]
  rfl
theorem sub6398 (p : Pattern) : d1267 (change p 163 (some 162)) = d4867 p := by
  change (if p 138 then d12 (change p 163 (some 162)) else d1228 (change p 163 (some 162))) = d4867 p
  rw [sub6261, sub6359]
  rfl
theorem sub6399 (p : Pattern) : d1268 (change p 163 (some 162)) = d4868 p := by
  change (if p 116 then d1267 (change p 163 (some 162)) else d1266 (change p 163 (some 162))) = d4868 p
  rw [sub6398, sub6397]
  rfl
theorem sub6400 (p : Pattern) : d1269 (change p 163 (some 162)) = d4869 p := by
  change (if p 115 then d1268 (change p 163 (some 162)) else d1259 (change p 163 (some 162))) = d4869 p
  rw [sub6399, sub6390]
  rfl
theorem sub6401 (p : Pattern) : d1270 (change p 163 (some 162)) = d4869 p := by
  change (if p 71 then d1269 (change p 163 (some 162)) else d1236 (change p 163 (some 162))) = d4869 p
  rw [sub6400, sub6367]
  simp only [ite_self]
theorem sub6402 (p : Pattern) : d1 (change p 163 (some 162)) = d1 p := by
  rfl
theorem sub6403 (p : Pattern) : d102 (change p 163 (some 162)) = d102 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d1 (change p 163 (some 162))) = d102 p
  rw [sub6261, sub6402]
  rfl
theorem sub6404 (p : Pattern) : d103 (change p 163 (some 162)) = d103 p := by
  change (if p 246 then d102 (change p 163 (some 162)) else d1 (change p 163 (some 162))) = d103 p
  rw [sub6403, sub6402]
  rfl
theorem sub6405 (p : Pattern) : d104 (change p 163 (some 162)) = d104 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d103 (change p 163 (some 162))) = d104 p
  rw [sub6261, sub6404]
  rfl
theorem sub6406 (p : Pattern) : d105 (change p 163 (some 162)) = d105 p := by
  change (if p 182 then d104 (change p 163 (some 162)) else d103 (change p 163 (some 162))) = d105 p
  rw [sub6405, sub6404]
  rfl
theorem sub6407 (p : Pattern) : d1272 (change p 163 (some 162)) = d105 p := by
  change d105 (change p 163 (some 162)) = d105 p
  exact sub6406 p
theorem sub6408 (p : Pattern) : d1273 (change p 163 (some 162)) = d105 p := by
  change d1272 (change p 163 (some 162)) = d105 p
  exact sub6407 p
theorem sub6409 (p : Pattern) : d10 (change p 163 (some 162)) = d10 p := by
  rfl
theorem sub6410 (p : Pattern) : d57 (change p 163 (some 162)) = d57 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d10 (change p 163 (some 162))) = d57 p
  rw [sub6261, sub6409]
  rfl
theorem sub6411 (p : Pattern) : d58 (change p 163 (some 162)) = d58 p := by
  change (if p 246 then d57 (change p 163 (some 162)) else d10 (change p 163 (some 162))) = d58 p
  rw [sub6410, sub6409]
  rfl
theorem sub6412 (p : Pattern) : d59 (change p 163 (some 162)) = d59 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d58 (change p 163 (some 162))) = d59 p
  rw [sub6261, sub6411]
  rfl
theorem sub6413 (p : Pattern) : d60 (change p 163 (some 162)) = d60 p := by
  change (if p 182 then d59 (change p 163 (some 162)) else d58 (change p 163 (some 162))) = d60 p
  rw [sub6412, sub6411]
  rfl
theorem sub6414 (p : Pattern) : d112 (change p 163 (some 162)) = d60 p := by
  change d60 (change p 163 (some 162)) = d60 p
  exact sub6413 p
theorem sub6415 (p : Pattern) : d1275 (change p 163 (some 162)) = d60 p := by
  change d112 (change p 163 (some 162)) = d60 p
  exact sub6414 p
theorem sub6416 (p : Pattern) : d1276 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1275 (change p 163 (some 162)) else d1273 (change p 163 (some 162))) = d4870 p
  rw [sub6415, sub6408]
  rfl
theorem sub6417 (p : Pattern) : d124 (change p 163 (some 162)) = d124 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d103 (change p 163 (some 162))) = d124 p
  rw [sub6261, sub6404]
  rfl
theorem sub6418 (p : Pattern) : d1278 (change p 163 (some 162)) = d124 p := by
  change d124 (change p 163 (some 162)) = d124 p
  exact sub6417 p
theorem sub6419 (p : Pattern) : d1279 (change p 163 (some 162)) = d124 p := by
  change d1278 (change p 163 (some 162)) = d124 p
  exact sub6418 p
theorem sub6420 (p : Pattern) : d70 (change p 163 (some 162)) = d70 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d58 (change p 163 (some 162))) = d70 p
  rw [sub6261, sub6411]
  rfl
theorem sub6421 (p : Pattern) : d128 (change p 163 (some 162)) = d70 p := by
  change d70 (change p 163 (some 162)) = d70 p
  exact sub6420 p
theorem sub6422 (p : Pattern) : d1280 (change p 163 (some 162)) = d70 p := by
  change d128 (change p 163 (some 162)) = d70 p
  exact sub6421 p
theorem sub6423 (p : Pattern) : d1281 (change p 163 (some 162)) = d4871 p := by
  change (if p 161 then d1280 (change p 163 (some 162)) else d1279 (change p 163 (some 162))) = d4871 p
  rw [sub6422, sub6419]
  rfl
theorem sub6424 (p : Pattern) : d1282 (change p 163 (some 162)) = d4872 p := by
  change (if p 160 then d1281 (change p 163 (some 162)) else d1276 (change p 163 (some 162))) = d4872 p
  rw [sub6423, sub6416]
  rfl
theorem sub6425 (p : Pattern) : d3 (change p 163 (some 162)) = d3 p := by
  rfl
theorem sub6426 (p : Pattern) : d115 (change p 163 (some 162)) = d115 p := by
  change (if p 247 then d12 (change p 163 (some 162)) else d3 (change p 163 (some 162))) = d115 p
  rw [sub6261, sub6425]
  rfl
theorem sub6427 (p : Pattern) : d116 (change p 163 (some 162)) = d116 p := by
  change (if p 246 then d115 (change p 163 (some 162)) else d3 (change p 163 (some 162))) = d116 p
  rw [sub6426, sub6425]
  rfl
theorem sub6428 (p : Pattern) : d117 (change p 163 (some 162)) = d117 p := by
  change (if p 204 then d12 (change p 163 (some 162)) else d116 (change p 163 (some 162))) = d117 p
  rw [sub6261, sub6427]
  rfl
theorem sub6429 (p : Pattern) : d132 (change p 163 (some 162)) = d132 p := by
  change (if p 182 then d117 (change p 163 (some 162)) else d116 (change p 163 (some 162))) = d132 p
  rw [sub6428, sub6427]
  rfl
theorem sub6430 (p : Pattern) : d1284 (change p 163 (some 162)) = d132 p := by
  change d132 (change p 163 (some 162)) = d132 p
  exact sub6429 p
theorem sub6431 (p : Pattern) : d1285 (change p 163 (some 162)) = d132 p := by
  change d1284 (change p 163 (some 162)) = d132 p
  exact sub6430 p
theorem sub6432 (p : Pattern) : d1287 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6433 (p : Pattern) : d1288 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1287 (change p 163 (some 162)) else d1285 (change p 163 (some 162))) = d4705 p
  rw [sub6432, sub6431]
  rfl
theorem sub6434 (p : Pattern) : d139 (change p 163 (some 162)) = d139 p := by
  change (if p 182 then d12 (change p 163 (some 162)) else d116 (change p 163 (some 162))) = d139 p
  rw [sub6261, sub6427]
  rfl
theorem sub6435 (p : Pattern) : d1290 (change p 163 (some 162)) = d139 p := by
  change d139 (change p 163 (some 162)) = d139 p
  exact sub6434 p
theorem sub6436 (p : Pattern) : d1291 (change p 163 (some 162)) = d139 p := by
  change d1290 (change p 163 (some 162)) = d139 p
  exact sub6435 p
theorem sub6437 (p : Pattern) : d1292 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6438 (p : Pattern) : d1293 (change p 163 (some 162)) = d4873 p := by
  change (if p 161 then d1292 (change p 163 (some 162)) else d1291 (change p 163 (some 162))) = d4873 p
  rw [sub6437, sub6436]
  rfl
theorem sub6439 (p : Pattern) : d1294 (change p 163 (some 162)) = d4874 p := by
  change (if p 160 then d1293 (change p 163 (some 162)) else d1288 (change p 163 (some 162))) = d4874 p
  rw [sub6438, sub6433]
  rfl
theorem sub6440 (p : Pattern) : d1295 (change p 163 (some 162)) = d4875 p := by
  change (if p 141 then d1294 (change p 163 (some 162)) else d1282 (change p 163 (some 162))) = d4875 p
  rw [sub6439, sub6424]
  rfl
theorem sub6441 (p : Pattern) : d1296 (change p 163 (some 162)) = d105 p := by
  change d105 (change p 163 (some 162)) = d105 p
  exact sub6406 p
theorem sub6442 (p : Pattern) : d1297 (change p 163 (some 162)) = d105 p := by
  change d1296 (change p 163 (some 162)) = d105 p
  exact sub6441 p
theorem sub6443 (p : Pattern) : d1298 (change p 163 (some 162)) = d60 p := by
  change d112 (change p 163 (some 162)) = d60 p
  exact sub6414 p
theorem sub6444 (p : Pattern) : d1299 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1297 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6442]
  rfl
theorem sub6445 (p : Pattern) : d1300 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6446 (p : Pattern) : d1301 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d1300 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6445]
  simp only [ite_self]
theorem sub6447 (p : Pattern) : d1302 (change p 163 (some 162)) = d4876 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1299 (change p 163 (some 162))) = d4876 p
  rw [sub6446, sub6444]
  rfl
theorem sub6448 (p : Pattern) : d1289 (change p 163 (some 162)) = d132 p := by
  change d132 (change p 163 (some 162)) = d132 p
  exact sub6429 p
theorem sub6449 (p : Pattern) : d1304 (change p 163 (some 162)) = d132 p := by
  change d1289 (change p 163 (some 162)) = d132 p
  exact sub6448 p
theorem sub6450 (p : Pattern) : d1305 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1300 (change p 163 (some 162)) else d1304 (change p 163 (some 162))) = d4705 p
  rw [sub6445, sub6449]
  rfl
theorem sub6451 (p : Pattern) : d1306 (change p 163 (some 162)) = d4877 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1305 (change p 163 (some 162))) = d4877 p
  rw [sub6446, sub6450]
  rfl
theorem sub6452 (p : Pattern) : d1307 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1306 (change p 163 (some 162)) else d1302 (change p 163 (some 162))) = d4878 p
  rw [sub6451, sub6447]
  rfl
theorem sub6453 (p : Pattern) : d1308 (change p 163 (some 162)) = d4879 p := by
  change (if p 138 then d1307 (change p 163 (some 162)) else d1295 (change p 163 (some 162))) = d4879 p
  rw [sub6452, sub6440]
  rfl
theorem sub6454 (p : Pattern) : d1309 (change p 163 (some 162)) = d105 p := by
  change d1296 (change p 163 (some 162)) = d105 p
  exact sub6441 p
theorem sub6455 (p : Pattern) : d1310 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1309 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6454]
  rfl
theorem sub6456 (p : Pattern) : d1311 (change p 163 (some 162)) = d4876 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1310 (change p 163 (some 162))) = d4876 p
  rw [sub6446, sub6455]
  rfl
theorem sub6457 (p : Pattern) : d1313 (change p 163 (some 162)) = d132 p := by
  change d1289 (change p 163 (some 162)) = d132 p
  exact sub6448 p
theorem sub6458 (p : Pattern) : d1314 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1300 (change p 163 (some 162)) else d1313 (change p 163 (some 162))) = d4705 p
  rw [sub6445, sub6457]
  rfl
theorem sub6459 (p : Pattern) : d1315 (change p 163 (some 162)) = d4877 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1314 (change p 163 (some 162))) = d4877 p
  rw [sub6446, sub6458]
  rfl
theorem sub6460 (p : Pattern) : d1316 (change p 163 (some 162)) = d4878 p := by
  change (if p 141 then d1315 (change p 163 (some 162)) else d1311 (change p 163 (some 162))) = d4878 p
  rw [sub6459, sub6456]
  rfl
theorem sub6461 (p : Pattern) : d159 (change p 163 (some 162)) = d12 p := by
  change d12 (change p 163 (some 162)) = d12 p
  exact sub6261 p
theorem sub6462 (p : Pattern) : d160 (change p 163 (some 162)) = d12 p := by
  change (if p 161 then d12 (change p 163 (some 162)) else d159 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6461]
  simp only [ite_self]
theorem sub6463 (p : Pattern) : d161 (change p 163 (some 162)) = d12 p := by
  change (if p 160 then d12 (change p 163 (some 162)) else d160 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6462]
  simp only [ite_self]
theorem sub6464 (p : Pattern) : d162 (change p 163 (some 162)) = d12 p := by
  change (if p 141 then d12 (change p 163 (some 162)) else d161 (change p 163 (some 162))) = d12 p
  rw [sub6261, sub6463]
  simp only [ite_self]
theorem sub6465 (p : Pattern) : d1317 (change p 163 (some 162)) = d4880 p := by
  change (if p 138 then d162 (change p 163 (some 162)) else d1316 (change p 163 (some 162))) = d4880 p
  rw [sub6464, sub6460]
  rfl
theorem sub6466 (p : Pattern) : d1318 (change p 163 (some 162)) = d4881 p := by
  change (if p 116 then d1317 (change p 163 (some 162)) else d1308 (change p 163 (some 162))) = d4881 p
  rw [sub6465, sub6453]
  rfl
theorem sub6467 (p : Pattern) : d1303 (change p 163 (some 162)) = d105 p := by
  change d105 (change p 163 (some 162)) = d105 p
  exact sub6406 p
theorem sub6468 (p : Pattern) : d1320 (change p 163 (some 162)) = d105 p := by
  change d1303 (change p 163 (some 162)) = d105 p
  exact sub6467 p
theorem sub6469 (p : Pattern) : d1321 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1320 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6468]
  rfl
theorem sub6470 (p : Pattern) : d1323 (change p 163 (some 162)) = d124 p := by
  change d1278 (change p 163 (some 162)) = d124 p
  exact sub6418 p
theorem sub6471 (p : Pattern) : d1324 (change p 163 (some 162)) = d4871 p := by
  change (if p 161 then d1280 (change p 163 (some 162)) else d1323 (change p 163 (some 162))) = d4871 p
  rw [sub6422, sub6470]
  rfl
theorem sub6472 (p : Pattern) : d1325 (change p 163 (some 162)) = d4872 p := by
  change (if p 160 then d1324 (change p 163 (some 162)) else d1321 (change p 163 (some 162))) = d4872 p
  rw [sub6471, sub6469]
  rfl
theorem sub6473 (p : Pattern) : d1326 (change p 163 (some 162)) = d132 p := by
  change d1289 (change p 163 (some 162)) = d132 p
  exact sub6448 p
theorem sub6474 (p : Pattern) : d1327 (change p 163 (some 162)) = d4705 p := by
  change (if p 161 then d1300 (change p 163 (some 162)) else d1326 (change p 163 (some 162))) = d4705 p
  rw [sub6445, sub6473]
  rfl
theorem sub6475 (p : Pattern) : d1328 (change p 163 (some 162)) = d4874 p := by
  change (if p 160 then d1293 (change p 163 (some 162)) else d1327 (change p 163 (some 162))) = d4874 p
  rw [sub6438, sub6474]
  rfl
theorem sub6476 (p : Pattern) : d1329 (change p 163 (some 162)) = d4875 p := by
  change (if p 141 then d1328 (change p 163 (some 162)) else d1325 (change p 163 (some 162))) = d4875 p
  rw [sub6475, sub6472]
  rfl
theorem sub6477 (p : Pattern) : d1330 (change p 163 (some 162)) = d4870 p := by
  change (if p 161 then d1298 (change p 163 (some 162)) else d1296 (change p 163 (some 162))) = d4870 p
  rw [sub6443, sub6441]
  rfl
theorem sub6478 (p : Pattern) : d1331 (change p 163 (some 162)) = d4876 p := by
  change (if p 160 then d1301 (change p 163 (some 162)) else d1330 (change p 163 (some 162))) = d4876 p
  rw [sub6446, sub6477]
  rfl
theorem sub6479 (p : Pattern) : d1332 (change p 163 (some 162)) = d132 p := by
  change d1289 (change p 163 (some 162)) = d132 p
  exact sub6448 p
end NetHack.Sokoban22Refined85
