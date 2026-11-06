/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes51
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6240 (p : Pattern) : Int := if p 161 then d6239 p else d6237 p
theorem agree6240 (p q : Pattern) (h : Agree support p q) : d6240 p = d6240 q := by
  simp only [d6240, h 161 (by decide), agree6239 p q h, agree6237 p q h]
theorem nonnegative6240 (p : Pattern) : 0 ≤ d6240 p :=
  nonnegative_ite (p 161) (nonnegative6239 p) (nonnegative6237 p)
def d6241 (p : Pattern) : Int := if p 160 then d6240 p else d6125 p
theorem agree6241 (p q : Pattern) (h : Agree support p q) : d6241 p = d6241 q := by
  simp only [d6241, h 160 (by decide), agree6240 p q h, agree6125 p q h]
theorem nonnegative6241 (p : Pattern) : 0 ≤ d6241 p :=
  nonnegative_ite (p 160) (nonnegative6240 p) (nonnegative6125 p)
def d6242 (p : Pattern) : Int := if p 141 then d6241 p else d6234 p
theorem agree6242 (p q : Pattern) (h : Agree support p q) : d6242 p = d6242 q := by
  simp only [d6242, h 141 (by decide), agree6241 p q h, agree6234 p q h]
theorem nonnegative6242 (p : Pattern) : 0 ≤ d6242 p :=
  nonnegative_ite (p 141) (nonnegative6241 p) (nonnegative6234 p)
def d6243 (p : Pattern) : Int := if p 162 then d6116 p else d6103 p
theorem agree6243 (p q : Pattern) (h : Agree support p q) : d6243 p = d6243 q := by
  simp only [d6243, h 162 (by decide), agree6116 p q h, agree6103 p q h]
theorem nonnegative6243 (p : Pattern) : 0 ≤ d6243 p :=
  nonnegative_ite (p 162) (nonnegative6116 p) (nonnegative6103 p)
def d6244 (p : Pattern) : Int := if p 161 then d6117 p else d6243 p
theorem agree6244 (p q : Pattern) (h : Agree support p q) : d6244 p = d6244 q := by
  simp only [d6244, h 161 (by decide), agree6117 p q h, agree6243 p q h]
theorem nonnegative6244 (p : Pattern) : 0 ≤ d6244 p :=
  nonnegative_ite (p 161) (nonnegative6117 p) (nonnegative6243 p)
def d6245 (p : Pattern) : Int := if p 204 then d315 p else d191 p
theorem agree6245 (p q : Pattern) (h : Agree support p q) : d6245 p = d6245 q := by
  simp only [d6245, h 204 (by decide), agree315 p q h, agree191 p q h]
theorem nonnegative6245 (p : Pattern) : 0 ≤ d6245 p :=
  nonnegative_ite (p 204) (nonnegative315 p) (nonnegative191 p)
def d6246 (p : Pattern) : Int := if p 204 then d12 p else d315 p
theorem agree6246 (p q : Pattern) (h : Agree support p q) : d6246 p = d6246 q := by
  simp only [d6246, h 204 (by decide), agree12 p q h, agree315 p q h]
theorem nonnegative6246 (p : Pattern) : 0 ≤ d6246 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative315 p)
def d6247 (p : Pattern) : Int := if p 182 then d6246 p else d6245 p
theorem agree6247 (p q : Pattern) (h : Agree support p q) : d6247 p = d6247 q := by
  simp only [d6247, h 182 (by decide), agree6246 p q h, agree6245 p q h]
theorem nonnegative6247 (p : Pattern) : 0 ≤ d6247 p :=
  nonnegative_ite (p 182) (nonnegative6246 p) (nonnegative6245 p)
def d6248 (p : Pattern) : Int := if p 163 then d6247 p else d6105 p
theorem agree6248 (p q : Pattern) (h : Agree support p q) : d6248 p = d6248 q := by
  simp only [d6248, h 163 (by decide), agree6247 p q h, agree6105 p q h]
theorem nonnegative6248 (p : Pattern) : 0 ≤ d6248 p :=
  nonnegative_ite (p 163) (nonnegative6247 p) (nonnegative6105 p)
def d6249 (p : Pattern) : Int := if p 162 then d12 p else d6248 p
theorem agree6249 (p q : Pattern) (h : Agree support p q) : d6249 p = d6249 q := by
  simp only [d6249, h 162 (by decide), agree12 p q h, agree6248 p q h]
theorem nonnegative6249 (p : Pattern) : 0 ≤ d6249 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6248 p)
def d6250 (p : Pattern) : Int := if p 161 then d12 p else d6249 p
theorem agree6250 (p q : Pattern) (h : Agree support p q) : d6250 p = d6250 q := by
  simp only [d6250, h 161 (by decide), agree12 p q h, agree6249 p q h]
theorem nonnegative6250 (p : Pattern) : 0 ≤ d6250 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6249 p)
def d6251 (p : Pattern) : Int := if p 160 then d6250 p else d6244 p
theorem agree6251 (p q : Pattern) (h : Agree support p q) : d6251 p = d6251 q := by
  simp only [d6251, h 160 (by decide), agree6250 p q h, agree6244 p q h]
theorem nonnegative6251 (p : Pattern) : 0 ≤ d6251 p :=
  nonnegative_ite (p 160) (nonnegative6250 p) (nonnegative6244 p)
def d6252 (p : Pattern) : Int := if p 163 then d6086 p else d6105 p
theorem agree6252 (p q : Pattern) (h : Agree support p q) : d6252 p = d6252 q := by
  simp only [d6252, h 163 (by decide), agree6086 p q h, agree6105 p q h]
theorem nonnegative6252 (p : Pattern) : 0 ≤ d6252 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6105 p)
def d6253 (p : Pattern) : Int := if p 162 then d6252 p else d6113 p
theorem agree6253 (p q : Pattern) (h : Agree support p q) : d6253 p = d6253 q := by
  simp only [d6253, h 162 (by decide), agree6252 p q h, agree6113 p q h]
theorem nonnegative6253 (p : Pattern) : 0 ≤ d6253 p :=
  nonnegative_ite (p 162) (nonnegative6252 p) (nonnegative6113 p)
def d6254 (p : Pattern) : Int := if p 161 then d6127 p else d6253 p
theorem agree6254 (p q : Pattern) (h : Agree support p q) : d6254 p = d6254 q := by
  simp only [d6254, h 161 (by decide), agree6127 p q h, agree6253 p q h]
theorem nonnegative6254 (p : Pattern) : 0 ≤ d6254 p :=
  nonnegative_ite (p 161) (nonnegative6127 p) (nonnegative6253 p)
def d6255 (p : Pattern) : Int := if p 163 then d12 p else d6247 p
theorem agree6255 (p q : Pattern) (h : Agree support p q) : d6255 p = d6255 q := by
  simp only [d6255, h 163 (by decide), agree12 p q h, agree6247 p q h]
theorem nonnegative6255 (p : Pattern) : 0 ≤ d6255 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6247 p)
def d6256 (p : Pattern) : Int := if p 162 then d12 p else d6255 p
theorem agree6256 (p q : Pattern) (h : Agree support p q) : d6256 p = d6256 q := by
  simp only [d6256, h 162 (by decide), agree12 p q h, agree6255 p q h]
theorem nonnegative6256 (p : Pattern) : 0 ≤ d6256 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6255 p)
def d6257 (p : Pattern) : Int := if p 161 then d12 p else d6256 p
theorem agree6257 (p q : Pattern) (h : Agree support p q) : d6257 p = d6257 q := by
  simp only [d6257, h 161 (by decide), agree12 p q h, agree6256 p q h]
theorem nonnegative6257 (p : Pattern) : 0 ≤ d6257 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6256 p)
def d6258 (p : Pattern) : Int := if p 160 then d6257 p else d6254 p
theorem agree6258 (p q : Pattern) (h : Agree support p q) : d6258 p = d6258 q := by
  simp only [d6258, h 160 (by decide), agree6257 p q h, agree6254 p q h]
theorem nonnegative6258 (p : Pattern) : 0 ≤ d6258 p :=
  nonnegative_ite (p 160) (nonnegative6257 p) (nonnegative6254 p)
def d6259 (p : Pattern) : Int := if p 141 then d6258 p else d6251 p
theorem agree6259 (p q : Pattern) (h : Agree support p q) : d6259 p = d6259 q := by
  simp only [d6259, h 141 (by decide), agree6258 p q h, agree6251 p q h]
theorem nonnegative6259 (p : Pattern) : 0 ≤ d6259 p :=
  nonnegative_ite (p 141) (nonnegative6258 p) (nonnegative6251 p)
def d6260 (p : Pattern) : Int := if p 138 then d6259 p else d6242 p
theorem agree6260 (p q : Pattern) (h : Agree support p q) : d6260 p = d6260 q := by
  simp only [d6260, h 138 (by decide), agree6259 p q h, agree6242 p q h]
theorem nonnegative6260 (p : Pattern) : 0 ≤ d6260 p :=
  nonnegative_ite (p 138) (nonnegative6259 p) (nonnegative6242 p)
def d6261 (p : Pattern) : Int := if p 138 then d12 p else d6259 p
theorem agree6261 (p q : Pattern) (h : Agree support p q) : d6261 p = d6261 q := by
  simp only [d6261, h 138 (by decide), agree12 p q h, agree6259 p q h]
theorem nonnegative6261 (p : Pattern) : 0 ≤ d6261 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6259 p)
def d6262 (p : Pattern) : Int := if p 116 then d6261 p else d6260 p
theorem agree6262 (p q : Pattern) (h : Agree support p q) : d6262 p = d6262 q := by
  simp only [d6262, h 116 (by decide), agree6261 p q h, agree6260 p q h]
theorem nonnegative6262 (p : Pattern) : 0 ≤ d6262 p :=
  nonnegative_ite (p 116) (nonnegative6261 p) (nonnegative6260 p)
def d6263 (p : Pattern) : Int := if p 115 then d6262 p else d6141 p
theorem agree6263 (p q : Pattern) (h : Agree support p q) : d6263 p = d6263 q := by
  simp only [d6263, h 115 (by decide), agree6262 p q h, agree6141 p q h]
theorem nonnegative6263 (p : Pattern) : 0 ≤ d6263 p :=
  nonnegative_ite (p 115) (nonnegative6262 p) (nonnegative6141 p)
def d6264 (p : Pattern) : Int := if p 71 then d6263 p else d6144 p
theorem agree6264 (p q : Pattern) (h : Agree support p q) : d6264 p = d6264 q := by
  simp only [d6264, h 71 (by decide), agree6263 p q h, agree6144 p q h]
theorem nonnegative6264 (p : Pattern) : 0 ≤ d6264 p :=
  nonnegative_ite (p 71) (nonnegative6263 p) (nonnegative6144 p)
def d6265 (p : Pattern) : Int := if p 163 then d12 p else d6150 p
theorem agree6265 (p q : Pattern) (h : Agree support p q) : d6265 p = d6265 q := by
  simp only [d6265, h 163 (by decide), agree12 p q h, agree6150 p q h]
theorem nonnegative6265 (p : Pattern) : 0 ≤ d6265 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6150 p)
def d6266 (p : Pattern) : Int := if p 162 then d6265 p else d6172 p
theorem agree6266 (p q : Pattern) (h : Agree support p q) : d6266 p = d6266 q := by
  simp only [d6266, h 162 (by decide), agree6265 p q h, agree6172 p q h]
theorem nonnegative6266 (p : Pattern) : 0 ≤ d6266 p :=
  nonnegative_ite (p 162) (nonnegative6265 p) (nonnegative6172 p)
def d6267 (p : Pattern) : Int := if p 162 then d12 p else d6265 p
theorem agree6267 (p q : Pattern) (h : Agree support p q) : d6267 p = d6267 q := by
  simp only [d6267, h 162 (by decide), agree12 p q h, agree6265 p q h]
theorem nonnegative6267 (p : Pattern) : 0 ≤ d6267 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6265 p)
def d6268 (p : Pattern) : Int := if p 161 then d6267 p else d6266 p
theorem agree6268 (p q : Pattern) (h : Agree support p q) : d6268 p = d6268 q := by
  simp only [d6268, h 161 (by decide), agree6267 p q h, agree6266 p q h]
theorem nonnegative6268 (p : Pattern) : 0 ≤ d6268 p :=
  nonnegative_ite (p 161) (nonnegative6267 p) (nonnegative6266 p)
def d6269 (p : Pattern) : Int := if p 163 then d12 p else d6162 p
theorem agree6269 (p q : Pattern) (h : Agree support p q) : d6269 p = d6269 q := by
  simp only [d6269, h 163 (by decide), agree12 p q h, agree6162 p q h]
theorem nonnegative6269 (p : Pattern) : 0 ≤ d6269 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6162 p)
def d6270 (p : Pattern) : Int := if p 162 then d6269 p else d6179 p
theorem agree6270 (p q : Pattern) (h : Agree support p q) : d6270 p = d6270 q := by
  simp only [d6270, h 162 (by decide), agree6269 p q h, agree6179 p q h]
theorem nonnegative6270 (p : Pattern) : 0 ≤ d6270 p :=
  nonnegative_ite (p 162) (nonnegative6269 p) (nonnegative6179 p)
def d6271 (p : Pattern) : Int := if p 162 then d12 p else d6269 p
theorem agree6271 (p q : Pattern) (h : Agree support p q) : d6271 p = d6271 q := by
  simp only [d6271, h 162 (by decide), agree12 p q h, agree6269 p q h]
theorem nonnegative6271 (p : Pattern) : 0 ≤ d6271 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6269 p)
def d6272 (p : Pattern) : Int := if p 161 then d6271 p else d6270 p
theorem agree6272 (p q : Pattern) (h : Agree support p q) : d6272 p = d6272 q := by
  simp only [d6272, h 161 (by decide), agree6271 p q h, agree6270 p q h]
theorem nonnegative6272 (p : Pattern) : 0 ≤ d6272 p :=
  nonnegative_ite (p 161) (nonnegative6271 p) (nonnegative6270 p)
def d6273 (p : Pattern) : Int := if p 160 then d6272 p else d6268 p
theorem agree6273 (p q : Pattern) (h : Agree support p q) : d6273 p = d6273 q := by
  simp only [d6273, h 160 (by decide), agree6272 p q h, agree6268 p q h]
theorem nonnegative6273 (p : Pattern) : 0 ≤ d6273 p :=
  nonnegative_ite (p 160) (nonnegative6272 p) (nonnegative6268 p)
def d6274 (p : Pattern) : Int := if p 141 then d6273 p else d6168 p
theorem agree6274 (p q : Pattern) (h : Agree support p q) : d6274 p = d6274 q := by
  simp only [d6274, h 141 (by decide), agree6273 p q h, agree6168 p q h]
theorem nonnegative6274 (p : Pattern) : 0 ≤ d6274 p :=
  nonnegative_ite (p 141) (nonnegative6273 p) (nonnegative6168 p)
def d6275 (p : Pattern) : Int := if p 163 then d12 p else d6190 p
theorem agree6275 (p q : Pattern) (h : Agree support p q) : d6275 p = d6275 q := by
  simp only [d6275, h 163 (by decide), agree12 p q h, agree6190 p q h]
theorem nonnegative6275 (p : Pattern) : 0 ≤ d6275 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6190 p)
def d6276 (p : Pattern) : Int := if p 162 then d6275 p else d6202 p
theorem agree6276 (p q : Pattern) (h : Agree support p q) : d6276 p = d6276 q := by
  simp only [d6276, h 162 (by decide), agree6275 p q h, agree6202 p q h]
theorem nonnegative6276 (p : Pattern) : 0 ≤ d6276 p :=
  nonnegative_ite (p 162) (nonnegative6275 p) (nonnegative6202 p)
def d6277 (p : Pattern) : Int := if p 162 then d12 p else d6275 p
theorem agree6277 (p q : Pattern) (h : Agree support p q) : d6277 p = d6277 q := by
  simp only [d6277, h 162 (by decide), agree12 p q h, agree6275 p q h]
theorem nonnegative6277 (p : Pattern) : 0 ≤ d6277 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6275 p)
def d6278 (p : Pattern) : Int := if p 161 then d6277 p else d6276 p
theorem agree6278 (p q : Pattern) (h : Agree support p q) : d6278 p = d6278 q := by
  simp only [d6278, h 161 (by decide), agree6277 p q h, agree6276 p q h]
theorem nonnegative6278 (p : Pattern) : 0 ≤ d6278 p :=
  nonnegative_ite (p 161) (nonnegative6277 p) (nonnegative6276 p)
def d6279 (p : Pattern) : Int := if p 160 then d6210 p else d6278 p
theorem agree6279 (p q : Pattern) (h : Agree support p q) : d6279 p = d6279 q := by
  simp only [d6279, h 160 (by decide), agree6210 p q h, agree6278 p q h]
theorem nonnegative6279 (p : Pattern) : 0 ≤ d6279 p :=
  nonnegative_ite (p 160) (nonnegative6210 p) (nonnegative6278 p)
def d6280 (p : Pattern) : Int := if p 141 then d6279 p else d6201 p
theorem agree6280 (p q : Pattern) (h : Agree support p q) : d6280 p = d6280 q := by
  simp only [d6280, h 141 (by decide), agree6279 p q h, agree6201 p q h]
theorem nonnegative6280 (p : Pattern) : 0 ≤ d6280 p :=
  nonnegative_ite (p 141) (nonnegative6279 p) (nonnegative6201 p)
def d6281 (p : Pattern) : Int := if p 138 then d6280 p else d6274 p
theorem agree6281 (p q : Pattern) (h : Agree support p q) : d6281 p = d6281 q := by
  simp only [d6281, h 138 (by decide), agree6280 p q h, agree6274 p q h]
theorem nonnegative6281 (p : Pattern) : 0 ≤ d6281 p :=
  nonnegative_ite (p 138) (nonnegative6280 p) (nonnegative6274 p)
def d6282 (p : Pattern) : Int := if p 138 then d6217 p else d6280 p
theorem agree6282 (p q : Pattern) (h : Agree support p q) : d6282 p = d6282 q := by
  simp only [d6282, h 138 (by decide), agree6217 p q h, agree6280 p q h]
theorem nonnegative6282 (p : Pattern) : 0 ≤ d6282 p :=
  nonnegative_ite (p 138) (nonnegative6217 p) (nonnegative6280 p)
def d6283 (p : Pattern) : Int := if p 116 then d6282 p else d6281 p
theorem agree6283 (p q : Pattern) (h : Agree support p q) : d6283 p = d6283 q := by
  simp only [d6283, h 116 (by decide), agree6282 p q h, agree6281 p q h]
theorem nonnegative6283 (p : Pattern) : 0 ≤ d6283 p :=
  nonnegative_ite (p 116) (nonnegative6282 p) (nonnegative6281 p)
def d6284 (p : Pattern) : Int := if p 182 then d6158 p else d6169 p
theorem agree6284 (p q : Pattern) (h : Agree support p q) : d6284 p = d6284 q := by
  simp only [d6284, h 182 (by decide), agree6158 p q h, agree6169 p q h]
theorem nonnegative6284 (p : Pattern) : 0 ≤ d6284 p :=
  nonnegative_ite (p 182) (nonnegative6158 p) (nonnegative6169 p)
def d6285 (p : Pattern) : Int := if p 163 then d6284 p else d6195 p
theorem agree6285 (p q : Pattern) (h : Agree support p q) : d6285 p = d6285 q := by
  simp only [d6285, h 163 (by decide), agree6284 p q h, agree6195 p q h]
theorem nonnegative6285 (p : Pattern) : 0 ≤ d6285 p :=
  nonnegative_ite (p 163) (nonnegative6284 p) (nonnegative6195 p)
def d6286 (p : Pattern) : Int := if p 162 then d6269 p else d6285 p
theorem agree6286 (p q : Pattern) (h : Agree support p q) : d6286 p = d6286 q := by
  simp only [d6286, h 162 (by decide), agree6269 p q h, agree6285 p q h]
theorem nonnegative6286 (p : Pattern) : 0 ≤ d6286 p :=
  nonnegative_ite (p 162) (nonnegative6269 p) (nonnegative6285 p)
def d6287 (p : Pattern) : Int := if p 182 then d12 p else d6196 p
theorem agree6287 (p q : Pattern) (h : Agree support p q) : d6287 p = d6287 q := by
  simp only [d6287, h 182 (by decide), agree12 p q h, agree6196 p q h]
theorem nonnegative6287 (p : Pattern) : 0 ≤ d6287 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative6196 p)
def d6288 (p : Pattern) : Int := if p 163 then d12 p else d6287 p
theorem agree6288 (p q : Pattern) (h : Agree support p q) : d6288 p = d6288 q := by
  simp only [d6288, h 163 (by decide), agree12 p q h, agree6287 p q h]
theorem nonnegative6288 (p : Pattern) : 0 ≤ d6288 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6287 p)
def d6289 (p : Pattern) : Int := if p 162 then d12 p else d6288 p
theorem agree6289 (p q : Pattern) (h : Agree support p q) : d6289 p = d6289 q := by
  simp only [d6289, h 162 (by decide), agree12 p q h, agree6288 p q h]
theorem nonnegative6289 (p : Pattern) : 0 ≤ d6289 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6288 p)
def d6290 (p : Pattern) : Int := if p 161 then d6289 p else d6286 p
theorem agree6290 (p q : Pattern) (h : Agree support p q) : d6290 p = d6290 q := by
  simp only [d6290, h 161 (by decide), agree6289 p q h, agree6286 p q h]
theorem nonnegative6290 (p : Pattern) : 0 ≤ d6290 p :=
  nonnegative_ite (p 161) (nonnegative6289 p) (nonnegative6286 p)
def d6291 (p : Pattern) : Int := if p 160 then d6290 p else d6194 p
theorem agree6291 (p q : Pattern) (h : Agree support p q) : d6291 p = d6291 q := by
  simp only [d6291, h 160 (by decide), agree6290 p q h, agree6194 p q h]
theorem nonnegative6291 (p : Pattern) : 0 ≤ d6291 p :=
  nonnegative_ite (p 160) (nonnegative6290 p) (nonnegative6194 p)
def d6292 (p : Pattern) : Int := if p 182 then d6158 p else d6148 p
theorem agree6292 (p q : Pattern) (h : Agree support p q) : d6292 p = d6292 q := by
  simp only [d6292, h 182 (by decide), agree6158 p q h, agree6148 p q h]
theorem nonnegative6292 (p : Pattern) : 0 ≤ d6292 p :=
  nonnegative_ite (p 182) (nonnegative6158 p) (nonnegative6148 p)
def d6293 (p : Pattern) : Int := if p 163 then d6162 p else d6292 p
theorem agree6293 (p q : Pattern) (h : Agree support p q) : d6293 p = d6293 q := by
  simp only [d6293, h 163 (by decide), agree6162 p q h, agree6292 p q h]
theorem nonnegative6293 (p : Pattern) : 0 ≤ d6293 p :=
  nonnegative_ite (p 163) (nonnegative6162 p) (nonnegative6292 p)
def d6294 (p : Pattern) : Int := if p 162 then d6288 p else d6293 p
theorem agree6294 (p q : Pattern) (h : Agree support p q) : d6294 p = d6294 q := by
  simp only [d6294, h 162 (by decide), agree6288 p q h, agree6293 p q h]
theorem nonnegative6294 (p : Pattern) : 0 ≤ d6294 p :=
  nonnegative_ite (p 162) (nonnegative6288 p) (nonnegative6293 p)
def d6295 (p : Pattern) : Int := if p 162 then d12 p else d6071 p
theorem agree6295 (p q : Pattern) (h : Agree support p q) : d6295 p = d6295 q := by
  simp only [d6295, h 162 (by decide), agree12 p q h, agree6071 p q h]
theorem nonnegative6295 (p : Pattern) : 0 ≤ d6295 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6071 p)
def d6296 (p : Pattern) : Int := if p 161 then d6295 p else d6294 p
theorem agree6296 (p q : Pattern) (h : Agree support p q) : d6296 p = d6296 q := by
  simp only [d6296, h 161 (by decide), agree6295 p q h, agree6294 p q h]
theorem nonnegative6296 (p : Pattern) : 0 ≤ d6296 p :=
  nonnegative_ite (p 161) (nonnegative6295 p) (nonnegative6294 p)
def d6297 (p : Pattern) : Int := if p 160 then d6296 p else d6278 p
theorem agree6297 (p q : Pattern) (h : Agree support p q) : d6297 p = d6297 q := by
  simp only [d6297, h 160 (by decide), agree6296 p q h, agree6278 p q h]
theorem nonnegative6297 (p : Pattern) : 0 ≤ d6297 p :=
  nonnegative_ite (p 160) (nonnegative6296 p) (nonnegative6278 p)
def d6298 (p : Pattern) : Int := if p 141 then d6297 p else d6291 p
theorem agree6298 (p q : Pattern) (h : Agree support p q) : d6298 p = d6298 q := by
  simp only [d6298, h 141 (by decide), agree6297 p q h, agree6291 p q h]
theorem nonnegative6298 (p : Pattern) : 0 ≤ d6298 p :=
  nonnegative_ite (p 141) (nonnegative6297 p) (nonnegative6291 p)
def d6299 (p : Pattern) : Int := if p 163 then d6086 p else d6195 p
theorem agree6299 (p q : Pattern) (h : Agree support p q) : d6299 p = d6299 q := by
  simp only [d6299, h 163 (by decide), agree6086 p q h, agree6195 p q h]
theorem nonnegative6299 (p : Pattern) : 0 ≤ d6299 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6195 p)
def d6300 (p : Pattern) : Int := if p 162 then d6299 p else d6188 p
theorem agree6300 (p q : Pattern) (h : Agree support p q) : d6300 p = d6300 q := by
  simp only [d6300, h 162 (by decide), agree6299 p q h, agree6188 p q h]
theorem nonnegative6300 (p : Pattern) : 0 ≤ d6300 p :=
  nonnegative_ite (p 162) (nonnegative6299 p) (nonnegative6188 p)
def d6301 (p : Pattern) : Int := if p 161 then d6206 p else d6300 p
theorem agree6301 (p q : Pattern) (h : Agree support p q) : d6301 p = d6301 q := by
  simp only [d6301, h 161 (by decide), agree6206 p q h, agree6300 p q h]
theorem nonnegative6301 (p : Pattern) : 0 ≤ d6301 p :=
  nonnegative_ite (p 161) (nonnegative6206 p) (nonnegative6300 p)
def d6302 (p : Pattern) : Int := if p 160 then d6210 p else d6301 p
theorem agree6302 (p q : Pattern) (h : Agree support p q) : d6302 p = d6302 q := by
  simp only [d6302, h 160 (by decide), agree6210 p q h, agree6301 p q h]
theorem nonnegative6302 (p : Pattern) : 0 ≤ d6302 p :=
  nonnegative_ite (p 160) (nonnegative6210 p) (nonnegative6301 p)
def d6303 (p : Pattern) : Int := if p 162 then d6275 p else d6195 p
theorem agree6303 (p q : Pattern) (h : Agree support p q) : d6303 p = d6303 q := by
  simp only [d6303, h 162 (by decide), agree6275 p q h, agree6195 p q h]
theorem nonnegative6303 (p : Pattern) : 0 ≤ d6303 p :=
  nonnegative_ite (p 162) (nonnegative6275 p) (nonnegative6195 p)
def d6304 (p : Pattern) : Int := if p 161 then d6209 p else d6303 p
theorem agree6304 (p q : Pattern) (h : Agree support p q) : d6304 p = d6304 q := by
  simp only [d6304, h 161 (by decide), agree6209 p q h, agree6303 p q h]
theorem nonnegative6304 (p : Pattern) : 0 ≤ d6304 p :=
  nonnegative_ite (p 161) (nonnegative6209 p) (nonnegative6303 p)
def d6305 (p : Pattern) : Int := if p 162 then d12 p else d6110 p
theorem agree6305 (p q : Pattern) (h : Agree support p q) : d6305 p = d6305 q := by
  simp only [d6305, h 162 (by decide), agree12 p q h, agree6110 p q h]
theorem nonnegative6305 (p : Pattern) : 0 ≤ d6305 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6110 p)
def d6306 (p : Pattern) : Int := if p 161 then d12 p else d6305 p
theorem agree6306 (p q : Pattern) (h : Agree support p q) : d6306 p = d6306 q := by
  simp only [d6306, h 161 (by decide), agree12 p q h, agree6305 p q h]
theorem nonnegative6306 (p : Pattern) : 0 ≤ d6306 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6305 p)
def d6307 (p : Pattern) : Int := if p 160 then d6306 p else d6304 p
theorem agree6307 (p q : Pattern) (h : Agree support p q) : d6307 p = d6307 q := by
  simp only [d6307, h 160 (by decide), agree6306 p q h, agree6304 p q h]
theorem nonnegative6307 (p : Pattern) : 0 ≤ d6307 p :=
  nonnegative_ite (p 160) (nonnegative6306 p) (nonnegative6304 p)
def d6308 (p : Pattern) : Int := if p 141 then d6307 p else d6302 p
theorem agree6308 (p q : Pattern) (h : Agree support p q) : d6308 p = d6308 q := by
  simp only [d6308, h 141 (by decide), agree6307 p q h, agree6302 p q h]
theorem nonnegative6308 (p : Pattern) : 0 ≤ d6308 p :=
  nonnegative_ite (p 141) (nonnegative6307 p) (nonnegative6302 p)
def d6309 (p : Pattern) : Int := if p 138 then d6308 p else d6298 p
theorem agree6309 (p q : Pattern) (h : Agree support p q) : d6309 p = d6309 q := by
  simp only [d6309, h 138 (by decide), agree6308 p q h, agree6298 p q h]
theorem nonnegative6309 (p : Pattern) : 0 ≤ d6309 p :=
  nonnegative_ite (p 138) (nonnegative6308 p) (nonnegative6298 p)
def d6310 (p : Pattern) : Int := if p 163 then d6109 p else d6195 p
theorem agree6310 (p q : Pattern) (h : Agree support p q) : d6310 p = d6310 q := by
  simp only [d6310, h 163 (by decide), agree6109 p q h, agree6195 p q h]
theorem nonnegative6310 (p : Pattern) : 0 ≤ d6310 p :=
  nonnegative_ite (p 163) (nonnegative6109 p) (nonnegative6195 p)
def d6311 (p : Pattern) : Int := if p 162 then d6310 p else d6188 p
theorem agree6311 (p q : Pattern) (h : Agree support p q) : d6311 p = d6311 q := by
  simp only [d6311, h 162 (by decide), agree6310 p q h, agree6188 p q h]
theorem nonnegative6311 (p : Pattern) : 0 ≤ d6311 p :=
  nonnegative_ite (p 162) (nonnegative6310 p) (nonnegative6188 p)
def d6312 (p : Pattern) : Int := if p 163 then d6109 p else d6190 p
theorem agree6312 (p q : Pattern) (h : Agree support p q) : d6312 p = d6312 q := by
  simp only [d6312, h 163 (by decide), agree6109 p q h, agree6190 p q h]
theorem nonnegative6312 (p : Pattern) : 0 ≤ d6312 p :=
  nonnegative_ite (p 163) (nonnegative6109 p) (nonnegative6190 p)
def d6313 (p : Pattern) : Int := if p 162 then d12 p else d6312 p
theorem agree6313 (p q : Pattern) (h : Agree support p q) : d6313 p = d6313 q := by
  simp only [d6313, h 162 (by decide), agree12 p q h, agree6312 p q h]
theorem nonnegative6313 (p : Pattern) : 0 ≤ d6313 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6312 p)
def d6314 (p : Pattern) : Int := if p 161 then d6313 p else d6311 p
theorem agree6314 (p q : Pattern) (h : Agree support p q) : d6314 p = d6314 q := by
  simp only [d6314, h 161 (by decide), agree6313 p q h, agree6311 p q h]
theorem nonnegative6314 (p : Pattern) : 0 ≤ d6314 p :=
  nonnegative_ite (p 161) (nonnegative6313 p) (nonnegative6311 p)
def d6315 (p : Pattern) : Int := if p 163 then d6086 p else d6197 p
theorem agree6315 (p q : Pattern) (h : Agree support p q) : d6315 p = d6315 q := by
  simp only [d6315, h 163 (by decide), agree6086 p q h, agree6197 p q h]
theorem nonnegative6315 (p : Pattern) : 0 ≤ d6315 p :=
  nonnegative_ite (p 163) (nonnegative6086 p) (nonnegative6197 p)
def d6316 (p : Pattern) : Int := if p 162 then d12 p else d6315 p
theorem agree6316 (p q : Pattern) (h : Agree support p q) : d6316 p = d6316 q := by
  simp only [d6316, h 162 (by decide), agree12 p q h, agree6315 p q h]
theorem nonnegative6316 (p : Pattern) : 0 ≤ d6316 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6315 p)
def d6317 (p : Pattern) : Int := if p 161 then d12 p else d6316 p
theorem agree6317 (p q : Pattern) (h : Agree support p q) : d6317 p = d6317 q := by
  simp only [d6317, h 161 (by decide), agree12 p q h, agree6316 p q h]
theorem nonnegative6317 (p : Pattern) : 0 ≤ d6317 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6316 p)
def d6318 (p : Pattern) : Int := if p 160 then d6317 p else d6314 p
theorem agree6318 (p q : Pattern) (h : Agree support p q) : d6318 p = d6318 q := by
  simp only [d6318, h 160 (by decide), agree6317 p q h, agree6314 p q h]
theorem nonnegative6318 (p : Pattern) : 0 ≤ d6318 p :=
  nonnegative_ite (p 160) (nonnegative6317 p) (nonnegative6314 p)
def d6319 (p : Pattern) : Int := if p 141 then d6307 p else d6318 p
theorem agree6319 (p q : Pattern) (h : Agree support p q) : d6319 p = d6319 q := by
  simp only [d6319, h 141 (by decide), agree6307 p q h, agree6318 p q h]
theorem nonnegative6319 (p : Pattern) : 0 ≤ d6319 p :=
  nonnegative_ite (p 141) (nonnegative6307 p) (nonnegative6318 p)
def d6320 (p : Pattern) : Int := if p 138 then d12 p else d6319 p
theorem agree6320 (p q : Pattern) (h : Agree support p q) : d6320 p = d6320 q := by
  simp only [d6320, h 138 (by decide), agree12 p q h, agree6319 p q h]
theorem nonnegative6320 (p : Pattern) : 0 ≤ d6320 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative6319 p)
def d6321 (p : Pattern) : Int := if p 116 then d6320 p else d6309 p
theorem agree6321 (p q : Pattern) (h : Agree support p q) : d6321 p = d6321 q := by
  simp only [d6321, h 116 (by decide), agree6320 p q h, agree6309 p q h]
theorem nonnegative6321 (p : Pattern) : 0 ≤ d6321 p :=
  nonnegative_ite (p 116) (nonnegative6320 p) (nonnegative6309 p)
def d6322 (p : Pattern) : Int := if p 115 then d6321 p else d6283 p
theorem agree6322 (p q : Pattern) (h : Agree support p q) : d6322 p = d6322 q := by
  simp only [d6322, h 115 (by decide), agree6321 p q h, agree6283 p q h]
theorem nonnegative6322 (p : Pattern) : 0 ≤ d6322 p :=
  nonnegative_ite (p 115) (nonnegative6321 p) (nonnegative6283 p)
def d6323 (p : Pattern) : Int := if p 71 then d6322 p else d6144 p
theorem agree6323 (p q : Pattern) (h : Agree support p q) : d6323 p = d6323 q := by
  simp only [d6323, h 71 (by decide), agree6322 p q h, agree6144 p q h]
theorem nonnegative6323 (p : Pattern) : 0 ≤ d6323 p :=
  nonnegative_ite (p 71) (nonnegative6322 p) (nonnegative6144 p)
def d6324 (p : Pattern) : Int := if p 49 then d6323 p else d6264 p
theorem agree6324 (p q : Pattern) (h : Agree support p q) : d6324 p = d6324 q := by
  simp only [d6324, h 49 (by decide), agree6323 p q h, agree6264 p q h]
theorem nonnegative6324 (p : Pattern) : 0 ≤ d6324 p :=
  nonnegative_ite (p 49) (nonnegative6323 p) (nonnegative6264 p)
def d6325 (p : Pattern) : Int := if p 48 then d6324 p else d6224 p
theorem agree6325 (p q : Pattern) (h : Agree support p q) : d6325 p = d6325 q := by
  simp only [d6325, h 48 (by decide), agree6324 p q h, agree6224 p q h]
theorem nonnegative6325 (p : Pattern) : 0 ≤ d6325 p :=
  nonnegative_ite (p 48) (nonnegative6324 p) (nonnegative6224 p)
def d6326 (p : Pattern) : Int := if p 246 then d5843 p else d0 p
theorem agree6326 (p q : Pattern) (h : Agree support p q) : d6326 p = d6326 q := by
  simp only [d6326, h 246 (by decide), agree5843 p q h, agree0 p q h]
theorem nonnegative6326 (p : Pattern) : 0 ≤ d6326 p :=
  nonnegative_ite (p 246) (nonnegative5843 p) (nonnegative0 p)
def d6327 (p : Pattern) : Int := if p 204 then d12 p else d0 p
theorem agree6327 (p q : Pattern) (h : Agree support p q) : d6327 p = d6327 q := by
  simp only [d6327, h 204 (by decide), agree12 p q h, agree0 p q h]
theorem nonnegative6327 (p : Pattern) : 0 ≤ d6327 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative0 p)
def d6328 (p : Pattern) : Int := if p 182 then d6327 p else d0 p
theorem agree6328 (p q : Pattern) (h : Agree support p q) : d6328 p = d6328 q := by
  simp only [d6328, h 182 (by decide), agree6327 p q h, agree0 p q h]
theorem nonnegative6328 (p : Pattern) : 0 ≤ d6328 p :=
  nonnegative_ite (p 182) (nonnegative6327 p) (nonnegative0 p)
def d6329 (p : Pattern) : Int := if p 204 then d12 p else d4 p
theorem agree6329 (p q : Pattern) (h : Agree support p q) : d6329 p = d6329 q := by
  simp only [d6329, h 204 (by decide), agree12 p q h, agree4 p q h]
theorem nonnegative6329 (p : Pattern) : 0 ≤ d6329 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative4 p)
def d6330 (p : Pattern) : Int := if p 182 then d6329 p else d4 p
theorem agree6330 (p q : Pattern) (h : Agree support p q) : d6330 p = d6330 q := by
  simp only [d6330, h 182 (by decide), agree6329 p q h, agree4 p q h]
theorem nonnegative6330 (p : Pattern) : 0 ≤ d6330 p :=
  nonnegative_ite (p 182) (nonnegative6329 p) (nonnegative4 p)
def d6331 (p : Pattern) : Int := if p 163 then d6330 p else d6328 p
theorem agree6331 (p q : Pattern) (h : Agree support p q) : d6331 p = d6331 q := by
  simp only [d6331, h 163 (by decide), agree6330 p q h, agree6328 p q h]
theorem nonnegative6331 (p : Pattern) : 0 ≤ d6331 p :=
  nonnegative_ite (p 163) (nonnegative6330 p) (nonnegative6328 p)
def d6332 (p : Pattern) : Int := if p 162 then d6331 p else d6328 p
theorem agree6332 (p q : Pattern) (h : Agree support p q) : d6332 p = d6332 q := by
  simp only [d6332, h 162 (by decide), agree6331 p q h, agree6328 p q h]
theorem nonnegative6332 (p : Pattern) : 0 ≤ d6332 p :=
  nonnegative_ite (p 162) (nonnegative6331 p) (nonnegative6328 p)
def d6333 (p : Pattern) : Int := if p 204 then d12 p else d9 p
theorem agree6333 (p q : Pattern) (h : Agree support p q) : d6333 p = d6333 q := by
  simp only [d6333, h 204 (by decide), agree12 p q h, agree9 p q h]
theorem nonnegative6333 (p : Pattern) : 0 ≤ d6333 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative9 p)
def d6334 (p : Pattern) : Int := if p 182 then d6333 p else d9 p
theorem agree6334 (p q : Pattern) (h : Agree support p q) : d6334 p = d6334 q := by
  simp only [d6334, h 182 (by decide), agree6333 p q h, agree9 p q h]
theorem nonnegative6334 (p : Pattern) : 0 ≤ d6334 p :=
  nonnegative_ite (p 182) (nonnegative6333 p) (nonnegative9 p)
def d6335 (p : Pattern) : Int := if p 163 then d12 p else d6334 p
theorem agree6335 (p q : Pattern) (h : Agree support p q) : d6335 p = d6335 q := by
  simp only [d6335, h 163 (by decide), agree12 p q h, agree6334 p q h]
theorem nonnegative6335 (p : Pattern) : 0 ≤ d6335 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6334 p)
def d6336 (p : Pattern) : Int := if p 162 then d6335 p else d6331 p
theorem agree6336 (p q : Pattern) (h : Agree support p q) : d6336 p = d6336 q := by
  simp only [d6336, h 162 (by decide), agree6335 p q h, agree6331 p q h]
theorem nonnegative6336 (p : Pattern) : 0 ≤ d6336 p :=
  nonnegative_ite (p 162) (nonnegative6335 p) (nonnegative6331 p)
def d6337 (p : Pattern) : Int := if p 161 then d6336 p else d6332 p
theorem agree6337 (p q : Pattern) (h : Agree support p q) : d6337 p = d6337 q := by
  simp only [d6337, h 161 (by decide), agree6336 p q h, agree6332 p q h]
theorem nonnegative6337 (p : Pattern) : 0 ≤ d6337 p :=
  nonnegative_ite (p 161) (nonnegative6336 p) (nonnegative6332 p)
def d6338 (p : Pattern) : Int := if p 204 then d12 p else d2 p
theorem agree6338 (p q : Pattern) (h : Agree support p q) : d6338 p = d6338 q := by
  simp only [d6338, h 204 (by decide), agree12 p q h, agree2 p q h]
theorem nonnegative6338 (p : Pattern) : 0 ≤ d6338 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2 p)
def d6339 (p : Pattern) : Int := if p 182 then d6338 p else d0 p
theorem agree6339 (p q : Pattern) (h : Agree support p q) : d6339 p = d6339 q := by
  simp only [d6339, h 182 (by decide), agree6338 p q h, agree0 p q h]
theorem nonnegative6339 (p : Pattern) : 0 ≤ d6339 p :=
  nonnegative_ite (p 182) (nonnegative6338 p) (nonnegative0 p)
def d6340 (p : Pattern) : Int := if p 204 then d12 p else d6 p
theorem agree6340 (p q : Pattern) (h : Agree support p q) : d6340 p = d6340 q := by
  simp only [d6340, h 204 (by decide), agree12 p q h, agree6 p q h]
theorem nonnegative6340 (p : Pattern) : 0 ≤ d6340 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6 p)
def d6341 (p : Pattern) : Int := if p 182 then d6340 p else d0 p
theorem agree6341 (p q : Pattern) (h : Agree support p q) : d6341 p = d6341 q := by
  simp only [d6341, h 182 (by decide), agree6340 p q h, agree0 p q h]
theorem nonnegative6341 (p : Pattern) : 0 ≤ d6341 p :=
  nonnegative_ite (p 182) (nonnegative6340 p) (nonnegative0 p)
def d6342 (p : Pattern) : Int := if p 163 then d6341 p else d6339 p
theorem agree6342 (p q : Pattern) (h : Agree support p q) : d6342 p = d6342 q := by
  simp only [d6342, h 163 (by decide), agree6341 p q h, agree6339 p q h]
theorem nonnegative6342 (p : Pattern) : 0 ≤ d6342 p :=
  nonnegative_ite (p 163) (nonnegative6341 p) (nonnegative6339 p)
def d6343 (p : Pattern) : Int := if p 204 then d12 p else d11 p
theorem agree6343 (p q : Pattern) (h : Agree support p q) : d6343 p = d6343 q := by
  simp only [d6343, h 204 (by decide), agree12 p q h, agree11 p q h]
theorem nonnegative6343 (p : Pattern) : 0 ≤ d6343 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative11 p)
def d6344 (p : Pattern) : Int := if p 182 then d6343 p else d0 p
theorem agree6344 (p q : Pattern) (h : Agree support p q) : d6344 p = d6344 q := by
  simp only [d6344, h 182 (by decide), agree6343 p q h, agree0 p q h]
theorem nonnegative6344 (p : Pattern) : 0 ≤ d6344 p :=
  nonnegative_ite (p 182) (nonnegative6343 p) (nonnegative0 p)
def d6345 (p : Pattern) : Int := if p 182 then d12 p else d4 p
theorem agree6345 (p q : Pattern) (h : Agree support p q) : d6345 p = d6345 q := by
  simp only [d6345, h 182 (by decide), agree12 p q h, agree4 p q h]
theorem nonnegative6345 (p : Pattern) : 0 ≤ d6345 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative4 p)
def d6346 (p : Pattern) : Int := if p 163 then d6345 p else d6344 p
theorem agree6346 (p q : Pattern) (h : Agree support p q) : d6346 p = d6346 q := by
  simp only [d6346, h 163 (by decide), agree6345 p q h, agree6344 p q h]
theorem nonnegative6346 (p : Pattern) : 0 ≤ d6346 p :=
  nonnegative_ite (p 163) (nonnegative6345 p) (nonnegative6344 p)
def d6347 (p : Pattern) : Int := if p 162 then d6346 p else d6342 p
theorem agree6347 (p q : Pattern) (h : Agree support p q) : d6347 p = d6347 q := by
  simp only [d6347, h 162 (by decide), agree6346 p q h, agree6342 p q h]
theorem nonnegative6347 (p : Pattern) : 0 ≤ d6347 p :=
  nonnegative_ite (p 162) (nonnegative6346 p) (nonnegative6342 p)
def d6348 (p : Pattern) : Int := if p 182 then d12 p else d0 p
theorem agree6348 (p q : Pattern) (h : Agree support p q) : d6348 p = d6348 q := by
  simp only [d6348, h 182 (by decide), agree12 p q h, agree0 p q h]
theorem nonnegative6348 (p : Pattern) : 0 ≤ d6348 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative0 p)
def d6349 (p : Pattern) : Int := if p 163 then d6345 p else d6348 p
theorem agree6349 (p q : Pattern) (h : Agree support p q) : d6349 p = d6349 q := by
  simp only [d6349, h 163 (by decide), agree6345 p q h, agree6348 p q h]
theorem nonnegative6349 (p : Pattern) : 0 ≤ d6349 p :=
  nonnegative_ite (p 163) (nonnegative6345 p) (nonnegative6348 p)
def d6350 (p : Pattern) : Int := if p 182 then d12 p else d9 p
theorem agree6350 (p q : Pattern) (h : Agree support p q) : d6350 p = d6350 q := by
  simp only [d6350, h 182 (by decide), agree12 p q h, agree9 p q h]
theorem nonnegative6350 (p : Pattern) : 0 ≤ d6350 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative9 p)
def d6351 (p : Pattern) : Int := if p 163 then d12 p else d6350 p
theorem agree6351 (p q : Pattern) (h : Agree support p q) : d6351 p = d6351 q := by
  simp only [d6351, h 163 (by decide), agree12 p q h, agree6350 p q h]
theorem nonnegative6351 (p : Pattern) : 0 ≤ d6351 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6350 p)
def d6352 (p : Pattern) : Int := if p 162 then d6351 p else d6349 p
theorem agree6352 (p q : Pattern) (h : Agree support p q) : d6352 p = d6352 q := by
  simp only [d6352, h 162 (by decide), agree6351 p q h, agree6349 p q h]
theorem nonnegative6352 (p : Pattern) : 0 ≤ d6352 p :=
  nonnegative_ite (p 162) (nonnegative6351 p) (nonnegative6349 p)
def d6353 (p : Pattern) : Int := if p 161 then d6352 p else d6347 p
theorem agree6353 (p q : Pattern) (h : Agree support p q) : d6353 p = d6353 q := by
  simp only [d6353, h 161 (by decide), agree6352 p q h, agree6347 p q h]
theorem nonnegative6353 (p : Pattern) : 0 ≤ d6353 p :=
  nonnegative_ite (p 161) (nonnegative6352 p) (nonnegative6347 p)
def d6354 (p : Pattern) : Int := if p 160 then d6353 p else d6337 p
theorem agree6354 (p q : Pattern) (h : Agree support p q) : d6354 p = d6354 q := by
  simp only [d6354, h 160 (by decide), agree6353 p q h, agree6337 p q h]
theorem nonnegative6354 (p : Pattern) : 0 ≤ d6354 p :=
  nonnegative_ite (p 160) (nonnegative6353 p) (nonnegative6337 p)
def d6355 (p : Pattern) : Int := if p 182 then d6338 p else d2 p
theorem agree6355 (p q : Pattern) (h : Agree support p q) : d6355 p = d6355 q := by
  simp only [d6355, h 182 (by decide), agree6338 p q h, agree2 p q h]
theorem nonnegative6355 (p : Pattern) : 0 ≤ d6355 p :=
  nonnegative_ite (p 182) (nonnegative6338 p) (nonnegative2 p)
def d6356 (p : Pattern) : Int := if p 163 then d6355 p else d6328 p
theorem agree6356 (p q : Pattern) (h : Agree support p q) : d6356 p = d6356 q := by
  simp only [d6356, h 163 (by decide), agree6355 p q h, agree6328 p q h]
theorem nonnegative6356 (p : Pattern) : 0 ≤ d6356 p :=
  nonnegative_ite (p 163) (nonnegative6355 p) (nonnegative6328 p)
def d6357 (p : Pattern) : Int := if p 163 then d6334 p else d6330 p
theorem agree6357 (p q : Pattern) (h : Agree support p q) : d6357 p = d6357 q := by
  simp only [d6357, h 163 (by decide), agree6334 p q h, agree6330 p q h]
theorem nonnegative6357 (p : Pattern) : 0 ≤ d6357 p :=
  nonnegative_ite (p 163) (nonnegative6334 p) (nonnegative6330 p)
def d6358 (p : Pattern) : Int := if p 162 then d6357 p else d6356 p
theorem agree6358 (p q : Pattern) (h : Agree support p q) : d6358 p = d6358 q := by
  simp only [d6358, h 162 (by decide), agree6357 p q h, agree6356 p q h]
theorem nonnegative6358 (p : Pattern) : 0 ≤ d6358 p :=
  nonnegative_ite (p 162) (nonnegative6357 p) (nonnegative6356 p)
def d6359 (p : Pattern) : Int := if p 204 then d12 p else d10 p
theorem agree6359 (p q : Pattern) (h : Agree support p q) : d6359 p = d6359 q := by
  simp only [d6359, h 204 (by decide), agree12 p q h, agree10 p q h]
theorem nonnegative6359 (p : Pattern) : 0 ≤ d6359 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative10 p)
end NetHack.Sokoban22Refined85
