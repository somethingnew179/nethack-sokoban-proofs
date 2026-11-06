/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Nodes01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d240 (p : Pattern) : Int := if p 158 then d65 p else d129 p
theorem agree240 (p q : Pattern) (h : Agree support p q) : d240 p = d240 q := by
  simp only [d240, h 158 (by decide), agree65 p q h, agree129 p q h]
theorem nonnegative240 (p : Pattern) : 0 ≤ d240 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative129 p)
def d241 (p : Pattern) : Int := if p 141 then d240 p else d181 p
theorem agree241 (p q : Pattern) (h : Agree support p q) : d241 p = d241 q := by
  simp only [d241, h 141 (by decide), agree240 p q h, agree181 p q h]
theorem nonnegative241 (p : Pattern) : 0 ≤ d241 p :=
  nonnegative_ite (p 141) (nonnegative240 p) (nonnegative181 p)
def d242 (p : Pattern) : Int := if p 134 then d241 p else d70 p
theorem agree242 (p q : Pattern) (h : Agree support p q) : d242 p = d242 q := by
  simp only [d242, h 134 (by decide), agree241 p q h, agree70 p q h]
theorem nonnegative242 (p : Pattern) : 0 ≤ d242 p :=
  nonnegative_ite (p 134) (nonnegative241 p) (nonnegative70 p)
def d243 (p : Pattern) : Int := if p 133 then d242 p else d239 p
theorem agree243 (p q : Pattern) (h : Agree support p q) : d243 p = d243 q := by
  simp only [d243, h 133 (by decide), agree242 p q h, agree239 p q h]
theorem nonnegative243 (p : Pattern) : 0 ≤ d243 p :=
  nonnegative_ite (p 133) (nonnegative242 p) (nonnegative239 p)
def d244 (p : Pattern) : Int := if p 133 then d66 p else d242 p
theorem agree244 (p q : Pattern) (h : Agree support p q) : d244 p = d244 q := by
  simp only [d244, h 133 (by decide), agree66 p q h, agree242 p q h]
theorem nonnegative244 (p : Pattern) : 0 ≤ d244 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative242 p)
def d245 (p : Pattern) : Int := if p 132 then d244 p else d243 p
theorem agree245 (p q : Pattern) (h : Agree support p q) : d245 p = d245 q := by
  simp only [d245, h 132 (by decide), agree244 p q h, agree243 p q h]
theorem nonnegative245 (p : Pattern) : 0 ≤ d245 p :=
  nonnegative_ite (p 132) (nonnegative244 p) (nonnegative243 p)
def d246 (p : Pattern) : Int := if p 158 then d155 p else d63 p
theorem agree246 (p q : Pattern) (h : Agree support p q) : d246 p = d246 q := by
  simp only [d246, h 158 (by decide), agree155 p q h, agree63 p q h]
theorem nonnegative246 (p : Pattern) : 0 ≤ d246 p :=
  nonnegative_ite (p 158) (nonnegative155 p) (nonnegative63 p)
def d247 (p : Pattern) : Int := if p 141 then d246 p else d186 p
theorem agree247 (p q : Pattern) (h : Agree support p q) : d247 p = d247 q := by
  simp only [d247, h 141 (by decide), agree246 p q h, agree186 p q h]
theorem nonnegative247 (p : Pattern) : 0 ≤ d247 p :=
  nonnegative_ite (p 141) (nonnegative246 p) (nonnegative186 p)
def d248 (p : Pattern) : Int := if p 134 then d66 p else d247 p
theorem agree248 (p q : Pattern) (h : Agree support p q) : d248 p = d248 q := by
  simp only [d248, h 134 (by decide), agree66 p q h, agree247 p q h]
theorem nonnegative248 (p : Pattern) : 0 ≤ d248 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative247 p)
def d249 (p : Pattern) : Int := if p 158 then d65 p else d147 p
theorem agree249 (p q : Pattern) (h : Agree support p q) : d249 p = d249 q := by
  simp only [d249, h 158 (by decide), agree65 p q h, agree147 p q h]
theorem nonnegative249 (p : Pattern) : 0 ≤ d249 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative147 p)
def d250 (p : Pattern) : Int := if p 141 then d249 p else d188 p
theorem agree250 (p q : Pattern) (h : Agree support p q) : d250 p = d250 q := by
  simp only [d250, h 141 (by decide), agree249 p q h, agree188 p q h]
theorem nonnegative250 (p : Pattern) : 0 ≤ d250 p :=
  nonnegative_ite (p 141) (nonnegative249 p) (nonnegative188 p)
def d251 (p : Pattern) : Int := if p 134 then d66 p else d250 p
theorem agree251 (p q : Pattern) (h : Agree support p q) : d251 p = d251 q := by
  simp only [d251, h 134 (by decide), agree66 p q h, agree250 p q h]
theorem nonnegative251 (p : Pattern) : 0 ≤ d251 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative250 p)
def d252 (p : Pattern) : Int := if p 133 then d251 p else d248 p
theorem agree252 (p q : Pattern) (h : Agree support p q) : d252 p = d252 q := by
  simp only [d252, h 133 (by decide), agree251 p q h, agree248 p q h]
theorem nonnegative252 (p : Pattern) : 0 ≤ d252 p :=
  nonnegative_ite (p 133) (nonnegative251 p) (nonnegative248 p)
def d253 (p : Pattern) : Int := if p 158 then d65 p else d155 p
theorem agree253 (p q : Pattern) (h : Agree support p q) : d253 p = d253 q := by
  simp only [d253, h 158 (by decide), agree65 p q h, agree155 p q h]
theorem nonnegative253 (p : Pattern) : 0 ≤ d253 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative155 p)
def d254 (p : Pattern) : Int := if p 141 then d253 p else d191 p
theorem agree254 (p q : Pattern) (h : Agree support p q) : d254 p = d254 q := by
  simp only [d254, h 141 (by decide), agree253 p q h, agree191 p q h]
theorem nonnegative254 (p : Pattern) : 0 ≤ d254 p :=
  nonnegative_ite (p 141) (nonnegative253 p) (nonnegative191 p)
def d255 (p : Pattern) : Int := if p 134 then d66 p else d254 p
theorem agree255 (p q : Pattern) (h : Agree support p q) : d255 p = d255 q := by
  simp only [d255, h 134 (by decide), agree66 p q h, agree254 p q h]
theorem nonnegative255 (p : Pattern) : 0 ≤ d255 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative254 p)
def d256 (p : Pattern) : Int := if p 133 then d66 p else d255 p
theorem agree256 (p q : Pattern) (h : Agree support p q) : d256 p = d256 q := by
  simp only [d256, h 133 (by decide), agree66 p q h, agree255 p q h]
theorem nonnegative256 (p : Pattern) : 0 ≤ d256 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative255 p)
def d257 (p : Pattern) : Int := if p 132 then d256 p else d252 p
theorem agree257 (p q : Pattern) (h : Agree support p q) : d257 p = d257 q := by
  simp only [d257, h 132 (by decide), agree256 p q h, agree252 p q h]
theorem nonnegative257 (p : Pattern) : 0 ≤ d257 p :=
  nonnegative_ite (p 132) (nonnegative256 p) (nonnegative252 p)
def d258 (p : Pattern) : Int := if p 108 then d257 p else d245 p
theorem agree258 (p q : Pattern) (h : Agree support p q) : d258 p = d258 q := by
  simp only [d258, h 108 (by decide), agree257 p q h, agree245 p q h]
theorem nonnegative258 (p : Pattern) : 0 ≤ d258 p :=
  nonnegative_ite (p 108) (nonnegative257 p) (nonnegative245 p)
def d259 (p : Pattern) : Int := if p 193 then d58 p else d2 p
theorem agree259 (p q : Pattern) (h : Agree support p q) : d259 p = d259 q := by
  simp only [d259, h 193 (by decide), agree58 p q h, agree2 p q h]
theorem nonnegative259 (p : Pattern) : 0 ≤ d259 p :=
  nonnegative_ite (p 193) (nonnegative58 p) (nonnegative2 p)
def d260 (p : Pattern) : Int := if p 192 then d5 p else d259 p
theorem agree260 (p q : Pattern) (h : Agree support p q) : d260 p = d260 q := by
  simp only [d260, h 192 (by decide), agree5 p q h, agree259 p q h]
theorem nonnegative260 (p : Pattern) : 0 ≤ d260 p :=
  nonnegative_ite (p 192) (nonnegative5 p) (nonnegative259 p)
def d261 (p : Pattern) : Int := if p 186 then d260 p else d15 p
theorem agree261 (p q : Pattern) (h : Agree support p q) : d261 p = d261 q := by
  simp only [d261, h 186 (by decide), agree260 p q h, agree15 p q h]
theorem nonnegative261 (p : Pattern) : 0 ≤ d261 p :=
  nonnegative_ite (p 186) (nonnegative260 p) (nonnegative15 p)
def d262 (p : Pattern) : Int := if p 271 then d5 p else d2 p
theorem agree262 (p q : Pattern) (h : Agree support p q) : d262 p = d262 q := by
  simp only [d262, h 271 (by decide), agree5 p q h, agree2 p q h]
theorem nonnegative262 (p : Pattern) : 0 ≤ d262 p :=
  nonnegative_ite (p 271) (nonnegative5 p) (nonnegative2 p)
def d263 (p : Pattern) : Int := if p 193 then d5 p else d262 p
theorem agree263 (p q : Pattern) (h : Agree support p q) : d263 p = d263 q := by
  simp only [d263, h 193 (by decide), agree5 p q h, agree262 p q h]
theorem nonnegative263 (p : Pattern) : 0 ≤ d263 p :=
  nonnegative_ite (p 193) (nonnegative5 p) (nonnegative262 p)
def d264 (p : Pattern) : Int := if p 192 then d5 p else d263 p
theorem agree264 (p q : Pattern) (h : Agree support p q) : d264 p = d264 q := by
  simp only [d264, h 192 (by decide), agree5 p q h, agree263 p q h]
theorem nonnegative264 (p : Pattern) : 0 ≤ d264 p :=
  nonnegative_ite (p 192) (nonnegative5 p) (nonnegative263 p)
def d265 (p : Pattern) : Int := if p 186 then d264 p else d18 p
theorem agree265 (p q : Pattern) (h : Agree support p q) : d265 p = d265 q := by
  simp only [d265, h 186 (by decide), agree264 p q h, agree18 p q h]
theorem nonnegative265 (p : Pattern) : 0 ≤ d265 p :=
  nonnegative_ite (p 186) (nonnegative264 p) (nonnegative18 p)
def d266 (p : Pattern) : Int := if p 168 then d265 p else d261 p
theorem agree266 (p q : Pattern) (h : Agree support p q) : d266 p = d266 q := by
  simp only [d266, h 168 (by decide), agree265 p q h, agree261 p q h]
theorem nonnegative266 (p : Pattern) : 0 ≤ d266 p :=
  nonnegative_ite (p 168) (nonnegative265 p) (nonnegative261 p)
def d267 (p : Pattern) : Int := if p 160 then d266 p else d19 p
theorem agree267 (p q : Pattern) (h : Agree support p q) : d267 p = d267 q := by
  simp only [d267, h 160 (by decide), agree266 p q h, agree19 p q h]
theorem nonnegative267 (p : Pattern) : 0 ≤ d267 p :=
  nonnegative_ite (p 160) (nonnegative266 p) (nonnegative19 p)
def d268 (p : Pattern) : Int := if p 141 then d267 p else d57 p
theorem agree268 (p q : Pattern) (h : Agree support p q) : d268 p = d268 q := by
  simp only [d268, h 141 (by decide), agree267 p q h, agree57 p q h]
theorem nonnegative268 (p : Pattern) : 0 ≤ d268 p :=
  nonnegative_ite (p 141) (nonnegative267 p) (nonnegative57 p)
def d269 (p : Pattern) : Int := if p 168 then d264 p else d260 p
theorem agree269 (p q : Pattern) (h : Agree support p q) : d269 p = d269 q := by
  simp only [d269, h 168 (by decide), agree264 p q h, agree260 p q h]
theorem nonnegative269 (p : Pattern) : 0 ≤ d269 p :=
  nonnegative_ite (p 168) (nonnegative264 p) (nonnegative260 p)
def d270 (p : Pattern) : Int := if p 160 then d269 p else d19 p
theorem agree270 (p q : Pattern) (h : Agree support p q) : d270 p = d270 q := by
  simp only [d270, h 160 (by decide), agree269 p q h, agree19 p q h]
theorem nonnegative270 (p : Pattern) : 0 ≤ d270 p :=
  nonnegative_ite (p 160) (nonnegative269 p) (nonnegative19 p)
def d271 (p : Pattern) : Int := if p 187 then d260 p else d15 p
theorem agree271 (p q : Pattern) (h : Agree support p q) : d271 p = d271 q := by
  simp only [d271, h 187 (by decide), agree260 p q h, agree15 p q h]
theorem nonnegative271 (p : Pattern) : 0 ≤ d271 p :=
  nonnegative_ite (p 187) (nonnegative260 p) (nonnegative15 p)
def d272 (p : Pattern) : Int := if p 186 then d271 p else d15 p
theorem agree272 (p q : Pattern) (h : Agree support p q) : d272 p = d272 q := by
  simp only [d272, h 186 (by decide), agree271 p q h, agree15 p q h]
theorem nonnegative272 (p : Pattern) : 0 ≤ d272 p :=
  nonnegative_ite (p 186) (nonnegative271 p) (nonnegative15 p)
def d273 (p : Pattern) : Int := if p 187 then d264 p else d18 p
theorem agree273 (p q : Pattern) (h : Agree support p q) : d273 p = d273 q := by
  simp only [d273, h 187 (by decide), agree264 p q h, agree18 p q h]
theorem nonnegative273 (p : Pattern) : 0 ≤ d273 p :=
  nonnegative_ite (p 187) (nonnegative264 p) (nonnegative18 p)
def d274 (p : Pattern) : Int := if p 186 then d273 p else d18 p
theorem agree274 (p q : Pattern) (h : Agree support p q) : d274 p = d274 q := by
  simp only [d274, h 186 (by decide), agree273 p q h, agree18 p q h]
theorem nonnegative274 (p : Pattern) : 0 ≤ d274 p :=
  nonnegative_ite (p 186) (nonnegative273 p) (nonnegative18 p)
def d275 (p : Pattern) : Int := if p 168 then d274 p else d272 p
theorem agree275 (p q : Pattern) (h : Agree support p q) : d275 p = d275 q := by
  simp only [d275, h 168 (by decide), agree274 p q h, agree272 p q h]
theorem nonnegative275 (p : Pattern) : 0 ≤ d275 p :=
  nonnegative_ite (p 168) (nonnegative274 p) (nonnegative272 p)
def d276 (p : Pattern) : Int := if p 160 then d269 p else d275 p
theorem agree276 (p q : Pattern) (h : Agree support p q) : d276 p = d276 q := by
  simp only [d276, h 160 (by decide), agree269 p q h, agree275 p q h]
theorem nonnegative276 (p : Pattern) : 0 ≤ d276 p :=
  nonnegative_ite (p 160) (nonnegative269 p) (nonnegative275 p)
def d277 (p : Pattern) : Int := if p 159 then d276 p else d270 p
theorem agree277 (p q : Pattern) (h : Agree support p q) : d277 p = d277 q := by
  simp only [d277, h 159 (by decide), agree276 p q h, agree270 p q h]
theorem nonnegative277 (p : Pattern) : 0 ≤ d277 p :=
  nonnegative_ite (p 159) (nonnegative276 p) (nonnegative270 p)
def d278 (p : Pattern) : Int := if p 158 then d277 p else d270 p
theorem agree278 (p q : Pattern) (h : Agree support p q) : d278 p = d278 q := by
  simp only [d278, h 158 (by decide), agree277 p q h, agree270 p q h]
theorem nonnegative278 (p : Pattern) : 0 ≤ d278 p :=
  nonnegative_ite (p 158) (nonnegative277 p) (nonnegative270 p)
def d279 (p : Pattern) : Int := if p 141 then d278 p else d179 p
theorem agree279 (p q : Pattern) (h : Agree support p q) : d279 p = d279 q := by
  simp only [d279, h 141 (by decide), agree278 p q h, agree179 p q h]
theorem nonnegative279 (p : Pattern) : 0 ≤ d279 p :=
  nonnegative_ite (p 141) (nonnegative278 p) (nonnegative179 p)
def d280 (p : Pattern) : Int := if p 134 then d279 p else d268 p
theorem agree280 (p q : Pattern) (h : Agree support p q) : d280 p = d280 q := by
  simp only [d280, h 134 (by decide), agree279 p q h, agree268 p q h]
theorem nonnegative280 (p : Pattern) : 0 ≤ d280 p :=
  nonnegative_ite (p 134) (nonnegative279 p) (nonnegative268 p)
def d281 (p : Pattern) : Int := if p 158 then d269 p else d267 p
theorem agree281 (p q : Pattern) (h : Agree support p q) : d281 p = d281 q := by
  simp only [d281, h 158 (by decide), agree269 p q h, agree267 p q h]
theorem nonnegative281 (p : Pattern) : 0 ≤ d281 p :=
  nonnegative_ite (p 158) (nonnegative269 p) (nonnegative267 p)
def d282 (p : Pattern) : Int := if p 141 then d281 p else d68 p
theorem agree282 (p q : Pattern) (h : Agree support p q) : d282 p = d282 q := by
  simp only [d282, h 141 (by decide), agree281 p q h, agree68 p q h]
theorem nonnegative282 (p : Pattern) : 0 ≤ d282 p :=
  nonnegative_ite (p 141) (nonnegative281 p) (nonnegative68 p)
def d283 (p : Pattern) : Int := if p 158 then d269 p else d277 p
theorem agree283 (p q : Pattern) (h : Agree support p q) : d283 p = d283 q := by
  simp only [d283, h 158 (by decide), agree269 p q h, agree277 p q h]
theorem nonnegative283 (p : Pattern) : 0 ≤ d283 p :=
  nonnegative_ite (p 158) (nonnegative269 p) (nonnegative277 p)
def d284 (p : Pattern) : Int := if p 141 then d283 p else d181 p
theorem agree284 (p q : Pattern) (h : Agree support p q) : d284 p = d284 q := by
  simp only [d284, h 141 (by decide), agree283 p q h, agree181 p q h]
theorem nonnegative284 (p : Pattern) : 0 ≤ d284 p :=
  nonnegative_ite (p 141) (nonnegative283 p) (nonnegative181 p)
def d285 (p : Pattern) : Int := if p 134 then d284 p else d282 p
theorem agree285 (p q : Pattern) (h : Agree support p q) : d285 p = d285 q := by
  simp only [d285, h 134 (by decide), agree284 p q h, agree282 p q h]
theorem nonnegative285 (p : Pattern) : 0 ≤ d285 p :=
  nonnegative_ite (p 134) (nonnegative284 p) (nonnegative282 p)
def d286 (p : Pattern) : Int := if p 133 then d285 p else d280 p
theorem agree286 (p q : Pattern) (h : Agree support p q) : d286 p = d286 q := by
  simp only [d286, h 133 (by decide), agree285 p q h, agree280 p q h]
theorem nonnegative286 (p : Pattern) : 0 ≤ d286 p :=
  nonnegative_ite (p 133) (nonnegative285 p) (nonnegative280 p)
def d287 (p : Pattern) : Int := if p 141 then d269 p else d55 p
theorem agree287 (p q : Pattern) (h : Agree support p q) : d287 p = d287 q := by
  simp only [d287, h 141 (by decide), agree269 p q h, agree55 p q h]
theorem nonnegative287 (p : Pattern) : 0 ≤ d287 p :=
  nonnegative_ite (p 141) (nonnegative269 p) (nonnegative55 p)
def d288 (p : Pattern) : Int := if p 133 then d287 p else d285 p
theorem agree288 (p q : Pattern) (h : Agree support p q) : d288 p = d288 q := by
  simp only [d288, h 133 (by decide), agree287 p q h, agree285 p q h]
theorem nonnegative288 (p : Pattern) : 0 ≤ d288 p :=
  nonnegative_ite (p 133) (nonnegative287 p) (nonnegative285 p)
def d289 (p : Pattern) : Int := if p 132 then d288 p else d286 p
theorem agree289 (p q : Pattern) (h : Agree support p q) : d289 p = d289 q := by
  simp only [d289, h 132 (by decide), agree288 p q h, agree286 p q h]
theorem nonnegative289 (p : Pattern) : 0 ≤ d289 p :=
  nonnegative_ite (p 132) (nonnegative288 p) (nonnegative286 p)
def d290 (p : Pattern) : Int := if p 186 then d260 p else d271 p
theorem agree290 (p q : Pattern) (h : Agree support p q) : d290 p = d290 q := by
  simp only [d290, h 186 (by decide), agree260 p q h, agree271 p q h]
theorem nonnegative290 (p : Pattern) : 0 ≤ d290 p :=
  nonnegative_ite (p 186) (nonnegative260 p) (nonnegative271 p)
def d291 (p : Pattern) : Int := if p 186 then d264 p else d273 p
theorem agree291 (p q : Pattern) (h : Agree support p q) : d291 p = d291 q := by
  simp only [d291, h 186 (by decide), agree264 p q h, agree273 p q h]
theorem nonnegative291 (p : Pattern) : 0 ≤ d291 p :=
  nonnegative_ite (p 186) (nonnegative264 p) (nonnegative273 p)
def d292 (p : Pattern) : Int := if p 168 then d291 p else d290 p
theorem agree292 (p q : Pattern) (h : Agree support p q) : d292 p = d292 q := by
  simp only [d292, h 168 (by decide), agree291 p q h, agree290 p q h]
theorem nonnegative292 (p : Pattern) : 0 ≤ d292 p :=
  nonnegative_ite (p 168) (nonnegative291 p) (nonnegative290 p)
def d293 (p : Pattern) : Int := if p 160 then d292 p else d275 p
theorem agree293 (p q : Pattern) (h : Agree support p q) : d293 p = d293 q := by
  simp only [d293, h 160 (by decide), agree292 p q h, agree275 p q h]
theorem nonnegative293 (p : Pattern) : 0 ≤ d293 p :=
  nonnegative_ite (p 160) (nonnegative292 p) (nonnegative275 p)
def d294 (p : Pattern) : Int := if p 159 then d293 p else d267 p
theorem agree294 (p q : Pattern) (h : Agree support p q) : d294 p = d294 q := by
  simp only [d294, h 159 (by decide), agree293 p q h, agree267 p q h]
theorem nonnegative294 (p : Pattern) : 0 ≤ d294 p :=
  nonnegative_ite (p 159) (nonnegative293 p) (nonnegative267 p)
def d295 (p : Pattern) : Int := if p 158 then d294 p else d267 p
theorem agree295 (p q : Pattern) (h : Agree support p q) : d295 p = d295 q := by
  simp only [d295, h 158 (by decide), agree294 p q h, agree267 p q h]
theorem nonnegative295 (p : Pattern) : 0 ≤ d295 p :=
  nonnegative_ite (p 158) (nonnegative294 p) (nonnegative267 p)
def d296 (p : Pattern) : Int := if p 141 then d295 p else d186 p
theorem agree296 (p q : Pattern) (h : Agree support p q) : d296 p = d296 q := by
  simp only [d296, h 141 (by decide), agree295 p q h, agree186 p q h]
theorem nonnegative296 (p : Pattern) : 0 ≤ d296 p :=
  nonnegative_ite (p 141) (nonnegative295 p) (nonnegative186 p)
def d297 (p : Pattern) : Int := if p 134 then d287 p else d296 p
theorem agree297 (p q : Pattern) (h : Agree support p q) : d297 p = d297 q := by
  simp only [d297, h 134 (by decide), agree287 p q h, agree296 p q h]
theorem nonnegative297 (p : Pattern) : 0 ≤ d297 p :=
  nonnegative_ite (p 134) (nonnegative287 p) (nonnegative296 p)
def d298 (p : Pattern) : Int := if p 160 then d292 p else d19 p
theorem agree298 (p q : Pattern) (h : Agree support p q) : d298 p = d298 q := by
  simp only [d298, h 160 (by decide), agree292 p q h, agree19 p q h]
theorem nonnegative298 (p : Pattern) : 0 ≤ d298 p :=
  nonnegative_ite (p 160) (nonnegative292 p) (nonnegative19 p)
def d299 (p : Pattern) : Int := if p 159 then d293 p else d298 p
theorem agree299 (p q : Pattern) (h : Agree support p q) : d299 p = d299 q := by
  simp only [d299, h 159 (by decide), agree293 p q h, agree298 p q h]
theorem nonnegative299 (p : Pattern) : 0 ≤ d299 p :=
  nonnegative_ite (p 159) (nonnegative293 p) (nonnegative298 p)
def d300 (p : Pattern) : Int := if p 158 then d269 p else d299 p
theorem agree300 (p q : Pattern) (h : Agree support p q) : d300 p = d300 q := by
  simp only [d300, h 158 (by decide), agree269 p q h, agree299 p q h]
theorem nonnegative300 (p : Pattern) : 0 ≤ d300 p :=
  nonnegative_ite (p 158) (nonnegative269 p) (nonnegative299 p)
def d301 (p : Pattern) : Int := if p 141 then d300 p else d188 p
theorem agree301 (p q : Pattern) (h : Agree support p q) : d301 p = d301 q := by
  simp only [d301, h 141 (by decide), agree300 p q h, agree188 p q h]
theorem nonnegative301 (p : Pattern) : 0 ≤ d301 p :=
  nonnegative_ite (p 141) (nonnegative300 p) (nonnegative188 p)
def d302 (p : Pattern) : Int := if p 134 then d287 p else d301 p
theorem agree302 (p q : Pattern) (h : Agree support p q) : d302 p = d302 q := by
  simp only [d302, h 134 (by decide), agree287 p q h, agree301 p q h]
theorem nonnegative302 (p : Pattern) : 0 ≤ d302 p :=
  nonnegative_ite (p 134) (nonnegative287 p) (nonnegative301 p)
def d303 (p : Pattern) : Int := if p 133 then d302 p else d297 p
theorem agree303 (p q : Pattern) (h : Agree support p q) : d303 p = d303 q := by
  simp only [d303, h 133 (by decide), agree302 p q h, agree297 p q h]
theorem nonnegative303 (p : Pattern) : 0 ≤ d303 p :=
  nonnegative_ite (p 133) (nonnegative302 p) (nonnegative297 p)
def d304 (p : Pattern) : Int := if p 158 then d269 p else d294 p
theorem agree304 (p q : Pattern) (h : Agree support p q) : d304 p = d304 q := by
  simp only [d304, h 158 (by decide), agree269 p q h, agree294 p q h]
theorem nonnegative304 (p : Pattern) : 0 ≤ d304 p :=
  nonnegative_ite (p 158) (nonnegative269 p) (nonnegative294 p)
def d305 (p : Pattern) : Int := if p 141 then d304 p else d191 p
theorem agree305 (p q : Pattern) (h : Agree support p q) : d305 p = d305 q := by
  simp only [d305, h 141 (by decide), agree304 p q h, agree191 p q h]
theorem nonnegative305 (p : Pattern) : 0 ≤ d305 p :=
  nonnegative_ite (p 141) (nonnegative304 p) (nonnegative191 p)
def d306 (p : Pattern) : Int := if p 134 then d287 p else d305 p
theorem agree306 (p q : Pattern) (h : Agree support p q) : d306 p = d306 q := by
  simp only [d306, h 134 (by decide), agree287 p q h, agree305 p q h]
theorem nonnegative306 (p : Pattern) : 0 ≤ d306 p :=
  nonnegative_ite (p 134) (nonnegative287 p) (nonnegative305 p)
def d307 (p : Pattern) : Int := if p 133 then d287 p else d306 p
theorem agree307 (p q : Pattern) (h : Agree support p q) : d307 p = d307 q := by
  simp only [d307, h 133 (by decide), agree287 p q h, agree306 p q h]
theorem nonnegative307 (p : Pattern) : 0 ≤ d307 p :=
  nonnegative_ite (p 133) (nonnegative287 p) (nonnegative306 p)
def d308 (p : Pattern) : Int := if p 132 then d307 p else d303 p
theorem agree308 (p q : Pattern) (h : Agree support p q) : d308 p = d308 q := by
  simp only [d308, h 132 (by decide), agree307 p q h, agree303 p q h]
theorem nonnegative308 (p : Pattern) : 0 ≤ d308 p :=
  nonnegative_ite (p 132) (nonnegative307 p) (nonnegative303 p)
def d309 (p : Pattern) : Int := if p 108 then d308 p else d289 p
theorem agree309 (p q : Pattern) (h : Agree support p q) : d309 p = d309 q := by
  simp only [d309, h 108 (by decide), agree308 p q h, agree289 p q h]
theorem nonnegative309 (p : Pattern) : 0 ≤ d309 p :=
  nonnegative_ite (p 108) (nonnegative308 p) (nonnegative289 p)
def d310 (p : Pattern) : Int := if p 133 then d165 p else d222 p
theorem agree310 (p q : Pattern) (h : Agree support p q) : d310 p = d310 q := by
  simp only [d310, h 133 (by decide), agree165 p q h, agree222 p q h]
theorem nonnegative310 (p : Pattern) : 0 ≤ d310 p :=
  nonnegative_ite (p 133) (nonnegative165 p) (nonnegative222 p)
def d311 (p : Pattern) : Int := if p 132 then d167 p else d310 p
theorem agree311 (p q : Pattern) (h : Agree support p q) : d311 p = d311 q := by
  simp only [d311, h 132 (by decide), agree167 p q h, agree310 p q h]
theorem nonnegative311 (p : Pattern) : 0 ≤ d311 p :=
  nonnegative_ite (p 132) (nonnegative167 p) (nonnegative310 p)
def d312 (p : Pattern) : Int := if p 133 then d172 p else d49 p
theorem agree312 (p q : Pattern) (h : Agree support p q) : d312 p = d312 q := by
  simp only [d312, h 133 (by decide), agree172 p q h, agree49 p q h]
theorem nonnegative312 (p : Pattern) : 0 ≤ d312 p :=
  nonnegative_ite (p 133) (nonnegative172 p) (nonnegative49 p)
def d313 (p : Pattern) : Int := if p 132 then d176 p else d312 p
theorem agree313 (p q : Pattern) (h : Agree support p q) : d313 p = d313 q := by
  simp only [d313, h 132 (by decide), agree176 p q h, agree312 p q h]
theorem nonnegative313 (p : Pattern) : 0 ≤ d313 p :=
  nonnegative_ite (p 132) (nonnegative176 p) (nonnegative312 p)
def d314 (p : Pattern) : Int := if p 108 then d313 p else d311 p
theorem agree314 (p q : Pattern) (h : Agree support p q) : d314 p = d314 q := by
  simp only [d314, h 108 (by decide), agree313 p q h, agree311 p q h]
theorem nonnegative314 (p : Pattern) : 0 ≤ d314 p :=
  nonnegative_ite (p 108) (nonnegative313 p) (nonnegative311 p)
def d315 (p : Pattern) : Int := if p 133 then d242 p else d232 p
theorem agree315 (p q : Pattern) (h : Agree support p q) : d315 p = d315 q := by
  simp only [d315, h 133 (by decide), agree242 p q h, agree232 p q h]
theorem nonnegative315 (p : Pattern) : 0 ≤ d315 p :=
  nonnegative_ite (p 133) (nonnegative242 p) (nonnegative232 p)
def d316 (p : Pattern) : Int := if p 132 then d244 p else d315 p
theorem agree316 (p q : Pattern) (h : Agree support p q) : d316 p = d316 q := by
  simp only [d316, h 132 (by decide), agree244 p q h, agree315 p q h]
theorem nonnegative316 (p : Pattern) : 0 ≤ d316 p :=
  nonnegative_ite (p 132) (nonnegative244 p) (nonnegative315 p)
def d317 (p : Pattern) : Int := if p 133 then d251 p else d71 p
theorem agree317 (p q : Pattern) (h : Agree support p q) : d317 p = d317 q := by
  simp only [d317, h 133 (by decide), agree251 p q h, agree71 p q h]
theorem nonnegative317 (p : Pattern) : 0 ≤ d317 p :=
  nonnegative_ite (p 133) (nonnegative251 p) (nonnegative71 p)
def d318 (p : Pattern) : Int := if p 132 then d256 p else d317 p
theorem agree318 (p q : Pattern) (h : Agree support p q) : d318 p = d318 q := by
  simp only [d318, h 132 (by decide), agree256 p q h, agree317 p q h]
theorem nonnegative318 (p : Pattern) : 0 ≤ d318 p :=
  nonnegative_ite (p 132) (nonnegative256 p) (nonnegative317 p)
def d319 (p : Pattern) : Int := if p 108 then d318 p else d316 p
theorem agree319 (p q : Pattern) (h : Agree support p q) : d319 p = d319 q := by
  simp only [d319, h 108 (by decide), agree318 p q h, agree316 p q h]
theorem nonnegative319 (p : Pattern) : 0 ≤ d319 p :=
  nonnegative_ite (p 108) (nonnegative318 p) (nonnegative316 p)
def d320 (p : Pattern) : Int := if p 134 then d77 p else d80 p
theorem agree320 (p q : Pattern) (h : Agree support p q) : d320 p = d320 q := by
  simp only [d320, h 134 (by decide), agree77 p q h, agree80 p q h]
theorem nonnegative320 (p : Pattern) : 0 ≤ d320 p :=
  nonnegative_ite (p 134) (nonnegative77 p) (nonnegative80 p)
def d321 (p : Pattern) : Int := if p 158 then d2 p else d80 p
theorem agree321 (p q : Pattern) (h : Agree support p q) : d321 p = d321 q := by
  simp only [d321, h 158 (by decide), agree2 p q h, agree80 p q h]
theorem nonnegative321 (p : Pattern) : 0 ≤ d321 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative80 p)
def d322 (p : Pattern) : Int := if p 134 then d203 p else d321 p
theorem agree322 (p q : Pattern) (h : Agree support p q) : d322 p = d322 q := by
  simp only [d322, h 134 (by decide), agree203 p q h, agree321 p q h]
theorem nonnegative322 (p : Pattern) : 0 ≤ d322 p :=
  nonnegative_ite (p 134) (nonnegative203 p) (nonnegative321 p)
def d323 (p : Pattern) : Int := if p 133 then d322 p else d320 p
theorem agree323 (p q : Pattern) (h : Agree support p q) : d323 p = d323 q := by
  simp only [d323, h 133 (by decide), agree322 p q h, agree320 p q h]
theorem nonnegative323 (p : Pattern) : 0 ≤ d323 p :=
  nonnegative_ite (p 133) (nonnegative322 p) (nonnegative320 p)
def d324 (p : Pattern) : Int := if p 133 then d2 p else d322 p
theorem agree324 (p q : Pattern) (h : Agree support p q) : d324 p = d324 q := by
  simp only [d324, h 133 (by decide), agree2 p q h, agree322 p q h]
theorem nonnegative324 (p : Pattern) : 0 ≤ d324 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative322 p)
def d325 (p : Pattern) : Int := if p 132 then d324 p else d323 p
theorem agree325 (p q : Pattern) (h : Agree support p q) : d325 p = d325 q := by
  simp only [d325, h 132 (by decide), agree324 p q h, agree323 p q h]
theorem nonnegative325 (p : Pattern) : 0 ≤ d325 p :=
  nonnegative_ite (p 132) (nonnegative324 p) (nonnegative323 p)
def d326 (p : Pattern) : Int := if p 134 then d2 p else d80 p
theorem agree326 (p q : Pattern) (h : Agree support p q) : d326 p = d326 q := by
  simp only [d326, h 134 (by decide), agree2 p q h, agree80 p q h]
theorem nonnegative326 (p : Pattern) : 0 ≤ d326 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative80 p)
def d327 (p : Pattern) : Int := if p 159 then d2 p else d93 p
theorem agree327 (p q : Pattern) (h : Agree support p q) : d327 p = d327 q := by
  simp only [d327, h 159 (by decide), agree2 p q h, agree93 p q h]
theorem nonnegative327 (p : Pattern) : 0 ≤ d327 p :=
  nonnegative_ite (p 159) (nonnegative2 p) (nonnegative93 p)
def d328 (p : Pattern) : Int := if p 158 then d2 p else d327 p
theorem agree328 (p q : Pattern) (h : Agree support p q) : d328 p = d328 q := by
  simp only [d328, h 158 (by decide), agree2 p q h, agree327 p q h]
theorem nonnegative328 (p : Pattern) : 0 ≤ d328 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative327 p)
def d329 (p : Pattern) : Int := if p 134 then d2 p else d328 p
theorem agree329 (p q : Pattern) (h : Agree support p q) : d329 p = d329 q := by
  simp only [d329, h 134 (by decide), agree2 p q h, agree328 p q h]
theorem nonnegative329 (p : Pattern) : 0 ≤ d329 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative328 p)
def d330 (p : Pattern) : Int := if p 133 then d329 p else d326 p
theorem agree330 (p q : Pattern) (h : Agree support p q) : d330 p = d330 q := by
  simp only [d330, h 133 (by decide), agree329 p q h, agree326 p q h]
theorem nonnegative330 (p : Pattern) : 0 ≤ d330 p :=
  nonnegative_ite (p 133) (nonnegative329 p) (nonnegative326 p)
def d331 (p : Pattern) : Int := if p 134 then d2 p else d321 p
theorem agree331 (p q : Pattern) (h : Agree support p q) : d331 p = d331 q := by
  simp only [d331, h 134 (by decide), agree2 p q h, agree321 p q h]
theorem nonnegative331 (p : Pattern) : 0 ≤ d331 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative321 p)
def d332 (p : Pattern) : Int := if p 133 then d2 p else d331 p
theorem agree332 (p q : Pattern) (h : Agree support p q) : d332 p = d332 q := by
  simp only [d332, h 133 (by decide), agree2 p q h, agree331 p q h]
theorem nonnegative332 (p : Pattern) : 0 ≤ d332 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative331 p)
def d333 (p : Pattern) : Int := if p 132 then d332 p else d330 p
theorem agree333 (p q : Pattern) (h : Agree support p q) : d333 p = d333 q := by
  simp only [d333, h 132 (by decide), agree332 p q h, agree330 p q h]
theorem nonnegative333 (p : Pattern) : 0 ≤ d333 p :=
  nonnegative_ite (p 132) (nonnegative332 p) (nonnegative330 p)
def d334 (p : Pattern) : Int := if p 108 then d333 p else d325 p
theorem agree334 (p q : Pattern) (h : Agree support p q) : d334 p = d334 q := by
  simp only [d334, h 108 (by decide), agree333 p q h, agree325 p q h]
theorem nonnegative334 (p : Pattern) : 0 ≤ d334 p :=
  nonnegative_ite (p 108) (nonnegative333 p) (nonnegative325 p)
def d335 (p : Pattern) : Int := if p 141 then d116 p else d114 p
theorem agree335 (p q : Pattern) (h : Agree support p q) : d335 p = d335 q := by
  simp only [d335, h 141 (by decide), agree116 p q h, agree114 p q h]
theorem nonnegative335 (p : Pattern) : 0 ≤ d335 p :=
  nonnegative_ite (p 141) (nonnegative116 p) (nonnegative114 p)
def d336 (p : Pattern) : Int := if p 141 then d110 p else d107 p
theorem agree336 (p q : Pattern) (h : Agree support p q) : d336 p = d336 q := by
  simp only [d336, h 141 (by decide), agree110 p q h, agree107 p q h]
theorem nonnegative336 (p : Pattern) : 0 ≤ d336 p :=
  nonnegative_ite (p 141) (nonnegative110 p) (nonnegative107 p)
def d337 (p : Pattern) : Int := if p 134 then d336 p else d335 p
theorem agree337 (p q : Pattern) (h : Agree support p q) : d337 p = d337 q := by
  simp only [d337, h 134 (by decide), agree336 p q h, agree335 p q h]
theorem nonnegative337 (p : Pattern) : 0 ≤ d337 p :=
  nonnegative_ite (p 134) (nonnegative336 p) (nonnegative335 p)
def d338 (p : Pattern) : Int := if p 158 then d55 p else d114 p
theorem agree338 (p q : Pattern) (h : Agree support p q) : d338 p = d338 q := by
  simp only [d338, h 158 (by decide), agree55 p q h, agree114 p q h]
theorem nonnegative338 (p : Pattern) : 0 ≤ d338 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative114 p)
def d339 (p : Pattern) : Int := if p 158 then d65 p else d116 p
theorem agree339 (p q : Pattern) (h : Agree support p q) : d339 p = d339 q := by
  simp only [d339, h 158 (by decide), agree65 p q h, agree116 p q h]
theorem nonnegative339 (p : Pattern) : 0 ≤ d339 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative116 p)
def d340 (p : Pattern) : Int := if p 141 then d339 p else d338 p
theorem agree340 (p q : Pattern) (h : Agree support p q) : d340 p = d340 q := by
  simp only [d340, h 141 (by decide), agree339 p q h, agree338 p q h]
theorem nonnegative340 (p : Pattern) : 0 ≤ d340 p :=
  nonnegative_ite (p 141) (nonnegative339 p) (nonnegative338 p)
def d341 (p : Pattern) : Int := if p 134 then d213 p else d340 p
theorem agree341 (p q : Pattern) (h : Agree support p q) : d341 p = d341 q := by
  simp only [d341, h 134 (by decide), agree213 p q h, agree340 p q h]
theorem nonnegative341 (p : Pattern) : 0 ≤ d341 p :=
  nonnegative_ite (p 134) (nonnegative213 p) (nonnegative340 p)
def d342 (p : Pattern) : Int := if p 133 then d341 p else d337 p
theorem agree342 (p q : Pattern) (h : Agree support p q) : d342 p = d342 q := by
  simp only [d342, h 133 (by decide), agree341 p q h, agree337 p q h]
theorem nonnegative342 (p : Pattern) : 0 ≤ d342 p :=
  nonnegative_ite (p 133) (nonnegative341 p) (nonnegative337 p)
def d343 (p : Pattern) : Int := if p 133 then d66 p else d341 p
theorem agree343 (p q : Pattern) (h : Agree support p q) : d343 p = d343 q := by
  simp only [d343, h 133 (by decide), agree66 p q h, agree341 p q h]
theorem nonnegative343 (p : Pattern) : 0 ≤ d343 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative341 p)
def d344 (p : Pattern) : Int := if p 132 then d343 p else d342 p
theorem agree344 (p q : Pattern) (h : Agree support p q) : d344 p = d344 q := by
  simp only [d344, h 132 (by decide), agree343 p q h, agree342 p q h]
theorem nonnegative344 (p : Pattern) : 0 ≤ d344 p :=
  nonnegative_ite (p 132) (nonnegative343 p) (nonnegative342 p)
def d345 (p : Pattern) : Int := if p 134 then d66 p else d335 p
theorem agree345 (p q : Pattern) (h : Agree support p q) : d345 p = d345 q := by
  simp only [d345, h 134 (by decide), agree66 p q h, agree335 p q h]
theorem nonnegative345 (p : Pattern) : 0 ≤ d345 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative335 p)
def d346 (p : Pattern) : Int := if p 159 then d55 p else d138 p
theorem agree346 (p q : Pattern) (h : Agree support p q) : d346 p = d346 q := by
  simp only [d346, h 159 (by decide), agree55 p q h, agree138 p q h]
theorem nonnegative346 (p : Pattern) : 0 ≤ d346 p :=
  nonnegative_ite (p 159) (nonnegative55 p) (nonnegative138 p)
def d347 (p : Pattern) : Int := if p 158 then d55 p else d346 p
theorem agree347 (p q : Pattern) (h : Agree support p q) : d347 p = d347 q := by
  simp only [d347, h 158 (by decide), agree55 p q h, agree346 p q h]
theorem nonnegative347 (p : Pattern) : 0 ≤ d347 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative346 p)
def d348 (p : Pattern) : Int := if p 159 then d65 p else d145 p
theorem agree348 (p q : Pattern) (h : Agree support p q) : d348 p = d348 q := by
  simp only [d348, h 159 (by decide), agree65 p q h, agree145 p q h]
theorem nonnegative348 (p : Pattern) : 0 ≤ d348 p :=
  nonnegative_ite (p 159) (nonnegative65 p) (nonnegative145 p)
def d349 (p : Pattern) : Int := if p 158 then d65 p else d348 p
theorem agree349 (p q : Pattern) (h : Agree support p q) : d349 p = d349 q := by
  simp only [d349, h 158 (by decide), agree65 p q h, agree348 p q h]
theorem nonnegative349 (p : Pattern) : 0 ≤ d349 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative348 p)
def d350 (p : Pattern) : Int := if p 141 then d349 p else d347 p
theorem agree350 (p q : Pattern) (h : Agree support p q) : d350 p = d350 q := by
  simp only [d350, h 141 (by decide), agree349 p q h, agree347 p q h]
theorem nonnegative350 (p : Pattern) : 0 ≤ d350 p :=
  nonnegative_ite (p 141) (nonnegative349 p) (nonnegative347 p)
def d351 (p : Pattern) : Int := if p 134 then d66 p else d350 p
theorem agree351 (p q : Pattern) (h : Agree support p q) : d351 p = d351 q := by
  simp only [d351, h 134 (by decide), agree66 p q h, agree350 p q h]
theorem nonnegative351 (p : Pattern) : 0 ≤ d351 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative350 p)
def d352 (p : Pattern) : Int := if p 133 then d351 p else d345 p
theorem agree352 (p q : Pattern) (h : Agree support p q) : d352 p = d352 q := by
  simp only [d352, h 133 (by decide), agree351 p q h, agree345 p q h]
theorem nonnegative352 (p : Pattern) : 0 ≤ d352 p :=
  nonnegative_ite (p 133) (nonnegative351 p) (nonnegative345 p)
def d353 (p : Pattern) : Int := if p 134 then d66 p else d340 p
theorem agree353 (p q : Pattern) (h : Agree support p q) : d353 p = d353 q := by
  simp only [d353, h 134 (by decide), agree66 p q h, agree340 p q h]
theorem nonnegative353 (p : Pattern) : 0 ≤ d353 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative340 p)
def d354 (p : Pattern) : Int := if p 133 then d66 p else d353 p
theorem agree354 (p q : Pattern) (h : Agree support p q) : d354 p = d354 q := by
  simp only [d354, h 133 (by decide), agree66 p q h, agree353 p q h]
theorem nonnegative354 (p : Pattern) : 0 ≤ d354 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative353 p)
def d355 (p : Pattern) : Int := if p 132 then d354 p else d352 p
theorem agree355 (p q : Pattern) (h : Agree support p q) : d355 p = d355 q := by
  simp only [d355, h 132 (by decide), agree354 p q h, agree352 p q h]
theorem nonnegative355 (p : Pattern) : 0 ≤ d355 p :=
  nonnegative_ite (p 132) (nonnegative354 p) (nonnegative352 p)
def d356 (p : Pattern) : Int := if p 108 then d355 p else d344 p
theorem agree356 (p q : Pattern) (h : Agree support p q) : d356 p = d356 q := by
  simp only [d356, h 108 (by decide), agree355 p q h, agree344 p q h]
theorem nonnegative356 (p : Pattern) : 0 ≤ d356 p :=
  nonnegative_ite (p 108) (nonnegative355 p) (nonnegative344 p)
def d357 (p : Pattern) : Int := if p 133 then d221 p else d76 p
theorem agree357 (p q : Pattern) (h : Agree support p q) : d357 p = d357 q := by
  simp only [d357, h 133 (by decide), agree221 p q h, agree76 p q h]
theorem nonnegative357 (p : Pattern) : 0 ≤ d357 p :=
  nonnegative_ite (p 133) (nonnegative221 p) (nonnegative76 p)
def d358 (p : Pattern) : Int := if p 133 then d2 p else d221 p
theorem agree358 (p q : Pattern) (h : Agree support p q) : d358 p = d358 q := by
  simp only [d358, h 133 (by decide), agree2 p q h, agree221 p q h]
theorem nonnegative358 (p : Pattern) : 0 ≤ d358 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative221 p)
def d359 (p : Pattern) : Int := if p 132 then d358 p else d357 p
theorem agree359 (p q : Pattern) (h : Agree support p q) : d359 p = d359 q := by
  simp only [d359, h 132 (by decide), agree358 p q h, agree357 p q h]
theorem nonnegative359 (p : Pattern) : 0 ≤ d359 p :=
  nonnegative_ite (p 132) (nonnegative358 p) (nonnegative357 p)
end NetHack.Sokoban12CostPartition
