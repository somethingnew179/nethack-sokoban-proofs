/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d240 (p : Pattern) : Int := if p 112 then d239 p else d238 p
theorem agree240 (p q : Pattern) (h : Agree support p q) : d240 p = d240 q := by
  simp only [d240, h 112 (by decide), agree239 p q h, agree238 p q h]
theorem nonnegative240 (p : Pattern) : 0 ≤ d240 p :=
  nonnegative_ite (p 112) (nonnegative239 p) (nonnegative238 p)
def d241 (p : Pattern) : Int := if p 106 then d240 p else d237 p
theorem agree241 (p q : Pattern) (h : Agree support p q) : d241 p = d241 q := by
  simp only [d241, h 106 (by decide), agree240 p q h, agree237 p q h]
theorem nonnegative241 (p : Pattern) : 0 ≤ d241 p :=
  nonnegative_ite (p 106) (nonnegative240 p) (nonnegative237 p)
def d242 (p : Pattern) : Int := if p 86 then d241 p else d234 p
theorem agree242 (p q : Pattern) (h : Agree support p q) : d242 p = d242 q := by
  simp only [d242, h 86 (by decide), agree241 p q h, agree234 p q h]
theorem nonnegative242 (p : Pattern) : 0 ≤ d242 p :=
  nonnegative_ite (p 86) (nonnegative241 p) (nonnegative234 p)
def d243 (p : Pattern) : Int := if p 113 then d154 p else d51 p
theorem agree243 (p q : Pattern) (h : Agree support p q) : d243 p = d243 q := by
  simp only [d243, h 113 (by decide), agree154 p q h, agree51 p q h]
theorem nonnegative243 (p : Pattern) : 0 ≤ d243 p :=
  nonnegative_ite (p 113) (nonnegative154 p) (nonnegative51 p)
def d244 (p : Pattern) : Int := if p 112 then d243 p else d235 p
theorem agree244 (p q : Pattern) (h : Agree support p q) : d244 p = d244 q := by
  simp only [d244, h 112 (by decide), agree243 p q h, agree235 p q h]
theorem nonnegative244 (p : Pattern) : 0 ≤ d244 p :=
  nonnegative_ite (p 112) (nonnegative243 p) (nonnegative235 p)
def d245 (p : Pattern) : Int := if p 113 then d163 p else d80 p
theorem agree245 (p q : Pattern) (h : Agree support p q) : d245 p = d245 q := by
  simp only [d245, h 113 (by decide), agree163 p q h, agree80 p q h]
theorem nonnegative245 (p : Pattern) : 0 ≤ d245 p :=
  nonnegative_ite (p 113) (nonnegative163 p) (nonnegative80 p)
def d246 (p : Pattern) : Int := if p 112 then d245 p else d238 p
theorem agree246 (p q : Pattern) (h : Agree support p q) : d246 p = d246 q := by
  simp only [d246, h 112 (by decide), agree245 p q h, agree238 p q h]
theorem nonnegative246 (p : Pattern) : 0 ≤ d246 p :=
  nonnegative_ite (p 112) (nonnegative245 p) (nonnegative238 p)
def d247 (p : Pattern) : Int := if p 106 then d246 p else d244 p
theorem agree247 (p q : Pattern) (h : Agree support p q) : d247 p = d247 q := by
  simp only [d247, h 106 (by decide), agree246 p q h, agree244 p q h]
theorem nonnegative247 (p : Pattern) : 0 ≤ d247 p :=
  nonnegative_ite (p 106) (nonnegative246 p) (nonnegative244 p)
def d248 (p : Pattern) : Int := if p 113 then d161 p else d45 p
theorem agree248 (p q : Pattern) (h : Agree support p q) : d248 p = d248 q := by
  simp only [d248, h 113 (by decide), agree161 p q h, agree45 p q h]
theorem nonnegative248 (p : Pattern) : 0 ≤ d248 p :=
  nonnegative_ite (p 113) (nonnegative161 p) (nonnegative45 p)
def d249 (p : Pattern) : Int := if p 113 then d163 p else d102 p
theorem agree249 (p q : Pattern) (h : Agree support p q) : d249 p = d249 q := by
  simp only [d249, h 113 (by decide), agree163 p q h, agree102 p q h]
theorem nonnegative249 (p : Pattern) : 0 ≤ d249 p :=
  nonnegative_ite (p 113) (nonnegative163 p) (nonnegative102 p)
def d250 (p : Pattern) : Int := if p 112 then d249 p else d248 p
theorem agree250 (p q : Pattern) (h : Agree support p q) : d250 p = d250 q := by
  simp only [d250, h 112 (by decide), agree249 p q h, agree248 p q h]
theorem nonnegative250 (p : Pattern) : 0 ≤ d250 p :=
  nonnegative_ite (p 112) (nonnegative249 p) (nonnegative248 p)
def d251 (p : Pattern) : Int := if p 113 then d167 p else d77 p
theorem agree251 (p q : Pattern) (h : Agree support p q) : d251 p = d251 q := by
  simp only [d251, h 113 (by decide), agree167 p q h, agree77 p q h]
theorem nonnegative251 (p : Pattern) : 0 ≤ d251 p :=
  nonnegative_ite (p 113) (nonnegative167 p) (nonnegative77 p)
def d252 (p : Pattern) : Int := if p 112 then d130 p else d251 p
theorem agree252 (p q : Pattern) (h : Agree support p q) : d252 p = d252 q := by
  simp only [d252, h 112 (by decide), agree130 p q h, agree251 p q h]
theorem nonnegative252 (p : Pattern) : 0 ≤ d252 p :=
  nonnegative_ite (p 112) (nonnegative130 p) (nonnegative251 p)
def d253 (p : Pattern) : Int := if p 106 then d252 p else d250 p
theorem agree253 (p q : Pattern) (h : Agree support p q) : d253 p = d253 q := by
  simp only [d253, h 106 (by decide), agree252 p q h, agree250 p q h]
theorem nonnegative253 (p : Pattern) : 0 ≤ d253 p :=
  nonnegative_ite (p 106) (nonnegative252 p) (nonnegative250 p)
def d254 (p : Pattern) : Int := if p 86 then d253 p else d247 p
theorem agree254 (p q : Pattern) (h : Agree support p q) : d254 p = d254 q := by
  simp only [d254, h 86 (by decide), agree253 p q h, agree247 p q h]
theorem nonnegative254 (p : Pattern) : 0 ≤ d254 p :=
  nonnegative_ite (p 86) (nonnegative253 p) (nonnegative247 p)
def d255 (p : Pattern) : Int := if p 80 then d254 p else d242 p
theorem agree255 (p q : Pattern) (h : Agree support p q) : d255 p = d255 q := by
  simp only [d255, h 80 (by decide), agree254 p q h, agree242 p q h]
theorem nonnegative255 (p : Pattern) : 0 ≤ d255 p :=
  nonnegative_ite (p 80) (nonnegative254 p) (nonnegative242 p)
def d256 (p : Pattern) : Int := if p 132 then d141 p else d28 p
theorem agree256 (p q : Pattern) (h : Agree support p q) : d256 p = d256 q := by
  simp only [d256, h 132 (by decide), agree141 p q h, agree28 p q h]
theorem nonnegative256 (p : Pattern) : 0 ≤ d256 p :=
  nonnegative_ite (p 132) (nonnegative141 p) (nonnegative28 p)
def d257 (p : Pattern) : Int := if p 132 then d152 p else d47 p
theorem agree257 (p q : Pattern) (h : Agree support p q) : d257 p = d257 q := by
  simp only [d257, h 132 (by decide), agree152 p q h, agree47 p q h]
theorem nonnegative257 (p : Pattern) : 0 ≤ d257 p :=
  nonnegative_ite (p 132) (nonnegative152 p) (nonnegative47 p)
def d258 (p : Pattern) : Int := if p 132 then d152 p else d57 p
theorem agree258 (p q : Pattern) (h : Agree support p q) : d258 p = d258 q := by
  simp only [d258, h 132 (by decide), agree152 p q h, agree57 p q h]
theorem nonnegative258 (p : Pattern) : 0 ≤ d258 p :=
  nonnegative_ite (p 132) (nonnegative152 p) (nonnegative57 p)
def d259 (p : Pattern) : Int := if p 113 then d258 p else d257 p
theorem agree259 (p q : Pattern) (h : Agree support p q) : d259 p = d259 q := by
  simp only [d259, h 113 (by decide), agree258 p q h, agree257 p q h]
theorem nonnegative259 (p : Pattern) : 0 ≤ d259 p :=
  nonnegative_ite (p 113) (nonnegative258 p) (nonnegative257 p)
def d260 (p : Pattern) : Int := if p 112 then d259 p else d256 p
theorem agree260 (p q : Pattern) (h : Agree support p q) : d260 p = d260 q := by
  simp only [d260, h 112 (by decide), agree259 p q h, agree256 p q h]
theorem nonnegative260 (p : Pattern) : 0 ≤ d260 p :=
  nonnegative_ite (p 112) (nonnegative259 p) (nonnegative256 p)
def d261 (p : Pattern) : Int := if p 132 then d149 p else d28 p
theorem agree261 (p q : Pattern) (h : Agree support p q) : d261 p = d261 q := by
  simp only [d261, h 132 (by decide), agree149 p q h, agree28 p q h]
theorem nonnegative261 (p : Pattern) : 0 ≤ d261 p :=
  nonnegative_ite (p 132) (nonnegative149 p) (nonnegative28 p)
def d262 (p : Pattern) : Int := if p 113 then d261 p else d256 p
theorem agree262 (p q : Pattern) (h : Agree support p q) : d262 p = d262 q := by
  simp only [d262, h 113 (by decide), agree261 p q h, agree256 p q h]
theorem nonnegative262 (p : Pattern) : 0 ≤ d262 p :=
  nonnegative_ite (p 113) (nonnegative261 p) (nonnegative256 p)
def d263 (p : Pattern) : Int := if p 132 then d153 p else d57 p
theorem agree263 (p q : Pattern) (h : Agree support p q) : d263 p = d263 q := by
  simp only [d263, h 132 (by decide), agree153 p q h, agree57 p q h]
theorem nonnegative263 (p : Pattern) : 0 ≤ d263 p :=
  nonnegative_ite (p 132) (nonnegative153 p) (nonnegative57 p)
def d264 (p : Pattern) : Int := if p 113 then d263 p else d257 p
theorem agree264 (p q : Pattern) (h : Agree support p q) : d264 p = d264 q := by
  simp only [d264, h 113 (by decide), agree263 p q h, agree257 p q h]
theorem nonnegative264 (p : Pattern) : 0 ≤ d264 p :=
  nonnegative_ite (p 113) (nonnegative263 p) (nonnegative257 p)
def d265 (p : Pattern) : Int := if p 112 then d264 p else d262 p
theorem agree265 (p q : Pattern) (h : Agree support p q) : d265 p = d265 q := by
  simp only [d265, h 112 (by decide), agree264 p q h, agree262 p q h]
theorem nonnegative265 (p : Pattern) : 0 ≤ d265 p :=
  nonnegative_ite (p 112) (nonnegative264 p) (nonnegative262 p)
def d266 (p : Pattern) : Int := if p 106 then d265 p else d260 p
theorem agree266 (p q : Pattern) (h : Agree support p q) : d266 p = d266 q := by
  simp only [d266, h 106 (by decide), agree265 p q h, agree260 p q h]
theorem nonnegative266 (p : Pattern) : 0 ≤ d266 p :=
  nonnegative_ite (p 106) (nonnegative265 p) (nonnegative260 p)
def d267 (p : Pattern) : Int := if p 132 then d149 p else d89 p
theorem agree267 (p q : Pattern) (h : Agree support p q) : d267 p = d267 q := by
  simp only [d267, h 132 (by decide), agree149 p q h, agree89 p q h]
theorem nonnegative267 (p : Pattern) : 0 ≤ d267 p :=
  nonnegative_ite (p 132) (nonnegative149 p) (nonnegative89 p)
def d268 (p : Pattern) : Int := if p 113 then d267 p else d256 p
theorem agree268 (p q : Pattern) (h : Agree support p q) : d268 p = d268 q := by
  simp only [d268, h 113 (by decide), agree267 p q h, agree256 p q h]
theorem nonnegative268 (p : Pattern) : 0 ≤ d268 p :=
  nonnegative_ite (p 113) (nonnegative267 p) (nonnegative256 p)
def d269 (p : Pattern) : Int := if p 132 then d152 p else d100 p
theorem agree269 (p q : Pattern) (h : Agree support p q) : d269 p = d269 q := by
  simp only [d269, h 132 (by decide), agree152 p q h, agree100 p q h]
theorem nonnegative269 (p : Pattern) : 0 ≤ d269 p :=
  nonnegative_ite (p 132) (nonnegative152 p) (nonnegative100 p)
def d270 (p : Pattern) : Int := if p 132 then d153 p else d100 p
theorem agree270 (p q : Pattern) (h : Agree support p q) : d270 p = d270 q := by
  simp only [d270, h 132 (by decide), agree153 p q h, agree100 p q h]
theorem nonnegative270 (p : Pattern) : 0 ≤ d270 p :=
  nonnegative_ite (p 132) (nonnegative153 p) (nonnegative100 p)
def d271 (p : Pattern) : Int := if p 113 then d270 p else d269 p
theorem agree271 (p q : Pattern) (h : Agree support p q) : d271 p = d271 q := by
  simp only [d271, h 113 (by decide), agree270 p q h, agree269 p q h]
theorem nonnegative271 (p : Pattern) : 0 ≤ d271 p :=
  nonnegative_ite (p 113) (nonnegative270 p) (nonnegative269 p)
def d272 (p : Pattern) : Int := if p 112 then d271 p else d268 p
theorem agree272 (p q : Pattern) (h : Agree support p q) : d272 p = d272 q := by
  simp only [d272, h 112 (by decide), agree271 p q h, agree268 p q h]
theorem nonnegative272 (p : Pattern) : 0 ≤ d272 p :=
  nonnegative_ite (p 112) (nonnegative271 p) (nonnegative268 p)
def d273 (p : Pattern) : Int := if p 132 then d160 p else d89 p
theorem agree273 (p q : Pattern) (h : Agree support p q) : d273 p = d273 q := by
  simp only [d273, h 132 (by decide), agree160 p q h, agree89 p q h]
theorem nonnegative273 (p : Pattern) : 0 ≤ d273 p :=
  nonnegative_ite (p 132) (nonnegative160 p) (nonnegative89 p)
def d274 (p : Pattern) : Int := if p 113 then d273 p else d261 p
theorem agree274 (p q : Pattern) (h : Agree support p q) : d274 p = d274 q := by
  simp only [d274, h 113 (by decide), agree273 p q h, agree261 p q h]
theorem nonnegative274 (p : Pattern) : 0 ≤ d274 p :=
  nonnegative_ite (p 113) (nonnegative273 p) (nonnegative261 p)
def d275 (p : Pattern) : Int := if p 132 then d2 p else d110 p
theorem agree275 (p q : Pattern) (h : Agree support p q) : d275 p = d275 q := by
  simp only [d275, h 132 (by decide), agree2 p q h, agree110 p q h]
theorem nonnegative275 (p : Pattern) : 0 ≤ d275 p :=
  nonnegative_ite (p 132) (nonnegative2 p) (nonnegative110 p)
def d276 (p : Pattern) : Int := if p 113 then d275 p else d270 p
theorem agree276 (p q : Pattern) (h : Agree support p q) : d276 p = d276 q := by
  simp only [d276, h 113 (by decide), agree275 p q h, agree270 p q h]
theorem nonnegative276 (p : Pattern) : 0 ≤ d276 p :=
  nonnegative_ite (p 113) (nonnegative275 p) (nonnegative270 p)
def d277 (p : Pattern) : Int := if p 112 then d276 p else d274 p
theorem agree277 (p q : Pattern) (h : Agree support p q) : d277 p = d277 q := by
  simp only [d277, h 112 (by decide), agree276 p q h, agree274 p q h]
theorem nonnegative277 (p : Pattern) : 0 ≤ d277 p :=
  nonnegative_ite (p 112) (nonnegative276 p) (nonnegative274 p)
def d278 (p : Pattern) : Int := if p 106 then d277 p else d272 p
theorem agree278 (p q : Pattern) (h : Agree support p q) : d278 p = d278 q := by
  simp only [d278, h 106 (by decide), agree277 p q h, agree272 p q h]
theorem nonnegative278 (p : Pattern) : 0 ≤ d278 p :=
  nonnegative_ite (p 106) (nonnegative277 p) (nonnegative272 p)
def d279 (p : Pattern) : Int := if p 86 then d278 p else d266 p
theorem agree279 (p q : Pattern) (h : Agree support p q) : d279 p = d279 q := by
  simp only [d279, h 86 (by decide), agree278 p q h, agree266 p q h]
theorem nonnegative279 (p : Pattern) : 0 ≤ d279 p :=
  nonnegative_ite (p 86) (nonnegative278 p) (nonnegative266 p)
def d280 (p : Pattern) : Int := if p 132 then d160 p else d28 p
theorem agree280 (p q : Pattern) (h : Agree support p q) : d280 p = d280 q := by
  simp only [d280, h 132 (by decide), agree160 p q h, agree28 p q h]
theorem nonnegative280 (p : Pattern) : 0 ≤ d280 p :=
  nonnegative_ite (p 132) (nonnegative160 p) (nonnegative28 p)
def d281 (p : Pattern) : Int := if p 113 then d280 p else d261 p
theorem agree281 (p q : Pattern) (h : Agree support p q) : d281 p = d281 q := by
  simp only [d281, h 113 (by decide), agree280 p q h, agree261 p q h]
theorem nonnegative281 (p : Pattern) : 0 ≤ d281 p :=
  nonnegative_ite (p 113) (nonnegative280 p) (nonnegative261 p)
def d282 (p : Pattern) : Int := if p 132 then d153 p else d47 p
theorem agree282 (p q : Pattern) (h : Agree support p q) : d282 p = d282 q := by
  simp only [d282, h 132 (by decide), agree153 p q h, agree47 p q h]
theorem nonnegative282 (p : Pattern) : 0 ≤ d282 p :=
  nonnegative_ite (p 132) (nonnegative153 p) (nonnegative47 p)
def d283 (p : Pattern) : Int := if p 132 then d2 p else d57 p
theorem agree283 (p q : Pattern) (h : Agree support p q) : d283 p = d283 q := by
  simp only [d283, h 132 (by decide), agree2 p q h, agree57 p q h]
theorem nonnegative283 (p : Pattern) : 0 ≤ d283 p :=
  nonnegative_ite (p 132) (nonnegative2 p) (nonnegative57 p)
def d284 (p : Pattern) : Int := if p 113 then d283 p else d282 p
theorem agree284 (p q : Pattern) (h : Agree support p q) : d284 p = d284 q := by
  simp only [d284, h 113 (by decide), agree283 p q h, agree282 p q h]
theorem nonnegative284 (p : Pattern) : 0 ≤ d284 p :=
  nonnegative_ite (p 113) (nonnegative283 p) (nonnegative282 p)
def d285 (p : Pattern) : Int := if p 112 then d284 p else d281 p
theorem agree285 (p q : Pattern) (h : Agree support p q) : d285 p = d285 q := by
  simp only [d285, h 112 (by decide), agree284 p q h, agree281 p q h]
theorem nonnegative285 (p : Pattern) : 0 ≤ d285 p :=
  nonnegative_ite (p 112) (nonnegative284 p) (nonnegative281 p)
def d286 (p : Pattern) : Int := if p 106 then d285 p else d265 p
theorem agree286 (p q : Pattern) (h : Agree support p q) : d286 p = d286 q := by
  simp only [d286, h 106 (by decide), agree285 p q h, agree265 p q h]
theorem nonnegative286 (p : Pattern) : 0 ≤ d286 p :=
  nonnegative_ite (p 106) (nonnegative285 p) (nonnegative265 p)
def d287 (p : Pattern) : Int := if p 113 then d283 p else d280 p
theorem agree287 (p q : Pattern) (h : Agree support p q) : d287 p = d287 q := by
  simp only [d287, h 113 (by decide), agree283 p q h, agree280 p q h]
theorem nonnegative287 (p : Pattern) : 0 ≤ d287 p :=
  nonnegative_ite (p 113) (nonnegative283 p) (nonnegative280 p)
def d288 (p : Pattern) : Int := if p 113 then d2 p else d275 p
theorem agree288 (p q : Pattern) (h : Agree support p q) : d288 p = d288 q := by
  simp only [d288, h 113 (by decide), agree2 p q h, agree275 p q h]
theorem nonnegative288 (p : Pattern) : 0 ≤ d288 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative275 p)
def d289 (p : Pattern) : Int := if p 112 then d288 p else d287 p
theorem agree289 (p q : Pattern) (h : Agree support p q) : d289 p = d289 q := by
  simp only [d289, h 112 (by decide), agree288 p q h, agree287 p q h]
theorem nonnegative289 (p : Pattern) : 0 ≤ d289 p :=
  nonnegative_ite (p 112) (nonnegative288 p) (nonnegative287 p)
def d290 (p : Pattern) : Int := if p 106 then d289 p else d277 p
theorem agree290 (p q : Pattern) (h : Agree support p q) : d290 p = d290 q := by
  simp only [d290, h 106 (by decide), agree289 p q h, agree277 p q h]
theorem nonnegative290 (p : Pattern) : 0 ≤ d290 p :=
  nonnegative_ite (p 106) (nonnegative289 p) (nonnegative277 p)
def d291 (p : Pattern) : Int := if p 86 then d290 p else d286 p
theorem agree291 (p q : Pattern) (h : Agree support p q) : d291 p = d291 q := by
  simp only [d291, h 86 (by decide), agree290 p q h, agree286 p q h]
theorem nonnegative291 (p : Pattern) : 0 ≤ d291 p :=
  nonnegative_ite (p 86) (nonnegative290 p) (nonnegative286 p)
def d292 (p : Pattern) : Int := if p 80 then d291 p else d279 p
theorem agree292 (p q : Pattern) (h : Agree support p q) : d292 p = d292 q := by
  simp only [d292, h 80 (by decide), agree291 p q h, agree279 p q h]
theorem nonnegative292 (p : Pattern) : 0 ≤ d292 p :=
  nonnegative_ite (p 80) (nonnegative291 p) (nonnegative279 p)
def d293 (p : Pattern) : Int := if p 133 then d140 p else d16 p
theorem agree293 (p q : Pattern) (h : Agree support p q) : d293 p = d293 q := by
  simp only [d293, h 133 (by decide), agree140 p q h, agree16 p q h]
theorem nonnegative293 (p : Pattern) : 0 ≤ d293 p :=
  nonnegative_ite (p 133) (nonnegative140 p) (nonnegative16 p)
def d294 (p : Pattern) : Int := if p 133 then d2 p else d15 p
theorem agree294 (p q : Pattern) (h : Agree support p q) : d294 p = d294 q := by
  simp only [d294, h 133 (by decide), agree2 p q h, agree15 p q h]
theorem nonnegative294 (p : Pattern) : 0 ≤ d294 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative15 p)
def d295 (p : Pattern) : Int := if p 133 then d2 p else d53 p
theorem agree295 (p q : Pattern) (h : Agree support p q) : d295 p = d295 q := by
  simp only [d295, h 133 (by decide), agree2 p q h, agree53 p q h]
theorem nonnegative295 (p : Pattern) : 0 ≤ d295 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative53 p)
def d296 (p : Pattern) : Int := if p 113 then d295 p else d294 p
theorem agree296 (p q : Pattern) (h : Agree support p q) : d296 p = d296 q := by
  simp only [d296, h 113 (by decide), agree295 p q h, agree294 p q h]
theorem nonnegative296 (p : Pattern) : 0 ≤ d296 p :=
  nonnegative_ite (p 113) (nonnegative295 p) (nonnegative294 p)
def d297 (p : Pattern) : Int := if p 112 then d296 p else d293 p
theorem agree297 (p q : Pattern) (h : Agree support p q) : d297 p = d297 q := by
  simp only [d297, h 112 (by decide), agree296 p q h, agree293 p q h]
theorem nonnegative297 (p : Pattern) : 0 ≤ d297 p :=
  nonnegative_ite (p 112) (nonnegative296 p) (nonnegative293 p)
def d298 (p : Pattern) : Int := if p 133 then d148 p else d16 p
theorem agree298 (p q : Pattern) (h : Agree support p q) : d298 p = d298 q := by
  simp only [d298, h 133 (by decide), agree148 p q h, agree16 p q h]
theorem nonnegative298 (p : Pattern) : 0 ≤ d298 p :=
  nonnegative_ite (p 133) (nonnegative148 p) (nonnegative16 p)
def d299 (p : Pattern) : Int := if p 132 then d298 p else d293 p
theorem agree299 (p q : Pattern) (h : Agree support p q) : d299 p = d299 q := by
  simp only [d299, h 132 (by decide), agree298 p q h, agree293 p q h]
theorem nonnegative299 (p : Pattern) : 0 ≤ d299 p :=
  nonnegative_ite (p 132) (nonnegative298 p) (nonnegative293 p)
def d300 (p : Pattern) : Int := if p 113 then d299 p else d293 p
theorem agree300 (p q : Pattern) (h : Agree support p q) : d300 p = d300 q := by
  simp only [d300, h 113 (by decide), agree299 p q h, agree293 p q h]
theorem nonnegative300 (p : Pattern) : 0 ≤ d300 p :=
  nonnegative_ite (p 113) (nonnegative299 p) (nonnegative293 p)
def d301 (p : Pattern) : Int := if p 112 then d296 p else d300 p
theorem agree301 (p q : Pattern) (h : Agree support p q) : d301 p = d301 q := by
  simp only [d301, h 112 (by decide), agree296 p q h, agree300 p q h]
theorem nonnegative301 (p : Pattern) : 0 ≤ d301 p :=
  nonnegative_ite (p 112) (nonnegative296 p) (nonnegative300 p)
def d302 (p : Pattern) : Int := if p 106 then d301 p else d297 p
theorem agree302 (p q : Pattern) (h : Agree support p q) : d302 p = d302 q := by
  simp only [d302, h 106 (by decide), agree301 p q h, agree297 p q h]
theorem nonnegative302 (p : Pattern) : 0 ≤ d302 p :=
  nonnegative_ite (p 106) (nonnegative301 p) (nonnegative297 p)
def d303 (p : Pattern) : Int := if p 133 then d140 p else d86 p
theorem agree303 (p q : Pattern) (h : Agree support p q) : d303 p = d303 q := by
  simp only [d303, h 133 (by decide), agree140 p q h, agree86 p q h]
theorem nonnegative303 (p : Pattern) : 0 ≤ d303 p :=
  nonnegative_ite (p 133) (nonnegative140 p) (nonnegative86 p)
def d304 (p : Pattern) : Int := if p 133 then d148 p else d86 p
theorem agree304 (p q : Pattern) (h : Agree support p q) : d304 p = d304 q := by
  simp only [d304, h 133 (by decide), agree148 p q h, agree86 p q h]
theorem nonnegative304 (p : Pattern) : 0 ≤ d304 p :=
  nonnegative_ite (p 133) (nonnegative148 p) (nonnegative86 p)
def d305 (p : Pattern) : Int := if p 132 then d304 p else d303 p
theorem agree305 (p q : Pattern) (h : Agree support p q) : d305 p = d305 q := by
  simp only [d305, h 132 (by decide), agree304 p q h, agree303 p q h]
theorem nonnegative305 (p : Pattern) : 0 ≤ d305 p :=
  nonnegative_ite (p 132) (nonnegative304 p) (nonnegative303 p)
def d306 (p : Pattern) : Int := if p 113 then d305 p else d293 p
theorem agree306 (p q : Pattern) (h : Agree support p q) : d306 p = d306 q := by
  simp only [d306, h 113 (by decide), agree305 p q h, agree293 p q h]
theorem nonnegative306 (p : Pattern) : 0 ≤ d306 p :=
  nonnegative_ite (p 113) (nonnegative305 p) (nonnegative293 p)
def d307 (p : Pattern) : Int := if p 133 then d2 p else d98 p
theorem agree307 (p q : Pattern) (h : Agree support p q) : d307 p = d307 q := by
  simp only [d307, h 133 (by decide), agree2 p q h, agree98 p q h]
theorem nonnegative307 (p : Pattern) : 0 ≤ d307 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative98 p)
def d308 (p : Pattern) : Int := if p 112 then d307 p else d306 p
theorem agree308 (p q : Pattern) (h : Agree support p q) : d308 p = d308 q := by
  simp only [d308, h 112 (by decide), agree307 p q h, agree306 p q h]
theorem nonnegative308 (p : Pattern) : 0 ≤ d308 p :=
  nonnegative_ite (p 112) (nonnegative307 p) (nonnegative306 p)
def d309 (p : Pattern) : Int := if p 133 then d2 p else d86 p
theorem agree309 (p q : Pattern) (h : Agree support p q) : d309 p = d309 q := by
  simp only [d309, h 133 (by decide), agree2 p q h, agree86 p q h]
theorem nonnegative309 (p : Pattern) : 0 ≤ d309 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative86 p)
def d310 (p : Pattern) : Int := if p 132 then d309 p else d304 p
theorem agree310 (p q : Pattern) (h : Agree support p q) : d310 p = d310 q := by
  simp only [d310, h 132 (by decide), agree309 p q h, agree304 p q h]
theorem nonnegative310 (p : Pattern) : 0 ≤ d310 p :=
  nonnegative_ite (p 132) (nonnegative309 p) (nonnegative304 p)
def d311 (p : Pattern) : Int := if p 113 then d310 p else d299 p
theorem agree311 (p q : Pattern) (h : Agree support p q) : d311 p = d311 q := by
  simp only [d311, h 113 (by decide), agree310 p q h, agree299 p q h]
theorem nonnegative311 (p : Pattern) : 0 ≤ d311 p :=
  nonnegative_ite (p 113) (nonnegative310 p) (nonnegative299 p)
def d312 (p : Pattern) : Int := if p 133 then d2 p else d97 p
theorem agree312 (p q : Pattern) (h : Agree support p q) : d312 p = d312 q := by
  simp only [d312, h 133 (by decide), agree2 p q h, agree97 p q h]
theorem nonnegative312 (p : Pattern) : 0 ≤ d312 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative97 p)
def d313 (p : Pattern) : Int := if p 113 then d312 p else d307 p
theorem agree313 (p q : Pattern) (h : Agree support p q) : d313 p = d313 q := by
  simp only [d313, h 113 (by decide), agree312 p q h, agree307 p q h]
theorem nonnegative313 (p : Pattern) : 0 ≤ d313 p :=
  nonnegative_ite (p 113) (nonnegative312 p) (nonnegative307 p)
def d314 (p : Pattern) : Int := if p 112 then d313 p else d311 p
theorem agree314 (p q : Pattern) (h : Agree support p q) : d314 p = d314 q := by
  simp only [d314, h 112 (by decide), agree313 p q h, agree311 p q h]
theorem nonnegative314 (p : Pattern) : 0 ≤ d314 p :=
  nonnegative_ite (p 112) (nonnegative313 p) (nonnegative311 p)
def d315 (p : Pattern) : Int := if p 106 then d314 p else d308 p
theorem agree315 (p q : Pattern) (h : Agree support p q) : d315 p = d315 q := by
  simp only [d315, h 106 (by decide), agree314 p q h, agree308 p q h]
theorem nonnegative315 (p : Pattern) : 0 ≤ d315 p :=
  nonnegative_ite (p 106) (nonnegative314 p) (nonnegative308 p)
def d316 (p : Pattern) : Int := if p 86 then d315 p else d302 p
theorem agree316 (p q : Pattern) (h : Agree support p q) : d316 p = d316 q := by
  simp only [d316, h 86 (by decide), agree315 p q h, agree302 p q h]
theorem nonnegative316 (p : Pattern) : 0 ≤ d316 p :=
  nonnegative_ite (p 86) (nonnegative315 p) (nonnegative302 p)
def d317 (p : Pattern) : Int := if p 133 then d2 p else d16 p
theorem agree317 (p q : Pattern) (h : Agree support p q) : d317 p = d317 q := by
  simp only [d317, h 133 (by decide), agree2 p q h, agree16 p q h]
theorem nonnegative317 (p : Pattern) : 0 ≤ d317 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative16 p)
def d318 (p : Pattern) : Int := if p 132 then d317 p else d298 p
theorem agree318 (p q : Pattern) (h : Agree support p q) : d318 p = d318 q := by
  simp only [d318, h 132 (by decide), agree317 p q h, agree298 p q h]
theorem nonnegative318 (p : Pattern) : 0 ≤ d318 p :=
  nonnegative_ite (p 132) (nonnegative317 p) (nonnegative298 p)
def d319 (p : Pattern) : Int := if p 113 then d318 p else d299 p
theorem agree319 (p q : Pattern) (h : Agree support p q) : d319 p = d319 q := by
  simp only [d319, h 113 (by decide), agree318 p q h, agree299 p q h]
theorem nonnegative319 (p : Pattern) : 0 ≤ d319 p :=
  nonnegative_ite (p 113) (nonnegative318 p) (nonnegative299 p)
def d320 (p : Pattern) : Int := if p 112 then d296 p else d319 p
theorem agree320 (p q : Pattern) (h : Agree support p q) : d320 p = d320 q := by
  simp only [d320, h 112 (by decide), agree296 p q h, agree319 p q h]
theorem nonnegative320 (p : Pattern) : 0 ≤ d320 p :=
  nonnegative_ite (p 112) (nonnegative296 p) (nonnegative319 p)
def d321 (p : Pattern) : Int := if p 106 then d320 p else d301 p
theorem agree321 (p q : Pattern) (h : Agree support p q) : d321 p = d321 q := by
  simp only [d321, h 106 (by decide), agree320 p q h, agree301 p q h]
theorem nonnegative321 (p : Pattern) : 0 ≤ d321 p :=
  nonnegative_ite (p 106) (nonnegative320 p) (nonnegative301 p)
def d322 (p : Pattern) : Int := if p 113 then d295 p else d318 p
theorem agree322 (p q : Pattern) (h : Agree support p q) : d322 p = d322 q := by
  simp only [d322, h 113 (by decide), agree295 p q h, agree318 p q h]
theorem nonnegative322 (p : Pattern) : 0 ≤ d322 p :=
  nonnegative_ite (p 113) (nonnegative295 p) (nonnegative318 p)
def d323 (p : Pattern) : Int := if p 113 then d2 p else d312 p
theorem agree323 (p q : Pattern) (h : Agree support p q) : d323 p = d323 q := by
  simp only [d323, h 113 (by decide), agree2 p q h, agree312 p q h]
theorem nonnegative323 (p : Pattern) : 0 ≤ d323 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative312 p)
def d324 (p : Pattern) : Int := if p 112 then d323 p else d322 p
theorem agree324 (p q : Pattern) (h : Agree support p q) : d324 p = d324 q := by
  simp only [d324, h 112 (by decide), agree323 p q h, agree322 p q h]
theorem nonnegative324 (p : Pattern) : 0 ≤ d324 p :=
  nonnegative_ite (p 112) (nonnegative323 p) (nonnegative322 p)
def d325 (p : Pattern) : Int := if p 106 then d324 p else d314 p
theorem agree325 (p q : Pattern) (h : Agree support p q) : d325 p = d325 q := by
  simp only [d325, h 106 (by decide), agree324 p q h, agree314 p q h]
theorem nonnegative325 (p : Pattern) : 0 ≤ d325 p :=
  nonnegative_ite (p 106) (nonnegative324 p) (nonnegative314 p)
def d326 (p : Pattern) : Int := if p 86 then d325 p else d321 p
theorem agree326 (p q : Pattern) (h : Agree support p q) : d326 p = d326 q := by
  simp only [d326, h 86 (by decide), agree325 p q h, agree321 p q h]
theorem nonnegative326 (p : Pattern) : 0 ≤ d326 p :=
  nonnegative_ite (p 86) (nonnegative325 p) (nonnegative321 p)
def d327 (p : Pattern) : Int := if p 80 then d326 p else d316 p
theorem agree327 (p q : Pattern) (h : Agree support p q) : d327 p = d327 q := by
  simp only [d327, h 80 (by decide), agree326 p q h, agree316 p q h]
theorem nonnegative327 (p : Pattern) : 0 ≤ d327 p :=
  nonnegative_ite (p 80) (nonnegative326 p) (nonnegative316 p)
def d328 (p : Pattern) : Int := if p 134 then d2 p else d16 p
theorem agree328 (p q : Pattern) (h : Agree support p q) : d328 p = d328 q := by
  simp only [d328, h 134 (by decide), agree2 p q h, agree16 p q h]
theorem nonnegative328 (p : Pattern) : 0 ≤ d328 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative16 p)
def d329 (p : Pattern) : Int := if p 134 then d2 p else d42 p
theorem agree329 (p q : Pattern) (h : Agree support p q) : d329 p = d329 q := by
  simp only [d329, h 134 (by decide), agree2 p q h, agree42 p q h]
theorem nonnegative329 (p : Pattern) : 0 ≤ d329 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative42 p)
def d330 (p : Pattern) : Int := if p 133 then d329 p else d328 p
theorem agree330 (p q : Pattern) (h : Agree support p q) : d330 p = d330 q := by
  simp only [d330, h 133 (by decide), agree329 p q h, agree328 p q h]
theorem nonnegative330 (p : Pattern) : 0 ≤ d330 p :=
  nonnegative_ite (p 133) (nonnegative329 p) (nonnegative328 p)
def d331 (p : Pattern) : Int := if p 132 then d330 p else d328 p
theorem agree331 (p q : Pattern) (h : Agree support p q) : d331 p = d331 q := by
  simp only [d331, h 132 (by decide), agree330 p q h, agree328 p q h]
theorem nonnegative331 (p : Pattern) : 0 ≤ d331 p :=
  nonnegative_ite (p 132) (nonnegative330 p) (nonnegative328 p)
def d332 (p : Pattern) : Int := if p 134 then d2 p else d15 p
theorem agree332 (p q : Pattern) (h : Agree support p q) : d332 p = d332 q := by
  simp only [d332, h 134 (by decide), agree2 p q h, agree15 p q h]
theorem nonnegative332 (p : Pattern) : 0 ≤ d332 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative15 p)
def d333 (p : Pattern) : Int := if p 134 then d2 p else d41 p
theorem agree333 (p q : Pattern) (h : Agree support p q) : d333 p = d333 q := by
  simp only [d333, h 134 (by decide), agree2 p q h, agree41 p q h]
theorem nonnegative333 (p : Pattern) : 0 ≤ d333 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative41 p)
def d334 (p : Pattern) : Int := if p 133 then d333 p else d332 p
theorem agree334 (p q : Pattern) (h : Agree support p q) : d334 p = d334 q := by
  simp only [d334, h 133 (by decide), agree333 p q h, agree332 p q h]
theorem nonnegative334 (p : Pattern) : 0 ≤ d334 p :=
  nonnegative_ite (p 133) (nonnegative333 p) (nonnegative332 p)
def d335 (p : Pattern) : Int := if p 132 then d334 p else d332 p
theorem agree335 (p q : Pattern) (h : Agree support p q) : d335 p = d335 q := by
  simp only [d335, h 132 (by decide), agree334 p q h, agree332 p q h]
theorem nonnegative335 (p : Pattern) : 0 ≤ d335 p :=
  nonnegative_ite (p 132) (nonnegative334 p) (nonnegative332 p)
def d336 (p : Pattern) : Int := if p 134 then d2 p else d53 p
theorem agree336 (p q : Pattern) (h : Agree support p q) : d336 p = d336 q := by
  simp only [d336, h 134 (by decide), agree2 p q h, agree53 p q h]
theorem nonnegative336 (p : Pattern) : 0 ≤ d336 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative53 p)
def d337 (p : Pattern) : Int := if p 134 then d2 p else d62 p
theorem agree337 (p q : Pattern) (h : Agree support p q) : d337 p = d337 q := by
  simp only [d337, h 134 (by decide), agree2 p q h, agree62 p q h]
theorem nonnegative337 (p : Pattern) : 0 ≤ d337 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative62 p)
def d338 (p : Pattern) : Int := if p 133 then d337 p else d336 p
theorem agree338 (p q : Pattern) (h : Agree support p q) : d338 p = d338 q := by
  simp only [d338, h 133 (by decide), agree337 p q h, agree336 p q h]
theorem nonnegative338 (p : Pattern) : 0 ≤ d338 p :=
  nonnegative_ite (p 133) (nonnegative337 p) (nonnegative336 p)
def d339 (p : Pattern) : Int := if p 132 then d338 p else d336 p
theorem agree339 (p q : Pattern) (h : Agree support p q) : d339 p = d339 q := by
  simp only [d339, h 132 (by decide), agree338 p q h, agree336 p q h]
theorem nonnegative339 (p : Pattern) : 0 ≤ d339 p :=
  nonnegative_ite (p 132) (nonnegative338 p) (nonnegative336 p)
def d340 (p : Pattern) : Int := if p 113 then d339 p else d335 p
theorem agree340 (p q : Pattern) (h : Agree support p q) : d340 p = d340 q := by
  simp only [d340, h 113 (by decide), agree339 p q h, agree335 p q h]
theorem nonnegative340 (p : Pattern) : 0 ≤ d340 p :=
  nonnegative_ite (p 113) (nonnegative339 p) (nonnegative335 p)
def d341 (p : Pattern) : Int := if p 112 then d340 p else d331 p
theorem agree341 (p q : Pattern) (h : Agree support p q) : d341 p = d341 q := by
  simp only [d341, h 112 (by decide), agree340 p q h, agree331 p q h]
theorem nonnegative341 (p : Pattern) : 0 ≤ d341 p :=
  nonnegative_ite (p 112) (nonnegative340 p) (nonnegative331 p)
def d342 (p : Pattern) : Int := if p 134 then d2 p else d69 p
theorem agree342 (p q : Pattern) (h : Agree support p q) : d342 p = d342 q := by
  simp only [d342, h 134 (by decide), agree2 p q h, agree69 p q h]
theorem nonnegative342 (p : Pattern) : 0 ≤ d342 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative69 p)
def d343 (p : Pattern) : Int := if p 133 then d342 p else d328 p
theorem agree343 (p q : Pattern) (h : Agree support p q) : d343 p = d343 q := by
  simp only [d343, h 133 (by decide), agree342 p q h, agree328 p q h]
theorem nonnegative343 (p : Pattern) : 0 ≤ d343 p :=
  nonnegative_ite (p 133) (nonnegative342 p) (nonnegative328 p)
def d344 (p : Pattern) : Int := if p 132 then d343 p else d328 p
theorem agree344 (p q : Pattern) (h : Agree support p q) : d344 p = d344 q := by
  simp only [d344, h 132 (by decide), agree343 p q h, agree328 p q h]
theorem nonnegative344 (p : Pattern) : 0 ≤ d344 p :=
  nonnegative_ite (p 132) (nonnegative343 p) (nonnegative328 p)
def d345 (p : Pattern) : Int := if p 134 then d2 p else d68 p
theorem agree345 (p q : Pattern) (h : Agree support p q) : d345 p = d345 q := by
  simp only [d345, h 134 (by decide), agree2 p q h, agree68 p q h]
theorem nonnegative345 (p : Pattern) : 0 ≤ d345 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative68 p)
def d346 (p : Pattern) : Int := if p 133 then d345 p else d328 p
theorem agree346 (p q : Pattern) (h : Agree support p q) : d346 p = d346 q := by
  simp only [d346, h 133 (by decide), agree345 p q h, agree328 p q h]
theorem nonnegative346 (p : Pattern) : 0 ≤ d346 p :=
  nonnegative_ite (p 133) (nonnegative345 p) (nonnegative328 p)
def d347 (p : Pattern) : Int := if p 132 then d346 p else d328 p
theorem agree347 (p q : Pattern) (h : Agree support p q) : d347 p = d347 q := by
  simp only [d347, h 132 (by decide), agree346 p q h, agree328 p q h]
theorem nonnegative347 (p : Pattern) : 0 ≤ d347 p :=
  nonnegative_ite (p 132) (nonnegative346 p) (nonnegative328 p)
def d348 (p : Pattern) : Int := if p 113 then d347 p else d344 p
theorem agree348 (p q : Pattern) (h : Agree support p q) : d348 p = d348 q := by
  simp only [d348, h 113 (by decide), agree347 p q h, agree344 p q h]
theorem nonnegative348 (p : Pattern) : 0 ≤ d348 p :=
  nonnegative_ite (p 113) (nonnegative347 p) (nonnegative344 p)
def d349 (p : Pattern) : Int := if p 133 then d345 p else d332 p
theorem agree349 (p q : Pattern) (h : Agree support p q) : d349 p = d349 q := by
  simp only [d349, h 133 (by decide), agree345 p q h, agree332 p q h]
theorem nonnegative349 (p : Pattern) : 0 ≤ d349 p :=
  nonnegative_ite (p 133) (nonnegative345 p) (nonnegative332 p)
def d350 (p : Pattern) : Int := if p 132 then d349 p else d332 p
theorem agree350 (p q : Pattern) (h : Agree support p q) : d350 p = d350 q := by
  simp only [d350, h 132 (by decide), agree349 p q h, agree332 p q h]
theorem nonnegative350 (p : Pattern) : 0 ≤ d350 p :=
  nonnegative_ite (p 132) (nonnegative349 p) (nonnegative332 p)
def d351 (p : Pattern) : Int := if p 133 then d345 p else d336 p
theorem agree351 (p q : Pattern) (h : Agree support p q) : d351 p = d351 q := by
  simp only [d351, h 133 (by decide), agree345 p q h, agree336 p q h]
theorem nonnegative351 (p : Pattern) : 0 ≤ d351 p :=
  nonnegative_ite (p 133) (nonnegative345 p) (nonnegative336 p)
def d352 (p : Pattern) : Int := if p 132 then d351 p else d336 p
theorem agree352 (p q : Pattern) (h : Agree support p q) : d352 p = d352 q := by
  simp only [d352, h 132 (by decide), agree351 p q h, agree336 p q h]
theorem nonnegative352 (p : Pattern) : 0 ≤ d352 p :=
  nonnegative_ite (p 132) (nonnegative351 p) (nonnegative336 p)
def d353 (p : Pattern) : Int := if p 113 then d352 p else d350 p
theorem agree353 (p q : Pattern) (h : Agree support p q) : d353 p = d353 q := by
  simp only [d353, h 113 (by decide), agree352 p q h, agree350 p q h]
theorem nonnegative353 (p : Pattern) : 0 ≤ d353 p :=
  nonnegative_ite (p 113) (nonnegative352 p) (nonnegative350 p)
def d354 (p : Pattern) : Int := if p 112 then d353 p else d348 p
theorem agree354 (p q : Pattern) (h : Agree support p q) : d354 p = d354 q := by
  simp only [d354, h 112 (by decide), agree353 p q h, agree348 p q h]
theorem nonnegative354 (p : Pattern) : 0 ≤ d354 p :=
  nonnegative_ite (p 112) (nonnegative353 p) (nonnegative348 p)
def d355 (p : Pattern) : Int := if p 106 then d354 p else d341 p
theorem agree355 (p q : Pattern) (h : Agree support p q) : d355 p = d355 q := by
  simp only [d355, h 106 (by decide), agree354 p q h, agree341 p q h]
theorem nonnegative355 (p : Pattern) : 0 ≤ d355 p :=
  nonnegative_ite (p 106) (nonnegative354 p) (nonnegative341 p)
def d356 (p : Pattern) : Int := if p 134 then d2 p else d86 p
theorem agree356 (p q : Pattern) (h : Agree support p q) : d356 p = d356 q := by
  simp only [d356, h 134 (by decide), agree2 p q h, agree86 p q h]
theorem nonnegative356 (p : Pattern) : 0 ≤ d356 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative86 p)
def d357 (p : Pattern) : Int := if p 134 then d2 p else d92 p
theorem agree357 (p q : Pattern) (h : Agree support p q) : d357 p = d357 q := by
  simp only [d357, h 134 (by decide), agree2 p q h, agree92 p q h]
theorem nonnegative357 (p : Pattern) : 0 ≤ d357 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative92 p)
def d358 (p : Pattern) : Int := if p 133 then d357 p else d356 p
theorem agree358 (p q : Pattern) (h : Agree support p q) : d358 p = d358 q := by
  simp only [d358, h 133 (by decide), agree357 p q h, agree356 p q h]
theorem nonnegative358 (p : Pattern) : 0 ≤ d358 p :=
  nonnegative_ite (p 133) (nonnegative357 p) (nonnegative356 p)
def d359 (p : Pattern) : Int := if p 132 then d358 p else d356 p
theorem agree359 (p q : Pattern) (h : Agree support p q) : d359 p = d359 q := by
  simp only [d359, h 132 (by decide), agree358 p q h, agree356 p q h]
theorem nonnegative359 (p : Pattern) : 0 ≤ d359 p :=
  nonnegative_ite (p 132) (nonnegative358 p) (nonnegative356 p)
end NetHack.Sokoban32Refined
