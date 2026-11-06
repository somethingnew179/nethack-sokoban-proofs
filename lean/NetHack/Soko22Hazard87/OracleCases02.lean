import NetHack.Soko22Hazard87.OracleCases01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases200 : List OracleBranch := []
noncomputable def rowCases201 : List OracleBranch := [((.walk 105), d1), ((.push 105 (.stay 127)), d0)]
theorem oracleMember174 : ((.walk 105), d1) ∈ rowCases201 := by
  exact List.mem_cons_self
theorem oracleMember175 : ((.push 105 (.stay 127)), d0) ∈ rowCases201 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases202 : List OracleBranch := [((.walk 84), d1)]
theorem oracleMember176 : ((.walk 84), d1) ∈ rowCases202 := by
  exact List.mem_cons_self
noncomputable def rowCases203 : List OracleBranch := [((.walk 82), d1), ((.push 82 (.stay 81)), d0)]
theorem oracleMember177 : ((.walk 82), d1) ∈ rowCases203 := by
  exact List.mem_cons_self
theorem oracleMember178 : ((.push 82 (.stay 81)), d0) ∈ rowCases203 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases204 : List OracleBranch := []
noncomputable def rowCases205 : List OracleBranch := []
noncomputable def rowCases206 : List OracleBranch := [((.walk 106), d1)]
theorem oracleMember179 : ((.walk 106), d1) ∈ rowCases206 := by
  exact List.mem_cons_self
noncomputable def rowCases207 : List OracleBranch := [((.walk 104), d1)]
theorem oracleMember180 : ((.walk 104), d1) ∈ rowCases207 := by
  exact List.mem_cons_self
noncomputable def rowCases208 : List OracleBranch := []
noncomputable def rowCases209 : List OracleBranch := [((.walk 106), d1), ((.push 106 (.stay 128)), d0)]
theorem oracleMember181 : ((.walk 106), d1) ∈ rowCases209 := by
  exact List.mem_cons_self
theorem oracleMember182 : ((.push 106 (.stay 128)), d0) ∈ rowCases209 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases210 : List OracleBranch := []
noncomputable def rowCases211 : List OracleBranch := [((.walk 83), d1), ((.push 83 (.stay 82)), d0)]
theorem oracleMember183 : ((.walk 83), d1) ∈ rowCases211 := by
  exact List.mem_cons_self
theorem oracleMember184 : ((.push 83 (.stay 82)), d0) ∈ rowCases211 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases212 : List OracleBranch := []
noncomputable def rowCases213 : List OracleBranch := []
noncomputable def rowCases214 : List OracleBranch := []
noncomputable def rowCases215 : List OracleBranch := [((.walk 105), d1)]
theorem oracleMember185 : ((.walk 105), d1) ∈ rowCases215 := by
  exact List.mem_cons_self
noncomputable def rowCases216 : List OracleBranch := [((.walk 67), d67301), ((.push 67 (.stay 45)), d57576)]
theorem oracleMember186 : ((.walk 67), d67301) ∈ rowCases216 := by
  exact List.mem_cons_self
theorem oracleMember187 : ((.push 67 (.stay 45)), d57576) ∈ rowCases216 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases217 : List OracleBranch := [((.walk 111), d74075), ((.push 111 (.stay 133)), d74854)]
theorem oracleMember188 : ((.walk 111), d74075) ∈ rowCases217 := by
  exact List.mem_cons_self
theorem oracleMember189 : ((.push 111 (.stay 133)), d74854) ∈ rowCases217 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases218 : List OracleBranch := [((.walk 90), d68222), ((.push 90 (.stay 91)), d74857)]
theorem oracleMember190 : ((.walk 90), d68222) ∈ rowCases218 := by
  exact List.mem_cons_self
theorem oracleMember191 : ((.push 90 (.stay 91)), d74857) ∈ rowCases218 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases219 : List OracleBranch := []
noncomputable def rowCases220 : List OracleBranch := []
noncomputable def rowCases221 : List OracleBranch := []
noncomputable def rowCases222 : List OracleBranch := []
noncomputable def rowCases223 : List OracleBranch := []
noncomputable def rowCases224 : List OracleBranch := []
noncomputable def rowCases225 : List OracleBranch := []
noncomputable def rowCases226 : List OracleBranch := [((.walk 91), d73190)]
theorem oracleMember192 : ((.walk 91), d73190) ∈ rowCases226 := by
  exact List.mem_cons_self
noncomputable def rowCases227 : List OracleBranch := [((.walk 89), d68222)]
theorem oracleMember193 : ((.walk 89), d68222) ∈ rowCases227 := by
  exact List.mem_cons_self
noncomputable def rowCases228 : List OracleBranch := [((.walk 69), d73191)]
theorem oracleMember194 : ((.walk 69), d73191) ∈ rowCases228 := by
  exact List.mem_cons_self
noncomputable def rowCases229 : List OracleBranch := [((.walk 67), d68223)]
theorem oracleMember195 : ((.walk 67), d68223) ∈ rowCases229 := by
  exact List.mem_cons_self
noncomputable def rowCases230 : List OracleBranch := [((.walk 113), d75630)]
theorem oracleMember196 : ((.walk 113), d75630) ∈ rowCases230 := by
  exact List.mem_cons_self
noncomputable def rowCases231 : List OracleBranch := [((.walk 111), d77113)]
theorem oracleMember197 : ((.walk 111), d77113) ∈ rowCases231 := by
  exact List.mem_cons_self
noncomputable def rowCases232 : List OracleBranch := [((.walk 69), d68751), ((.push 69 (.stay 47)), d58750)]
theorem oracleMember198 : ((.walk 69), d68751) ∈ rowCases232 := by
  exact List.mem_cons_self
theorem oracleMember199 : ((.push 69 (.stay 47)), d58750) ∈ rowCases232 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases233 : List OracleBranch := [((.walk 113), d75629), ((.push 113 (.stay 135)), d77845)]
theorem oracleMember200 : ((.walk 113), d75629) ∈ rowCases233 := by
  exact List.mem_cons_self
theorem oracleMember201 : ((.push 113 (.stay 135)), d77845) ∈ rowCases233 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases234 : List OracleBranch := []
noncomputable def rowCases235 : List OracleBranch := [((.walk 90), d73190), ((.push 90 (.stay 89)), d74857)]
theorem oracleMember202 : ((.walk 90), d73190) ∈ rowCases235 := by
  exact List.mem_cons_self
theorem oracleMember203 : ((.push 90 (.stay 89)), d74857) ∈ rowCases235 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases236 : List OracleBranch := [((.walk 70), d73495)]
theorem oracleMember204 : ((.walk 70), d73495) ∈ rowCases236 := by
  exact List.mem_cons_self
noncomputable def rowCases237 : List OracleBranch := []
noncomputable def rowCases238 : List OracleBranch := [((.walk 114), d81525)]
theorem oracleMember205 : ((.walk 114), d81525) ∈ rowCases238 := by
  exact List.mem_cons_self
noncomputable def rowCases239 : List OracleBranch := []
noncomputable def rowCases240 : List OracleBranch := [((.walk 71), d73492), ((.push 71 (.stay 49)), d62939)]
theorem oracleMember206 : ((.walk 71), d73492) ∈ rowCases240 := by
  exact List.mem_cons_self
theorem oracleMember207 : ((.push 71 (.stay 49)), d62939) ∈ rowCases240 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases241 : List OracleBranch := [((.walk 115), d82320)]
theorem oracleMember208 : ((.walk 115), d82320) ∈ rowCases241 := by
  exact List.mem_cons_self
noncomputable def rowCases242 : List OracleBranch := [((.walk 94), d82321), ((.push 94 (.stay 95)), d82324)]
theorem oracleMember209 : ((.walk 94), d82321) ∈ rowCases242 := by
  exact List.mem_cons_self
theorem oracleMember210 : ((.push 94 (.stay 95)), d82324) ∈ rowCases242 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases243 : List OracleBranch := []
noncomputable def rowCases244 : List OracleBranch := []
noncomputable def rowCases245 : List OracleBranch := [((.walk 70), d73493)]
theorem oracleMember211 : ((.walk 70), d73493) ∈ rowCases245 := by
  exact List.mem_cons_self
noncomputable def rowCases246 : List OracleBranch := [((.walk 116), d82333)]
theorem oracleMember212 : ((.walk 116), d82333) ∈ rowCases246 := by
  exact List.mem_cons_self
noncomputable def rowCases247 : List OracleBranch := [((.walk 114), d82334)]
theorem oracleMember213 : ((.walk 114), d82334) ∈ rowCases247 := by
  exact List.mem_cons_self
noncomputable def rowCases248 : List OracleBranch := []
noncomputable def rowCases249 : List OracleBranch := [((.walk 116), d82335), ((.push 116 (.stay 138)), d82340)]
theorem oracleMember214 : ((.walk 116), d82335) ∈ rowCases249 := by
  exact List.mem_cons_self
theorem oracleMember215 : ((.push 116 (.stay 138)), d82340) ∈ rowCases249 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases250 : List OracleBranch := [((.walk 95), d82347), ((.push 95 (.stay 96)), d82350)]
theorem oracleMember216 : ((.walk 95), d82347) ∈ rowCases250 := by
  exact List.mem_cons_self
theorem oracleMember217 : ((.push 95 (.stay 96)), d82350) ∈ rowCases250 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases251 : List OracleBranch := [((.walk 93), d82321)]
theorem oracleMember218 : ((.walk 93), d82321) ∈ rowCases251 := by
  exact List.mem_cons_self
noncomputable def rowCases252 : List OracleBranch := [((.walk 73), d74047)]
theorem oracleMember219 : ((.walk 73), d74047) ∈ rowCases252 := by
  exact List.mem_cons_self
noncomputable def rowCases253 : List OracleBranch := [((.walk 71), d74039)]
theorem oracleMember220 : ((.walk 71), d74039) ∈ rowCases253 := by
  exact List.mem_cons_self
noncomputable def rowCases254 : List OracleBranch := []
noncomputable def rowCases255 : List OracleBranch := [((.walk 115), d82355)]
theorem oracleMember221 : ((.walk 115), d82355) ∈ rowCases255 := by
  exact List.mem_cons_self
noncomputable def rowCases256 : List OracleBranch := [((.walk 73), d74040), ((.push 73 (.stay 51)), d65090)]
theorem oracleMember222 : ((.walk 73), d74040) ∈ rowCases256 := by
  exact List.mem_cons_self
theorem oracleMember223 : ((.push 73 (.stay 51)), d65090) ∈ rowCases256 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases257 : List OracleBranch := []
noncomputable def rowCases258 : List OracleBranch := [((.walk 96), d74044), ((.push 96 (.stay 97)), d82357)]
theorem oracleMember224 : ((.walk 96), d74044) ∈ rowCases258 := by
  exact List.mem_cons_self
theorem oracleMember225 : ((.push 96 (.stay 97)), d82357) ∈ rowCases258 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases259 : List OracleBranch := [((.walk 94), d82347), ((.push 94 (.stay 93)), d82324)]
theorem oracleMember226 : ((.walk 94), d82347) ∈ rowCases259 := by
  exact List.mem_cons_self
theorem oracleMember227 : ((.push 94 (.stay 93)), d82324) ∈ rowCases259 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases260 : List OracleBranch := [((.walk 74), d74062)]
theorem oracleMember228 : ((.walk 74), d74062) ∈ rowCases260 := by
  exact List.mem_cons_self
noncomputable def rowCases261 : List OracleBranch := []
noncomputable def rowCases262 : List OracleBranch := [((.walk 118), d82360)]
theorem oracleMember229 : ((.walk 118), d82360) ∈ rowCases262 := by
  exact List.mem_cons_self
noncomputable def rowCases263 : List OracleBranch := [((.walk 116), d82362)]
theorem oracleMember230 : ((.walk 116), d82362) ∈ rowCases263 := by
  exact List.mem_cons_self
noncomputable def rowCases264 : List OracleBranch := [((.walk 74), d74048), ((.push 74 (.stay 52)), d66280)]
theorem oracleMember231 : ((.walk 74), d74048) ∈ rowCases264 := by
  exact List.mem_cons_self
theorem oracleMember232 : ((.push 74 (.stay 52)), d66280) ∈ rowCases264 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases265 : List OracleBranch := [((.walk 118), d82363)]
theorem oracleMember233 : ((.walk 118), d82363) ∈ rowCases265 := by
  exact List.mem_cons_self
noncomputable def rowCases266 : List OracleBranch := [((.walk 97), d82364), ((.push 97 (.stay 98)), d82367)]
theorem oracleMember234 : ((.walk 97), d82364) ∈ rowCases266 := by
  exact List.mem_cons_self
theorem oracleMember235 : ((.push 97 (.stay 98)), d82367) ∈ rowCases266 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases267 : List OracleBranch := [((.walk 95), d74044), ((.push 95 (.stay 94)), d82350)]
theorem oracleMember236 : ((.walk 95), d74044) ∈ rowCases267 := by
  exact List.mem_cons_self
theorem oracleMember237 : ((.push 95 (.stay 94)), d82350) ∈ rowCases267 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases268 : List OracleBranch := []
noncomputable def rowCases269 : List OracleBranch := [((.walk 73), d74046)]
theorem oracleMember238 : ((.walk 73), d74046) ∈ rowCases269 := by
  exact List.mem_cons_self
noncomputable def rowCases270 : List OracleBranch := [((.walk 119), d82375)]
theorem oracleMember239 : ((.walk 119), d82375) ∈ rowCases270 := by
  exact List.mem_cons_self
noncomputable def rowCases271 : List OracleBranch := []
noncomputable def rowCases272 : List OracleBranch := []
noncomputable def rowCases273 : List OracleBranch := [((.walk 119), d82376), ((.push 119 (.stay 141)), d82381)]
theorem oracleMember240 : ((.walk 119), d82376) ∈ rowCases273 := by
  exact List.mem_cons_self
theorem oracleMember241 : ((.push 119 (.stay 141)), d82381) ∈ rowCases273 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases274 : List OracleBranch := [((.walk 98), d74073)]
theorem oracleMember242 : ((.walk 98), d74073) ∈ rowCases274 := by
  exact List.mem_cons_self
noncomputable def rowCases275 : List OracleBranch := [((.walk 96), d82364), ((.push 96 (.stay 95)), d82357)]
theorem oracleMember243 : ((.walk 96), d82364) ∈ rowCases275 := by
  exact List.mem_cons_self
theorem oracleMember244 : ((.push 96 (.stay 95)), d82357) ∈ rowCases275 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases276 : List OracleBranch := [((.walk 76), d74074)]
theorem oracleMember245 : ((.walk 76), d74074) ∈ rowCases276 := by
  exact List.mem_cons_self
noncomputable def rowCases277 : List OracleBranch := [((.walk 74), d74056)]
theorem oracleMember246 : ((.walk 74), d74056) ∈ rowCases277 := by
  exact List.mem_cons_self
noncomputable def rowCases278 : List OracleBranch := [((.walk 120), d82409)]
theorem oracleMember247 : ((.walk 120), d82409) ∈ rowCases278 := by
  exact List.mem_cons_self
noncomputable def rowCases279 : List OracleBranch := [((.walk 118), d82414)]
theorem oracleMember248 : ((.walk 118), d82414) ∈ rowCases279 := by
  exact List.mem_cons_self
noncomputable def rowCases280 : List OracleBranch := [((.walk 76), d74067)]
theorem oracleMember249 : ((.walk 76), d74067) ∈ rowCases280 := by
  exact List.mem_cons_self
noncomputable def rowCases281 : List OracleBranch := [((.walk 120), d82415)]
theorem oracleMember250 : ((.walk 120), d82415) ∈ rowCases281 := by
  exact List.mem_cons_self
noncomputable def rowCases282 : List OracleBranch := []
noncomputable def rowCases283 : List OracleBranch := [((.walk 97), d74073), ((.push 97 (.stay 96)), d82367)]
theorem oracleMember251 : ((.walk 97), d74073) ∈ rowCases283 := by
  exact List.mem_cons_self
theorem oracleMember252 : ((.push 97 (.stay 96)), d82367) ∈ rowCases283 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases284 : List OracleBranch := []
noncomputable def rowCases285 : List OracleBranch := []
noncomputable def rowCases286 : List OracleBranch := []
noncomputable def rowCases287 : List OracleBranch := [((.walk 119), d82422)]
theorem oracleMember253 : ((.walk 119), d82422) ∈ rowCases287 := by
  exact List.mem_cons_self
noncomputable def rowCases288 : List OracleBranch := [((.walk 78), d1)]
theorem oracleMember254 : ((.walk 78), d1) ∈ rowCases288 := by
  exact List.mem_cons_self
noncomputable def rowCases289 : List OracleBranch := [((.walk 122), d1), ((.push 122 (.stay 144)), d0)]
theorem oracleMember255 : ((.walk 122), d1) ∈ rowCases289 := by
  exact List.mem_cons_self
theorem oracleMember256 : ((.push 122 (.stay 144)), d0) ∈ rowCases289 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases290 : List OracleBranch := [((.walk 101), d1), ((.push 101 (.stay 102)), d0)]
theorem oracleMember257 : ((.walk 101), d1) ∈ rowCases290 := by
  exact List.mem_cons_self
theorem oracleMember258 : ((.push 101 (.stay 102)), d0) ∈ rowCases290 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases291 : List OracleBranch := []
noncomputable def rowCases292 : List OracleBranch := [((.walk 79), d1)]
theorem oracleMember259 : ((.walk 79), d1) ∈ rowCases292 := by
  exact List.mem_cons_self
noncomputable def rowCases293 : List OracleBranch := []
noncomputable def rowCases294 : List OracleBranch := [((.walk 123), d1)]
theorem oracleMember260 : ((.walk 123), d1) ∈ rowCases294 := by
  exact List.mem_cons_self
noncomputable def rowCases295 : List OracleBranch := []
noncomputable def rowCases296 : List OracleBranch := [((.walk 79), d1)]
theorem oracleMember261 : ((.walk 79), d1) ∈ rowCases296 := by
  exact List.mem_cons_self
noncomputable def rowCases297 : List OracleBranch := [((.walk 123), d1), ((.push 123 (.stay 145)), d0)]
theorem oracleMember262 : ((.walk 123), d1) ∈ rowCases297 := by
  exact List.mem_cons_self
theorem oracleMember263 : ((.push 123 (.stay 145)), d0) ∈ rowCases297 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases298 : List OracleBranch := [((.walk 102), d1), ((.push 102 (.stay 103)), d0)]
theorem oracleMember264 : ((.walk 102), d1) ∈ rowCases298 := by
  exact List.mem_cons_self
theorem oracleMember265 : ((.push 102 (.stay 103)), d0) ∈ rowCases298 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases299 : List OracleBranch := [((.walk 100), d1)]
theorem oracleMember266 : ((.walk 100), d1) ∈ rowCases299 := by
  exact List.mem_cons_self
end NetHack.Soko22Hazard87
