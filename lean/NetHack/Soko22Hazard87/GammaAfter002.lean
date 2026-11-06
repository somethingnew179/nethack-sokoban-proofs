import NetHack.Soko22Hazard87.GammaAfter001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter200 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) = d6737 p := by
  change bonus 113 _ = _
  rw [at113]
  rfl
theorem gammaAfter201 (p : Pattern) : bonus (HazardPattern.nextHero (.push 113 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 135))) = d78794 p := by
  change bonus 113 _ = _
  rw [at113]
  change d6737 (u93 p) = d78794 p
  exact allUpdate7559 p
theorem gammaAfter202 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) = d4650 p := by
  change bonus 90 _ = _
  rw [at90]
  rfl
theorem gammaAfter203 (p : Pattern) : bonus (HazardPattern.nextHero (.push 90 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 90 (.stay 89))) = d81124 p := by
  change bonus 90 _ = _
  rw [at90]
  change d4650 (u48 p) = d81124 p
  exact allUpdate4346 p
theorem gammaAfter204 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) = d3496 p := by
  change bonus 70 _ = _
  rw [at70]
  rfl
theorem gammaAfter205 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter206 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) = d3673 p := by
  change bonus 71 _ = _
  rw [at71]
  rfl
theorem gammaAfter207 (p : Pattern) : bonus (HazardPattern.nextHero (.push 71 (.stay 49))) (HazardPattern.afterPattern 10000 p (.push 71 (.stay 49))) = d0 p := by
  change bonus 71 _ = _
  rw [at71]
  change d3673 (u30 p) = d0 p
  exact allUpdate3617 p
theorem gammaAfter208 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter209 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  rfl
theorem gammaAfter210 (p : Pattern) : bonus (HazardPattern.nextHero (.push 94 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 95))) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  change d0 (u55 p) = d0 p
  exact allUpdate13 p
theorem gammaAfter211 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 70)) (HazardPattern.afterPattern 10000 p (.walk 70)) = d3496 p := by
  change bonus 70 _ = _
  rw [at70]
  rfl
theorem gammaAfter212 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  rfl
theorem gammaAfter213 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter214 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  rfl
theorem gammaAfter215 (p : Pattern) : bonus (HazardPattern.nextHero (.push 116 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 138))) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  change d0 (u99 p) = d0 p
  exact allUpdate51 p
theorem gammaAfter216 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  rfl
theorem gammaAfter217 (p : Pattern) : bonus (HazardPattern.nextHero (.push 95 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 96))) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  change d0 (u57 p) = d0 p
  exact allUpdate15 p
theorem gammaAfter218 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) = d0 p := by
  change bonus 93 _ = _
  rw [at93]
  rfl
theorem gammaAfter219 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) = d3842 p := by
  change bonus 73 _ = _
  rw [at73]
  rfl
theorem gammaAfter220 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 71)) (HazardPattern.afterPattern 10000 p (.walk 71)) = d3673 p := by
  change bonus 71 _ = _
  rw [at71]
  rfl
theorem gammaAfter221 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter222 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) = d3842 p := by
  change bonus 73 _ = _
  rw [at73]
  rfl
theorem gammaAfter223 (p : Pattern) : bonus (HazardPattern.nextHero (.push 73 (.stay 51))) (HazardPattern.afterPattern 10000 p (.push 73 (.stay 51))) = d0 p := by
  change bonus 73 _ = _
  rw [at73]
  change d3842 (u32 p) = d0 p
  exact allUpdate3897 p
theorem gammaAfter224 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  rfl
theorem gammaAfter225 (p : Pattern) : bonus (HazardPattern.nextHero (.push 96 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 97))) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  change d0 (u60 p) = d0 p
  exact allUpdate18 p
theorem gammaAfter226 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  rfl
theorem gammaAfter227 (p : Pattern) : bonus (HazardPattern.nextHero (.push 94 (.stay 93))) (HazardPattern.afterPattern 10000 p (.push 94 (.stay 93))) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  change d0 (u54 p) = d0 p
  exact allUpdate12 p
theorem gammaAfter228 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) = d4025 p := by
  change bonus 74 _ = _
  rw [at74]
  rfl
theorem gammaAfter229 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) = d0 p := by
  change bonus 118 _ = _
  rw [at118]
  rfl
theorem gammaAfter230 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  rfl
theorem gammaAfter231 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) = d4025 p := by
  change bonus 74 _ = _
  rw [at74]
  rfl
theorem gammaAfter232 (p : Pattern) : bonus (HazardPattern.nextHero (.push 74 (.stay 52))) (HazardPattern.afterPattern 10000 p (.push 74 (.stay 52))) = d0 p := by
  change bonus 74 _ = _
  rw [at74]
  change d4025 (u34 p) = d0 p
  exact allUpdate4032 p
theorem gammaAfter233 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) = d0 p := by
  change bonus 118 _ = _
  rw [at118]
  rfl
theorem gammaAfter234 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  rfl
theorem gammaAfter235 (p : Pattern) : bonus (HazardPattern.nextHero (.push 97 (.stay 98))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 98))) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  change d0 (u63 p) = d0 p
  exact allUpdate21 p
theorem gammaAfter236 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  rfl
theorem gammaAfter237 (p : Pattern) : bonus (HazardPattern.nextHero (.push 95 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 95 (.stay 94))) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  change d0 (u56 p) = d0 p
  exact allUpdate14 p
theorem gammaAfter238 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 73)) (HazardPattern.afterPattern 10000 p (.walk 73)) = d3842 p := by
  change bonus 73 _ = _
  rw [at73]
  rfl
theorem gammaAfter239 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter240 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter241 (p : Pattern) : bonus (HazardPattern.nextHero (.push 119 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 141))) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  change d0 (u103 p) = d0 p
  exact allUpdate55 p
theorem gammaAfter242 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) = d0 p := by
  change bonus 98 _ = _
  rw [at98]
  rfl
theorem gammaAfter243 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  rfl
theorem gammaAfter244 (p : Pattern) : bonus (HazardPattern.nextHero (.push 96 (.stay 95))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 95))) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  change d0 (u59 p) = d0 p
  exact allUpdate17 p
theorem gammaAfter245 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) = d0 p := by
  change bonus 76 _ = _
  rw [at76]
  rfl
theorem gammaAfter246 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 74)) (HazardPattern.afterPattern 10000 p (.walk 74)) = d4025 p := by
  change bonus 74 _ = _
  rw [at74]
  rfl
theorem gammaAfter247 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) = d0 p := by
  change bonus 120 _ = _
  rw [at120]
  rfl
theorem gammaAfter248 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) = d0 p := by
  change bonus 118 _ = _
  rw [at118]
  rfl
theorem gammaAfter249 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 76)) (HazardPattern.afterPattern 10000 p (.walk 76)) = d0 p := by
  change bonus 76 _ = _
  rw [at76]
  rfl
theorem gammaAfter250 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) = d0 p := by
  change bonus 120 _ = _
  rw [at120]
  rfl
theorem gammaAfter251 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  rfl
theorem gammaAfter252 (p : Pattern) : bonus (HazardPattern.nextHero (.push 97 (.stay 96))) (HazardPattern.afterPattern 10000 p (.push 97 (.stay 96))) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  change d0 (u62 p) = d0 p
  exact allUpdate20 p
theorem gammaAfter253 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter254 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) = d0 p := by
  change bonus 78 _ = _
  rw [at78]
  rfl
theorem gammaAfter255 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  rfl
theorem gammaAfter256 (p : Pattern) : bonus (HazardPattern.nextHero (.push 122 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 144))) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  change d0 (u105 p) = d0 p
  exact allUpdate57 p
theorem gammaAfter257 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  rfl
theorem gammaAfter258 (p : Pattern) : bonus (HazardPattern.nextHero (.push 101 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 102))) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  change d0 (u70 p) = d0 p
  exact allUpdate28 p
theorem gammaAfter259 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) = d0 p := by
  change bonus 79 _ = _
  rw [at79]
  rfl
theorem gammaAfter260 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter261 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) = d0 p := by
  change bonus 79 _ = _
  rw [at79]
  rfl
theorem gammaAfter262 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter263 (p : Pattern) : bonus (HazardPattern.nextHero (.push 123 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 145))) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  change d0 (u109 p) = d0 p
  exact allUpdate61 p
theorem gammaAfter264 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  rfl
theorem gammaAfter265 (p : Pattern) : bonus (HazardPattern.nextHero (.push 102 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 103))) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  change d0 (u74 p) = d0 p
  exact allUpdate32 p
theorem gammaAfter266 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) = d0 p := by
  change bonus 100 _ = _
  rw [at100]
  rfl
theorem gammaAfter267 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) = d0 p := by
  change bonus 80 _ = _
  rw [at80]
  rfl
theorem gammaAfter268 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 78)) (HazardPattern.afterPattern 10000 p (.walk 78)) = d0 p := by
  change bonus 78 _ = _
  rw [at78]
  rfl
theorem gammaAfter269 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter270 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  rfl
theorem gammaAfter271 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) = d0 p := by
  change bonus 80 _ = _
  rw [at80]
  rfl
theorem gammaAfter272 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter273 (p : Pattern) : bonus (HazardPattern.nextHero (.push 124 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 146))) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  change d0 (u113 p) = d0 p
  exact allUpdate65 p
theorem gammaAfter274 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  rfl
theorem gammaAfter275 (p : Pattern) : bonus (HazardPattern.nextHero (.push 103 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 104))) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  change d0 (u78 p) = d0 p
  exact allUpdate36 p
theorem gammaAfter276 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  rfl
theorem gammaAfter277 (p : Pattern) : bonus (HazardPattern.nextHero (.push 101 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 100))) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  change d0 (u69 p) = d0 p
  exact allUpdate27 p
theorem gammaAfter278 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) = d0 p := by
  change bonus 81 _ = _
  rw [at81]
  rfl
theorem gammaAfter279 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 79)) (HazardPattern.afterPattern 10000 p (.walk 79)) = d0 p := by
  change bonus 79 _ = _
  rw [at79]
  rfl
theorem gammaAfter280 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter281 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter282 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) = d0 p := by
  change bonus 81 _ = _
  rw [at81]
  rfl
theorem gammaAfter283 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter284 (p : Pattern) : bonus (HazardPattern.nextHero (.push 125 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 147))) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  change d0 (u117 p) = d0 p
  exact allUpdate69 p
theorem gammaAfter285 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  rfl
theorem gammaAfter286 (p : Pattern) : bonus (HazardPattern.nextHero (.push 104 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 105))) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  change d0 (u82 p) = d0 p
  exact allUpdate40 p
theorem gammaAfter287 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  rfl
theorem gammaAfter288 (p : Pattern) : bonus (HazardPattern.nextHero (.push 102 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 101))) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  change d0 (u73 p) = d0 p
  exact allUpdate31 p
theorem gammaAfter289 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) = d0 p := by
  change bonus 82 _ = _
  rw [at82]
  rfl
theorem gammaAfter290 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 80)) (HazardPattern.afterPattern 10000 p (.walk 80)) = d0 p := by
  change bonus 80 _ = _
  rw [at80]
  rfl
theorem gammaAfter291 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter292 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter293 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) = d0 p := by
  change bonus 82 _ = _
  rw [at82]
  rfl
theorem gammaAfter294 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter295 (p : Pattern) : bonus (HazardPattern.nextHero (.push 126 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 148))) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  change d0 (u121 p) = d0 p
  exact allUpdate73 p
theorem gammaAfter296 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  rfl
theorem gammaAfter297 (p : Pattern) : bonus (HazardPattern.nextHero (.push 105 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 106))) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  change d0 (u86 p) = d0 p
  exact allUpdate44 p
theorem gammaAfter298 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  rfl
theorem gammaAfter299 (p : Pattern) : bonus (HazardPattern.nextHero (.push 103 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 102))) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  change d0 (u77 p) = d0 p
  exact allUpdate35 p
end NetHack.Soko22Hazard87
