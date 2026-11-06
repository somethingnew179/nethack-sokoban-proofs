import NetHack.Soko22Hazard87.OldNodes012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
namespace Prior
end Prior
theorem oldNode5281 (p : Pattern) : NetHack.Sokoban22Refined85.d5281 p = d253284 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d30 p) = d253284 p
  rw [oldNode12, oldNode30]
  rfl
theorem oldNode5282 (p : Pattern) : NetHack.Sokoban22Refined85.d5282 p = d253285 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5281 p else NetHack.Sokoban22Refined85.d13 p) = d253285 p
  rw [oldNode5281, oldNode13]
  rfl
theorem oldNode5283 (p : Pattern) : NetHack.Sokoban22Refined85.d5283 p = d253286 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d34 p) = d253286 p
  rw [oldNode12, oldNode34]
  rfl
theorem oldNode5284 (p : Pattern) : NetHack.Sokoban22Refined85.d5284 p = d253287 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5283 p else NetHack.Sokoban22Refined85.d13 p) = d253287 p
  rw [oldNode5283, oldNode13]
  rfl
theorem oldNode5285 (p : Pattern) : NetHack.Sokoban22Refined85.d5285 p = d253288 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5284 p else NetHack.Sokoban22Refined85.d5282 p) = d253288 p
  rw [oldNode5284, oldNode5282]
  rfl
theorem oldNode5286 (p : Pattern) : NetHack.Sokoban22Refined85.d5286 p = d253289 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d39 p) = d253289 p
  rw [oldNode12, oldNode39]
  rfl
theorem oldNode5287 (p : Pattern) : NetHack.Sokoban22Refined85.d5287 p = d253290 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5286 p else NetHack.Sokoban22Refined85.d13 p) = d253290 p
  rw [oldNode5286, oldNode13]
  rfl
theorem oldNode5288 (p : Pattern) : NetHack.Sokoban22Refined85.d5288 p = d253291 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d17 p) = d253291 p
  rw [oldNode12, oldNode17]
  rfl
theorem oldNode5289 (p : Pattern) : NetHack.Sokoban22Refined85.d5289 p = d253292 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5288 p else NetHack.Sokoban22Refined85.d5287 p) = d253292 p
  rw [oldNode5288, oldNode5287]
  rfl
theorem oldNode5290 (p : Pattern) : NetHack.Sokoban22Refined85.d5290 p = d253293 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5289 p else NetHack.Sokoban22Refined85.d5285 p) = d253293 p
  rw [oldNode5289, oldNode5285]
  rfl
theorem oldNode5291 (p : Pattern) : NetHack.Sokoban22Refined85.d5291 p = d253294 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d13 p) = d253294 p
  rw [oldNode12, oldNode13]
  rfl
theorem oldNode5292 (p : Pattern) : NetHack.Sokoban22Refined85.d5292 p = d253295 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5288 p else NetHack.Sokoban22Refined85.d5291 p) = d253295 p
  rw [oldNode5288, oldNode5291]
  rfl
theorem oldNode5293 (p : Pattern) : NetHack.Sokoban22Refined85.d5293 p = d253296 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d23 p) = d253296 p
  rw [oldNode12, oldNode23]
  rfl
theorem oldNode5294 (p : Pattern) : NetHack.Sokoban22Refined85.d5294 p = d253297 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5293 p) = d253297 p
  rw [oldNode12, oldNode5293]
  rfl
theorem oldNode5295 (p : Pattern) : NetHack.Sokoban22Refined85.d5295 p = d253298 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5294 p else NetHack.Sokoban22Refined85.d5292 p) = d253298 p
  rw [oldNode5294, oldNode5292]
  rfl
theorem oldNode5296 (p : Pattern) : NetHack.Sokoban22Refined85.d5296 p = d253299 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5295 p else NetHack.Sokoban22Refined85.d5290 p) = d253299 p
  rw [oldNode5295, oldNode5290]
  rfl
theorem oldNode5297 (p : Pattern) : NetHack.Sokoban22Refined85.d5297 p = d253300 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5296 p else NetHack.Sokoban22Refined85.d5280 p) = d253300 p
  rw [oldNode5296, oldNode5280]
  rfl
theorem oldNode5298 (p : Pattern) : NetHack.Sokoban22Refined85.d5298 p = d253301 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5281 p else NetHack.Sokoban22Refined85.d30 p) = d253301 p
  rw [oldNode5281, oldNode30]
  rfl
theorem oldNode5299 (p : Pattern) : NetHack.Sokoban22Refined85.d5299 p = d253302 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5298 p else NetHack.Sokoban22Refined85.d5271 p) = d253302 p
  rw [oldNode5298, oldNode5271]
  rfl
theorem oldNode5300 (p : Pattern) : NetHack.Sokoban22Refined85.d5300 p = d253303 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5277 p else NetHack.Sokoban22Refined85.d5273 p) = d253303 p
  rw [oldNode5277, oldNode5273]
  rfl
theorem oldNode5301 (p : Pattern) : NetHack.Sokoban22Refined85.d5301 p = d253304 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5300 p else NetHack.Sokoban22Refined85.d5299 p) = d253304 p
  rw [oldNode5300, oldNode5299]
  rfl
theorem oldNode5302 (p : Pattern) : NetHack.Sokoban22Refined85.d5302 p = d253305 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d57 p) = d253305 p
  rw [oldNode12, oldNode57]
  rfl
theorem oldNode5303 (p : Pattern) : NetHack.Sokoban22Refined85.d5303 p = d253306 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5302 p else NetHack.Sokoban22Refined85.d57 p) = d253306 p
  rw [oldNode5302, oldNode57]
  rfl
theorem oldNode5304 (p : Pattern) : NetHack.Sokoban22Refined85.d5304 p = d253307 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5303 p else NetHack.Sokoban22Refined85.d5273 p) = d253307 p
  rw [oldNode5303, oldNode5273]
  rfl
theorem oldNode5305 (p : Pattern) : NetHack.Sokoban22Refined85.d5305 p = d253308 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5286 p else NetHack.Sokoban22Refined85.d39 p) = d253308 p
  rw [oldNode5286, oldNode39]
  rfl
theorem oldNode5306 (p : Pattern) : NetHack.Sokoban22Refined85.d5306 p = d253309 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5305 p) = d253309 p
  rw [oldNode12, oldNode5305]
  rfl
theorem oldNode5307 (p : Pattern) : NetHack.Sokoban22Refined85.d5307 p = d253310 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5306 p else NetHack.Sokoban22Refined85.d5304 p) = d253310 p
  rw [oldNode5306, oldNode5304]
  rfl
theorem oldNode5308 (p : Pattern) : NetHack.Sokoban22Refined85.d5308 p = d253311 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5307 p else NetHack.Sokoban22Refined85.d5301 p) = d253311 p
  rw [oldNode5307, oldNode5301]
  rfl
theorem oldNode5309 (p : Pattern) : NetHack.Sokoban22Refined85.d5309 p = d253312 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d30 p) = d253312 p
  rw [oldNode12, oldNode30]
  rfl
theorem oldNode5310 (p : Pattern) : NetHack.Sokoban22Refined85.d5310 p = d253313 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5309 p else NetHack.Sokoban22Refined85.d5284 p) = d253313 p
  rw [oldNode5309, oldNode5284]
  rfl
theorem oldNode5311 (p : Pattern) : NetHack.Sokoban22Refined85.d5311 p = d253314 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5293 p else NetHack.Sokoban22Refined85.d5288 p) = d253314 p
  rw [oldNode5293, oldNode5288]
  rfl
theorem oldNode5312 (p : Pattern) : NetHack.Sokoban22Refined85.d5312 p = d253315 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5311 p else NetHack.Sokoban22Refined85.d5310 p) = d253315 p
  rw [oldNode5311, oldNode5310]
  rfl
theorem oldNode5313 (p : Pattern) : NetHack.Sokoban22Refined85.d5313 p = d253316 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d57 p) = d253316 p
  rw [oldNode12, oldNode57]
  rfl
theorem oldNode5314 (p : Pattern) : NetHack.Sokoban22Refined85.d5314 p = d253317 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5313 p else NetHack.Sokoban22Refined85.d5288 p) = d253317 p
  rw [oldNode5313, oldNode5288]
  rfl
theorem oldNode5315 (p : Pattern) : NetHack.Sokoban22Refined85.d5315 p = d253318 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d39 p) = d253318 p
  rw [oldNode12, oldNode39]
  rfl
theorem oldNode5316 (p : Pattern) : NetHack.Sokoban22Refined85.d5316 p = d253319 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5315 p) = d253319 p
  rw [oldNode12, oldNode5315]
  rfl
theorem oldNode5317 (p : Pattern) : NetHack.Sokoban22Refined85.d5317 p = d253320 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5316 p else NetHack.Sokoban22Refined85.d5314 p) = d253320 p
  rw [oldNode5316, oldNode5314]
  rfl
theorem oldNode5318 (p : Pattern) : NetHack.Sokoban22Refined85.d5318 p = d253321 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5317 p else NetHack.Sokoban22Refined85.d5312 p) = d253321 p
  rw [oldNode5317, oldNode5312]
  rfl
theorem oldNode5319 (p : Pattern) : NetHack.Sokoban22Refined85.d5319 p = d253322 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5318 p else NetHack.Sokoban22Refined85.d5308 p) = d253322 p
  rw [oldNode5318, oldNode5308]
  rfl
theorem oldNode5320 (p : Pattern) : NetHack.Sokoban22Refined85.d5320 p = d253323 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5319 p else NetHack.Sokoban22Refined85.d5297 p) = d253323 p
  rw [oldNode5319, oldNode5297]
  rfl
theorem oldNode5321 (p : Pattern) : NetHack.Sokoban22Refined85.d5321 p = d253324 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5283 p else NetHack.Sokoban22Refined85.d34 p) = d253324 p
  rw [oldNode5283, oldNode34]
  rfl
theorem oldNode5322 (p : Pattern) : NetHack.Sokoban22Refined85.d5322 p = d253325 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5321 p else NetHack.Sokoban22Refined85.d5298 p) = d253325 p
  rw [oldNode5321, oldNode5298]
  rfl
theorem oldNode5323 (p : Pattern) : NetHack.Sokoban22Refined85.d5323 p = d253326 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5306 p else NetHack.Sokoban22Refined85.d5322 p) = d253326 p
  rw [oldNode5306, oldNode5322]
  rfl
theorem oldNode5324 (p : Pattern) : NetHack.Sokoban22Refined85.d5324 p = d253327 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5323 p) = d253327 p
  rw [oldNode12, oldNode5323]
  rfl
theorem oldNode5325 (p : Pattern) : NetHack.Sokoban22Refined85.d5325 p = d253328 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5324 p else NetHack.Sokoban22Refined85.d5280 p) = d253328 p
  rw [oldNode5324, oldNode5280]
  rfl
theorem oldNode5326 (p : Pattern) : NetHack.Sokoban22Refined85.d5326 p = d253329 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5321 p) = d253329 p
  rw [oldNode12, oldNode5321]
  rfl
theorem oldNode5327 (p : Pattern) : NetHack.Sokoban22Refined85.d5327 p = d253330 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5326 p) = d253330 p
  rw [oldNode12, oldNode5326]
  rfl
theorem oldNode5328 (p : Pattern) : NetHack.Sokoban22Refined85.d5328 p = d253331 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5327 p) = d253331 p
  rw [oldNode12, oldNode5327]
  rfl
theorem oldNode5329 (p : Pattern) : NetHack.Sokoban22Refined85.d5329 p = d253332 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5328 p else NetHack.Sokoban22Refined85.d5308 p) = d253332 p
  rw [oldNode5328, oldNode5308]
  rfl
theorem oldNode5330 (p : Pattern) : NetHack.Sokoban22Refined85.d5330 p = d253333 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5329 p else NetHack.Sokoban22Refined85.d5325 p) = d253333 p
  rw [oldNode5329, oldNode5325]
  rfl
theorem oldNode5331 (p : Pattern) : NetHack.Sokoban22Refined85.d5331 p = d253334 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5330 p else NetHack.Sokoban22Refined85.d5320 p) = d253334 p
  rw [oldNode5330, oldNode5320]
  rfl
theorem oldNode5332 (p : Pattern) : NetHack.Sokoban22Refined85.d5332 p = d253335 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5305 p else NetHack.Sokoban22Refined85.d5277 p) = d253335 p
  rw [oldNode5305, oldNode5277]
  rfl
theorem oldNode5333 (p : Pattern) : NetHack.Sokoban22Refined85.d5333 p = d253336 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5306 p else NetHack.Sokoban22Refined85.d5332 p) = d253336 p
  rw [oldNode5306, oldNode5332]
  rfl
theorem oldNode5334 (p : Pattern) : NetHack.Sokoban22Refined85.d5334 p = d253337 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5306 p) = d253337 p
  rw [oldNode12, oldNode5306]
  rfl
theorem oldNode5335 (p : Pattern) : NetHack.Sokoban22Refined85.d5335 p = d253338 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5334 p else NetHack.Sokoban22Refined85.d5333 p) = d253338 p
  rw [oldNode5334, oldNode5333]
  rfl
theorem oldNode5336 (p : Pattern) : NetHack.Sokoban22Refined85.d5336 p = d253339 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5334 p) = d253339 p
  rw [oldNode12, oldNode5334]
  rfl
theorem oldNode5337 (p : Pattern) : NetHack.Sokoban22Refined85.d5337 p = d253340 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5336 p else NetHack.Sokoban22Refined85.d5335 p) = d253340 p
  rw [oldNode5336, oldNode5335]
  rfl
theorem oldNode5338 (p : Pattern) : NetHack.Sokoban22Refined85.d5338 p = d253341 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5336 p) = d253341 p
  rw [oldNode12, oldNode5336]
  rfl
theorem oldNode5339 (p : Pattern) : NetHack.Sokoban22Refined85.d5339 p = d253342 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5338 p else NetHack.Sokoban22Refined85.d5337 p) = d253342 p
  rw [oldNode5338, oldNode5337]
  rfl
theorem oldNode5340 (p : Pattern) : NetHack.Sokoban22Refined85.d5340 p = d253343 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5339 p else NetHack.Sokoban22Refined85.d5330 p) = d253343 p
  rw [oldNode5339, oldNode5330]
  rfl
theorem oldNode5341 (p : Pattern) : NetHack.Sokoban22Refined85.d5341 p = d253344 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5340 p else NetHack.Sokoban22Refined85.d5331 p) = d253344 p
  rw [oldNode5340, oldNode5331]
  rfl
theorem oldNode5342 (p : Pattern) : NetHack.Sokoban22Refined85.d5342 p = d253345 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5330 p) = d253345 p
  rw [oldNode12, oldNode5330]
  rfl
theorem oldNode5343 (p : Pattern) : NetHack.Sokoban22Refined85.d5343 p = d253346 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5342 p else NetHack.Sokoban22Refined85.d5331 p) = d253346 p
  rw [oldNode5342, oldNode5331]
  rfl
theorem oldNode5344 (p : Pattern) : NetHack.Sokoban22Refined85.d5344 p = d253347 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5343 p else NetHack.Sokoban22Refined85.d5341 p) = d253347 p
  rw [oldNode5343, oldNode5341]
  rfl
theorem oldNode5345 (p : Pattern) : NetHack.Sokoban22Refined85.d5345 p = d253348 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d102 p) = d253348 p
  rw [oldNode12, oldNode102]
  rfl
theorem oldNode5346 (p : Pattern) : NetHack.Sokoban22Refined85.d5346 p = d253349 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5345 p else NetHack.Sokoban22Refined85.d102 p) = d253349 p
  rw [oldNode5345, oldNode102]
  rfl
theorem oldNode5347 (p : Pattern) : NetHack.Sokoban22Refined85.d5347 p = d253350 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d106 p) = d253350 p
  rw [oldNode12, oldNode106]
  rfl
theorem oldNode5348 (p : Pattern) : NetHack.Sokoban22Refined85.d5348 p = d253351 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5347 p else NetHack.Sokoban22Refined85.d106 p) = d253351 p
  rw [oldNode5347, oldNode106]
  rfl
theorem oldNode5349 (p : Pattern) : NetHack.Sokoban22Refined85.d5349 p = d253352 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5348 p else NetHack.Sokoban22Refined85.d5346 p) = d253352 p
  rw [oldNode5348, oldNode5346]
  rfl
theorem oldNode5350 (p : Pattern) : NetHack.Sokoban22Refined85.d5350 p = d253353 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5349 p else NetHack.Sokoban22Refined85.d5346 p) = d253353 p
  rw [oldNode5349, oldNode5346]
  rfl
theorem oldNode5351 (p : Pattern) : NetHack.Sokoban22Refined85.d5351 p = d253354 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5303 p) = d253354 p
  rw [oldNode12, oldNode5303]
  rfl
theorem oldNode5352 (p : Pattern) : NetHack.Sokoban22Refined85.d5352 p = d253355 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5351 p else NetHack.Sokoban22Refined85.d5349 p) = d253355 p
  rw [oldNode5351, oldNode5349]
  rfl
theorem oldNode5353 (p : Pattern) : NetHack.Sokoban22Refined85.d5353 p = d253356 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5352 p else NetHack.Sokoban22Refined85.d5350 p) = d253356 p
  rw [oldNode5352, oldNode5350]
  rfl
theorem oldNode5354 (p : Pattern) : NetHack.Sokoban22Refined85.d5354 p = d253357 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d115 p) = d253357 p
  rw [oldNode12, oldNode115]
  rfl
theorem oldNode5355 (p : Pattern) : NetHack.Sokoban22Refined85.d5355 p = d253358 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5354 p else NetHack.Sokoban22Refined85.d102 p) = d253358 p
  rw [oldNode5354, oldNode102]
  rfl
theorem oldNode5356 (p : Pattern) : NetHack.Sokoban22Refined85.d5356 p = d253359 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d119 p) = d253359 p
  rw [oldNode12, oldNode119]
  rfl
theorem oldNode5357 (p : Pattern) : NetHack.Sokoban22Refined85.d5357 p = d253360 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5356 p else NetHack.Sokoban22Refined85.d102 p) = d253360 p
  rw [oldNode5356, oldNode102]
  rfl
theorem oldNode5358 (p : Pattern) : NetHack.Sokoban22Refined85.d5358 p = d253361 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5357 p else NetHack.Sokoban22Refined85.d5355 p) = d253361 p
  rw [oldNode5357, oldNode5355]
  rfl
theorem oldNode5359 (p : Pattern) : NetHack.Sokoban22Refined85.d5359 p = d253362 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d102 p) = d253362 p
  rw [oldNode12, oldNode102]
  rfl
theorem oldNode5360 (p : Pattern) : NetHack.Sokoban22Refined85.d5360 p = d253363 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d106 p) = d253363 p
  rw [oldNode12, oldNode106]
  rfl
theorem oldNode5361 (p : Pattern) : NetHack.Sokoban22Refined85.d5361 p = d253364 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5360 p else NetHack.Sokoban22Refined85.d5359 p) = d253364 p
  rw [oldNode5360, oldNode5359]
  rfl
theorem oldNode5362 (p : Pattern) : NetHack.Sokoban22Refined85.d5362 p = d253365 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5361 p else NetHack.Sokoban22Refined85.d5358 p) = d253365 p
  rw [oldNode5361, oldNode5358]
  rfl
theorem oldNode5363 (p : Pattern) : NetHack.Sokoban22Refined85.d5363 p = d253366 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5313 p) = d253366 p
  rw [oldNode12, oldNode5313]
  rfl
theorem oldNode5364 (p : Pattern) : NetHack.Sokoban22Refined85.d5364 p = d253367 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5363 p else NetHack.Sokoban22Refined85.d5361 p) = d253367 p
  rw [oldNode5363, oldNode5361]
  rfl
theorem oldNode5365 (p : Pattern) : NetHack.Sokoban22Refined85.d5365 p = d253368 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5364 p else NetHack.Sokoban22Refined85.d5362 p) = d253368 p
  rw [oldNode5364, oldNode5362]
  rfl
theorem oldNode5366 (p : Pattern) : NetHack.Sokoban22Refined85.d5366 p = d253369 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5365 p else NetHack.Sokoban22Refined85.d5353 p) = d253369 p
  rw [oldNode5365, oldNode5353]
  rfl
theorem oldNode5367 (p : Pattern) : NetHack.Sokoban22Refined85.d5367 p = d253370 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5354 p else NetHack.Sokoban22Refined85.d115 p) = d253370 p
  rw [oldNode5354, oldNode115]
  rfl
theorem oldNode5368 (p : Pattern) : NetHack.Sokoban22Refined85.d5368 p = d253371 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5367 p else NetHack.Sokoban22Refined85.d5346 p) = d253371 p
  rw [oldNode5367, oldNode5346]
  rfl
theorem oldNode5369 (p : Pattern) : NetHack.Sokoban22Refined85.d5369 p = d253372 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5303 p else NetHack.Sokoban22Refined85.d5348 p) = d253372 p
  rw [oldNode5303, oldNode5348]
  rfl
theorem oldNode5370 (p : Pattern) : NetHack.Sokoban22Refined85.d5370 p = d253373 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5369 p else NetHack.Sokoban22Refined85.d5368 p) = d253373 p
  rw [oldNode5369, oldNode5368]
  rfl
theorem oldNode5371 (p : Pattern) : NetHack.Sokoban22Refined85.d5371 p = d253374 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5305 p else NetHack.Sokoban22Refined85.d5348 p) = d253374 p
  rw [oldNode5305, oldNode5348]
  rfl
theorem oldNode5372 (p : Pattern) : NetHack.Sokoban22Refined85.d5372 p = d253375 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5371 p) = d253375 p
  rw [oldNode12, oldNode5371]
  rfl
theorem oldNode5373 (p : Pattern) : NetHack.Sokoban22Refined85.d5373 p = d253376 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5372 p else NetHack.Sokoban22Refined85.d5370 p) = d253376 p
  rw [oldNode5372, oldNode5370]
  rfl
theorem oldNode5374 (p : Pattern) : NetHack.Sokoban22Refined85.d5374 p = d253377 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d115 p) = d253377 p
  rw [oldNode12, oldNode115]
  rfl
theorem oldNode5375 (p : Pattern) : NetHack.Sokoban22Refined85.d5375 p = d253378 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5374 p else NetHack.Sokoban22Refined85.d5357 p) = d253378 p
  rw [oldNode5374, oldNode5357]
  rfl
theorem oldNode5376 (p : Pattern) : NetHack.Sokoban22Refined85.d5376 p = d253379 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5313 p else NetHack.Sokoban22Refined85.d5360 p) = d253379 p
  rw [oldNode5313, oldNode5360]
  rfl
theorem oldNode5377 (p : Pattern) : NetHack.Sokoban22Refined85.d5377 p = d253380 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5376 p else NetHack.Sokoban22Refined85.d5375 p) = d253380 p
  rw [oldNode5376, oldNode5375]
  rfl
theorem oldNode5378 (p : Pattern) : NetHack.Sokoban22Refined85.d5378 p = d253381 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5315 p else NetHack.Sokoban22Refined85.d5360 p) = d253381 p
  rw [oldNode5315, oldNode5360]
  rfl
theorem oldNode5379 (p : Pattern) : NetHack.Sokoban22Refined85.d5379 p = d253382 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5378 p) = d253382 p
  rw [oldNode12, oldNode5378]
  rfl
theorem oldNode5380 (p : Pattern) : NetHack.Sokoban22Refined85.d5380 p = d253383 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5379 p else NetHack.Sokoban22Refined85.d5377 p) = d253383 p
  rw [oldNode5379, oldNode5377]
  rfl
theorem oldNode5381 (p : Pattern) : NetHack.Sokoban22Refined85.d5381 p = d253384 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5380 p else NetHack.Sokoban22Refined85.d5373 p) = d253384 p
  rw [oldNode5380, oldNode5373]
  rfl
theorem oldNode5382 (p : Pattern) : NetHack.Sokoban22Refined85.d5382 p = d253385 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5381 p else NetHack.Sokoban22Refined85.d5366 p) = d253385 p
  rw [oldNode5381, oldNode5366]
  rfl
theorem oldNode5383 (p : Pattern) : NetHack.Sokoban22Refined85.d5383 p = d253386 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5356 p else NetHack.Sokoban22Refined85.d119 p) = d253386 p
  rw [oldNode5356, oldNode119]
  rfl
theorem oldNode5384 (p : Pattern) : NetHack.Sokoban22Refined85.d5384 p = d253387 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5383 p else NetHack.Sokoban22Refined85.d5367 p) = d253387 p
  rw [oldNode5383, oldNode5367]
  rfl
theorem oldNode5385 (p : Pattern) : NetHack.Sokoban22Refined85.d5385 p = d253388 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5384 p) = d253388 p
  rw [oldNode12, oldNode5384]
  rfl
theorem oldNode5386 (p : Pattern) : NetHack.Sokoban22Refined85.d5386 p = d253389 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5385 p) = d253389 p
  rw [oldNode12, oldNode5385]
  rfl
theorem oldNode5387 (p : Pattern) : NetHack.Sokoban22Refined85.d5387 p = d253390 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5386 p else NetHack.Sokoban22Refined85.d5353 p) = d253390 p
  rw [oldNode5386, oldNode5353]
  rfl
theorem oldNode5388 (p : Pattern) : NetHack.Sokoban22Refined85.d5388 p = d253391 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5383 p) = d253391 p
  rw [oldNode12, oldNode5383]
  rfl
theorem oldNode5389 (p : Pattern) : NetHack.Sokoban22Refined85.d5389 p = d253392 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5388 p) = d253392 p
  rw [oldNode12, oldNode5388]
  rfl
theorem oldNode5390 (p : Pattern) : NetHack.Sokoban22Refined85.d5390 p = d253393 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5389 p) = d253393 p
  rw [oldNode12, oldNode5389]
  rfl
theorem oldNode5391 (p : Pattern) : NetHack.Sokoban22Refined85.d5391 p = d253394 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5390 p else NetHack.Sokoban22Refined85.d5373 p) = d253394 p
  rw [oldNode5390, oldNode5373]
  rfl
theorem oldNode5392 (p : Pattern) : NetHack.Sokoban22Refined85.d5392 p = d253395 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5391 p else NetHack.Sokoban22Refined85.d5387 p) = d253395 p
  rw [oldNode5391, oldNode5387]
  rfl
theorem oldNode5393 (p : Pattern) : NetHack.Sokoban22Refined85.d5393 p = d253396 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5392 p else NetHack.Sokoban22Refined85.d5382 p) = d253396 p
  rw [oldNode5392, oldNode5382]
  rfl
theorem oldNode5394 (p : Pattern) : NetHack.Sokoban22Refined85.d5394 p = d253397 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5351 p) = d253397 p
  rw [oldNode12, oldNode5351]
  rfl
theorem oldNode5395 (p : Pattern) : NetHack.Sokoban22Refined85.d5395 p = d253398 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5394 p) = d253398 p
  rw [oldNode12, oldNode5394]
  rfl
theorem oldNode5396 (p : Pattern) : NetHack.Sokoban22Refined85.d5396 p = d253399 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5395 p) = d253399 p
  rw [oldNode12, oldNode5395]
  rfl
theorem oldNode5397 (p : Pattern) : NetHack.Sokoban22Refined85.d5397 p = d253400 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5396 p) = d253400 p
  rw [oldNode12, oldNode5396]
  rfl
theorem oldNode5398 (p : Pattern) : NetHack.Sokoban22Refined85.d5398 p = d253401 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5397 p else NetHack.Sokoban22Refined85.d5392 p) = d253401 p
  rw [oldNode5397, oldNode5392]
  rfl
theorem oldNode5399 (p : Pattern) : NetHack.Sokoban22Refined85.d5399 p = d253402 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5398 p else NetHack.Sokoban22Refined85.d5393 p) = d253402 p
  rw [oldNode5398, oldNode5393]
  rfl
theorem oldNode5400 (p : Pattern) : NetHack.Sokoban22Refined85.d5400 p = d253403 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5392 p) = d253403 p
  rw [oldNode12, oldNode5392]
  rfl
theorem oldNode5401 (p : Pattern) : NetHack.Sokoban22Refined85.d5401 p = d253404 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5400 p else NetHack.Sokoban22Refined85.d5393 p) = d253404 p
  rw [oldNode5400, oldNode5393]
  rfl
theorem oldNode5402 (p : Pattern) : NetHack.Sokoban22Refined85.d5402 p = d253405 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5401 p else NetHack.Sokoban22Refined85.d5399 p) = d253405 p
  rw [oldNode5401, oldNode5399]
  rfl
theorem oldNode5403 (p : Pattern) : NetHack.Sokoban22Refined85.d5403 p = d253406 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5402 p else NetHack.Sokoban22Refined85.d5344 p) = d253406 p
  rw [oldNode5402, oldNode5344]
  rfl
theorem oldNode5404 (p : Pattern) : NetHack.Sokoban22Refined85.d5404 p = d253407 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d5403 p else NetHack.Sokoban22Refined85.d5344 p) = d253407 p
  rw [oldNode5403, oldNode5344]
  rfl
theorem oldNode5405 (p : Pattern) : NetHack.Sokoban22Refined85.d5405 p = d253408 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5283 p else NetHack.Sokoban22Refined85.d30 p) = d253408 p
  rw [oldNode5283, oldNode30]
  rfl
theorem oldNode5406 (p : Pattern) : NetHack.Sokoban22Refined85.d5406 p = d253409 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5405 p else NetHack.Sokoban22Refined85.d5298 p) = d253409 p
  rw [oldNode5405, oldNode5298]
  rfl
theorem oldNode5407 (p : Pattern) : NetHack.Sokoban22Refined85.d5407 p = d253410 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5286 p else NetHack.Sokoban22Refined85.d30 p) = d253410 p
  rw [oldNode5286, oldNode30]
  rfl
theorem oldNode5408 (p : Pattern) : NetHack.Sokoban22Refined85.d5408 p = d253411 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d34 p) = d253411 p
  rw [oldNode12, oldNode34]
  rfl
theorem oldNode5409 (p : Pattern) : NetHack.Sokoban22Refined85.d5409 p = d253412 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5408 p else NetHack.Sokoban22Refined85.d5407 p) = d253412 p
  rw [oldNode5408, oldNode5407]
  rfl
theorem oldNode5410 (p : Pattern) : NetHack.Sokoban22Refined85.d5410 p = d253413 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5409 p else NetHack.Sokoban22Refined85.d5406 p) = d253413 p
  rw [oldNode5409, oldNode5406]
  rfl
theorem oldNode5411 (p : Pattern) : NetHack.Sokoban22Refined85.d5411 p = d253414 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5408 p else NetHack.Sokoban22Refined85.d5309 p) = d253414 p
  rw [oldNode5408, oldNode5309]
  rfl
theorem oldNode5412 (p : Pattern) : NetHack.Sokoban22Refined85.d5412 p = d253415 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5316 p else NetHack.Sokoban22Refined85.d5411 p) = d253415 p
  rw [oldNode5316, oldNode5411]
  rfl
theorem oldNode5413 (p : Pattern) : NetHack.Sokoban22Refined85.d5413 p = d253416 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5412 p else NetHack.Sokoban22Refined85.d5410 p) = d253416 p
  rw [oldNode5412, oldNode5410]
  rfl
theorem oldNode5414 (p : Pattern) : NetHack.Sokoban22Refined85.d5414 p = d253417 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5413 p else NetHack.Sokoban22Refined85.d5280 p) = d253417 p
  rw [oldNode5413, oldNode5280]
  rfl
theorem oldNode5415 (p : Pattern) : NetHack.Sokoban22Refined85.d5415 p = d253418 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5288 p else NetHack.Sokoban22Refined85.d5405 p) = d253418 p
  rw [oldNode5288, oldNode5405]
  rfl
theorem oldNode5416 (p : Pattern) : NetHack.Sokoban22Refined85.d5416 p = d253419 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5315 p else NetHack.Sokoban22Refined85.d5408 p) = d253419 p
  rw [oldNode5315, oldNode5408]
  rfl
theorem oldNode5417 (p : Pattern) : NetHack.Sokoban22Refined85.d5417 p = d253420 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5416 p else NetHack.Sokoban22Refined85.d5415 p) = d253420 p
  rw [oldNode5416, oldNode5415]
  rfl
theorem oldNode5418 (p : Pattern) : NetHack.Sokoban22Refined85.d5418 p = d253421 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5408 p) = d253421 p
  rw [oldNode12, oldNode5408]
  rfl
theorem oldNode5419 (p : Pattern) : NetHack.Sokoban22Refined85.d5419 p = d253422 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5418 p) = d253422 p
  rw [oldNode12, oldNode5418]
  rfl
theorem oldNode5420 (p : Pattern) : NetHack.Sokoban22Refined85.d5420 p = d253423 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5419 p else NetHack.Sokoban22Refined85.d5417 p) = d253423 p
  rw [oldNode5419, oldNode5417]
  rfl
theorem oldNode5421 (p : Pattern) : NetHack.Sokoban22Refined85.d5421 p = d253424 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5420 p else NetHack.Sokoban22Refined85.d5308 p) = d253424 p
  rw [oldNode5420, oldNode5308]
  rfl
theorem oldNode5422 (p : Pattern) : NetHack.Sokoban22Refined85.d5422 p = d253425 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5421 p else NetHack.Sokoban22Refined85.d5414 p) = d253425 p
  rw [oldNode5421, oldNode5414]
  rfl
theorem oldNode5423 (p : Pattern) : NetHack.Sokoban22Refined85.d5423 p = d253426 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5322 p else NetHack.Sokoban22Refined85.d5271 p) = d253426 p
  rw [oldNode5322, oldNode5271]
  rfl
theorem oldNode5424 (p : Pattern) : NetHack.Sokoban22Refined85.d5424 p = d253427 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5323 p else NetHack.Sokoban22Refined85.d5423 p) = d253427 p
  rw [oldNode5323, oldNode5423]
  rfl
theorem oldNode5425 (p : Pattern) : NetHack.Sokoban22Refined85.d5425 p = d253428 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d190 p) = d253428 p
  rw [oldNode12, oldNode190]
  rfl
theorem oldNode5426 (p : Pattern) : NetHack.Sokoban22Refined85.d5426 p = d253429 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5425 p else NetHack.Sokoban22Refined85.d190 p) = d253429 p
  rw [oldNode5425, oldNode190]
  rfl
theorem oldNode5427 (p : Pattern) : NetHack.Sokoban22Refined85.d5427 p = d253430 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5426 p else NetHack.Sokoban22Refined85.d5273 p) = d253430 p
  rw [oldNode5426, oldNode5273]
  rfl
theorem oldNode5428 (p : Pattern) : NetHack.Sokoban22Refined85.d5428 p = d253431 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5427 p) = d253431 p
  rw [oldNode12, oldNode5427]
  rfl
theorem oldNode5429 (p : Pattern) : NetHack.Sokoban22Refined85.d5429 p = d253432 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5428 p) = d253432 p
  rw [oldNode12, oldNode5428]
  rfl
theorem oldNode5430 (p : Pattern) : NetHack.Sokoban22Refined85.d5430 p = d253433 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5429 p else NetHack.Sokoban22Refined85.d5424 p) = d253433 p
  rw [oldNode5429, oldNode5424]
  rfl
theorem oldNode5431 (p : Pattern) : NetHack.Sokoban22Refined85.d5431 p = d253434 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5305 p else NetHack.Sokoban22Refined85.d5273 p) = d253434 p
  rw [oldNode5305, oldNode5273]
  rfl
theorem oldNode5432 (p : Pattern) : NetHack.Sokoban22Refined85.d5432 p = d253435 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5431 p else NetHack.Sokoban22Refined85.d5298 p) = d253435 p
  rw [oldNode5431, oldNode5298]
  rfl
theorem oldNode5433 (p : Pattern) : NetHack.Sokoban22Refined85.d5433 p = d253436 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5327 p else NetHack.Sokoban22Refined85.d5432 p) = d253436 p
  rw [oldNode5327, oldNode5432]
  rfl
theorem oldNode5434 (p : Pattern) : NetHack.Sokoban22Refined85.d5434 p = d253437 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5426 p) = d253437 p
  rw [oldNode12, oldNode5426]
  rfl
theorem oldNode5435 (p : Pattern) : NetHack.Sokoban22Refined85.d5435 p = d253438 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5434 p) = d253438 p
  rw [oldNode12, oldNode5434]
  rfl
theorem oldNode5436 (p : Pattern) : NetHack.Sokoban22Refined85.d5436 p = d253439 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5435 p) = d253439 p
  rw [oldNode12, oldNode5435]
  rfl
theorem oldNode5437 (p : Pattern) : NetHack.Sokoban22Refined85.d5437 p = d253440 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5436 p else NetHack.Sokoban22Refined85.d5433 p) = d253440 p
  rw [oldNode5436, oldNode5433]
  rfl
theorem oldNode5438 (p : Pattern) : NetHack.Sokoban22Refined85.d5438 p = d253441 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5437 p else NetHack.Sokoban22Refined85.d5430 p) = d253441 p
  rw [oldNode5437, oldNode5430]
  rfl
theorem oldNode5439 (p : Pattern) : NetHack.Sokoban22Refined85.d5439 p = d253442 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5438 p else NetHack.Sokoban22Refined85.d5422 p) = d253442 p
  rw [oldNode5438, oldNode5422]
  rfl
theorem oldNode5440 (p : Pattern) : NetHack.Sokoban22Refined85.d5440 p = d253443 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5438 p) = d253443 p
  rw [oldNode12, oldNode5438]
  rfl
theorem oldNode5441 (p : Pattern) : NetHack.Sokoban22Refined85.d5441 p = d253444 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5440 p else NetHack.Sokoban22Refined85.d5439 p) = d253444 p
  rw [oldNode5440, oldNode5439]
  rfl
theorem oldNode5442 (p : Pattern) : NetHack.Sokoban22Refined85.d5442 p = d253445 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5441 p else NetHack.Sokoban22Refined85.d5341 p) = d253445 p
  rw [oldNode5441, oldNode5341]
  rfl
theorem oldNode5443 (p : Pattern) : NetHack.Sokoban22Refined85.d5443 p = d253446 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5442 p else NetHack.Sokoban22Refined85.d5344 p) = d253446 p
  rw [oldNode5442, oldNode5344]
  rfl
theorem oldNode5444 (p : Pattern) : NetHack.Sokoban22Refined85.d5444 p = d253447 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5348 p) = d253447 p
  rw [oldNode12, oldNode5348]
  rfl
theorem oldNode5445 (p : Pattern) : NetHack.Sokoban22Refined85.d5445 p = d253448 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5444 p else NetHack.Sokoban22Refined85.d5368 p) = d253448 p
  rw [oldNode5444, oldNode5368]
  rfl
theorem oldNode5446 (p : Pattern) : NetHack.Sokoban22Refined85.d5446 p = d253449 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5444 p) = d253449 p
  rw [oldNode12, oldNode5444]
  rfl
theorem oldNode5447 (p : Pattern) : NetHack.Sokoban22Refined85.d5447 p = d253450 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5446 p else NetHack.Sokoban22Refined85.d5445 p) = d253450 p
  rw [oldNode5446, oldNode5445]
  rfl
theorem oldNode5448 (p : Pattern) : NetHack.Sokoban22Refined85.d5448 p = d253451 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5360 p) = d253451 p
  rw [oldNode12, oldNode5360]
  rfl
theorem oldNode5449 (p : Pattern) : NetHack.Sokoban22Refined85.d5449 p = d253452 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5448 p else NetHack.Sokoban22Refined85.d5375 p) = d253452 p
  rw [oldNode5448, oldNode5375]
  rfl
theorem oldNode5450 (p : Pattern) : NetHack.Sokoban22Refined85.d5450 p = d253453 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5448 p) = d253453 p
  rw [oldNode12, oldNode5448]
  rfl
theorem oldNode5451 (p : Pattern) : NetHack.Sokoban22Refined85.d5451 p = d253454 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5450 p else NetHack.Sokoban22Refined85.d5449 p) = d253454 p
  rw [oldNode5450, oldNode5449]
  rfl
theorem oldNode5452 (p : Pattern) : NetHack.Sokoban22Refined85.d5452 p = d253455 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5451 p else NetHack.Sokoban22Refined85.d5447 p) = d253455 p
  rw [oldNode5451, oldNode5447]
  rfl
theorem oldNode5453 (p : Pattern) : NetHack.Sokoban22Refined85.d5453 p = d253456 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5452 p else NetHack.Sokoban22Refined85.d5366 p) = d253456 p
  rw [oldNode5452, oldNode5366]
  rfl
theorem oldNode5454 (p : Pattern) : NetHack.Sokoban22Refined85.d5454 p = d253457 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5390 p else NetHack.Sokoban22Refined85.d5447 p) = d253457 p
  rw [oldNode5390, oldNode5447]
  rfl
theorem oldNode5455 (p : Pattern) : NetHack.Sokoban22Refined85.d5455 p = d253458 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5454 p else NetHack.Sokoban22Refined85.d5387 p) = d253458 p
  rw [oldNode5454, oldNode5387]
  rfl
theorem oldNode5456 (p : Pattern) : NetHack.Sokoban22Refined85.d5456 p = d253459 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5455 p else NetHack.Sokoban22Refined85.d5453 p) = d253459 p
  rw [oldNode5455, oldNode5453]
  rfl
theorem oldNode5457 (p : Pattern) : NetHack.Sokoban22Refined85.d5457 p = d253460 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5397 p else NetHack.Sokoban22Refined85.d5455 p) = d253460 p
  rw [oldNode5397, oldNode5455]
  rfl
theorem oldNode5458 (p : Pattern) : NetHack.Sokoban22Refined85.d5458 p = d253461 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5457 p else NetHack.Sokoban22Refined85.d5456 p) = d253461 p
  rw [oldNode5457, oldNode5456]
  rfl
theorem oldNode5459 (p : Pattern) : NetHack.Sokoban22Refined85.d5459 p = d253462 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5356 p else NetHack.Sokoban22Refined85.d115 p) = d253462 p
  rw [oldNode5356, oldNode115]
  rfl
theorem oldNode5460 (p : Pattern) : NetHack.Sokoban22Refined85.d5460 p = d253463 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5459 p else NetHack.Sokoban22Refined85.d5367 p) = d253463 p
  rw [oldNode5459, oldNode5367]
  rfl
theorem oldNode5461 (p : Pattern) : NetHack.Sokoban22Refined85.d5461 p = d253464 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5448 p else NetHack.Sokoban22Refined85.d5460 p) = d253464 p
  rw [oldNode5448, oldNode5460]
  rfl
theorem oldNode5462 (p : Pattern) : NetHack.Sokoban22Refined85.d5462 p = d253465 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d119 p) = d253465 p
  rw [oldNode12, oldNode119]
  rfl
theorem oldNode5463 (p : Pattern) : NetHack.Sokoban22Refined85.d5463 p = d253466 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5462 p) = d253466 p
  rw [oldNode12, oldNode5462]
  rfl
theorem oldNode5464 (p : Pattern) : NetHack.Sokoban22Refined85.d5464 p = d253467 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5463 p) = d253467 p
  rw [oldNode12, oldNode5463]
  rfl
theorem oldNode5465 (p : Pattern) : NetHack.Sokoban22Refined85.d5465 p = d253468 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5464 p else NetHack.Sokoban22Refined85.d5461 p) = d253468 p
  rw [oldNode5464, oldNode5461]
  rfl
theorem oldNode5466 (p : Pattern) : NetHack.Sokoban22Refined85.d5466 p = d253469 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5465 p else NetHack.Sokoban22Refined85.d5353 p) = d253469 p
  rw [oldNode5465, oldNode5353]
  rfl
theorem oldNode5467 (p : Pattern) : NetHack.Sokoban22Refined85.d5467 p = d253470 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5356 p else NetHack.Sokoban22Refined85.d106 p) = d253470 p
  rw [oldNode5356, oldNode106]
  rfl
theorem oldNode5468 (p : Pattern) : NetHack.Sokoban22Refined85.d5468 p = d253471 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5360 p else NetHack.Sokoban22Refined85.d5467 p) = d253471 p
  rw [oldNode5360, oldNode5467]
  rfl
theorem oldNode5469 (p : Pattern) : NetHack.Sokoban22Refined85.d5469 p = d253472 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5463 p else NetHack.Sokoban22Refined85.d5468 p) = d253472 p
  rw [oldNode5463, oldNode5468]
  rfl
theorem oldNode5470 (p : Pattern) : NetHack.Sokoban22Refined85.d5470 p = d253473 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5294 p) = d253473 p
  rw [oldNode12, oldNode5294]
  rfl
theorem oldNode5471 (p : Pattern) : NetHack.Sokoban22Refined85.d5471 p = d253474 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5470 p else NetHack.Sokoban22Refined85.d5469 p) = d253474 p
  rw [oldNode5470, oldNode5469]
  rfl
theorem oldNode5472 (p : Pattern) : NetHack.Sokoban22Refined85.d5472 p = d253475 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5471 p else NetHack.Sokoban22Refined85.d5447 p) = d253475 p
  rw [oldNode5471, oldNode5447]
  rfl
theorem oldNode5473 (p : Pattern) : NetHack.Sokoban22Refined85.d5473 p = d253476 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5472 p else NetHack.Sokoban22Refined85.d5466 p) = d253476 p
  rw [oldNode5472, oldNode5466]
  rfl
theorem oldNode5474 (p : Pattern) : NetHack.Sokoban22Refined85.d5474 p = d253477 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5305 p else NetHack.Sokoban22Refined85.d5367 p) = d253477 p
  rw [oldNode5305, oldNode5367]
  rfl
theorem oldNode5475 (p : Pattern) : NetHack.Sokoban22Refined85.d5475 p = d253478 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5474 p else NetHack.Sokoban22Refined85.d5346 p) = d253478 p
  rw [oldNode5474, oldNode5346]
  rfl
theorem oldNode5476 (p : Pattern) : NetHack.Sokoban22Refined85.d5476 p = d253479 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5372 p else NetHack.Sokoban22Refined85.d5475 p) = d253479 p
  rw [oldNode5372, oldNode5475]
  rfl
theorem oldNode5477 (p : Pattern) : NetHack.Sokoban22Refined85.d5477 p = d253480 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5390 p else NetHack.Sokoban22Refined85.d5476 p) = d253480 p
  rw [oldNode5390, oldNode5476]
  rfl
theorem oldNode5478 (p : Pattern) : NetHack.Sokoban22Refined85.d5478 p = d253481 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5444 p else NetHack.Sokoban22Refined85.d5367 p) = d253481 p
  rw [oldNode5444, oldNode5367]
  rfl
theorem oldNode5479 (p : Pattern) : NetHack.Sokoban22Refined85.d5479 p = d253482 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5389 p else NetHack.Sokoban22Refined85.d5478 p) = d253482 p
  rw [oldNode5389, oldNode5478]
  rfl
theorem oldNode5480 (p : Pattern) : NetHack.Sokoban22Refined85.d5480 p = d253483 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5278 p) = d253483 p
  rw [oldNode12, oldNode5278]
  rfl
theorem oldNode5481 (p : Pattern) : NetHack.Sokoban22Refined85.d5481 p = d253484 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5480 p) = d253484 p
  rw [oldNode12, oldNode5480]
  rfl
theorem oldNode5482 (p : Pattern) : NetHack.Sokoban22Refined85.d5482 p = d253485 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5481 p else NetHack.Sokoban22Refined85.d5479 p) = d253485 p
  rw [oldNode5481, oldNode5479]
  rfl
theorem oldNode5483 (p : Pattern) : NetHack.Sokoban22Refined85.d5483 p = d253486 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5482 p else NetHack.Sokoban22Refined85.d5477 p) = d253486 p
  rw [oldNode5482, oldNode5477]
  rfl
theorem oldNode5484 (p : Pattern) : NetHack.Sokoban22Refined85.d5484 p = d253487 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5483 p else NetHack.Sokoban22Refined85.d5473 p) = d253487 p
  rw [oldNode5483, oldNode5473]
  rfl
theorem oldNode5485 (p : Pattern) : NetHack.Sokoban22Refined85.d5485 p = d253488 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5277 p else NetHack.Sokoban22Refined85.d5367 p) = d253488 p
  rw [oldNode5277, oldNode5367]
  rfl
theorem oldNode5486 (p : Pattern) : NetHack.Sokoban22Refined85.d5486 p = d253489 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5485 p else NetHack.Sokoban22Refined85.d5346 p) = d253489 p
  rw [oldNode5485, oldNode5346]
  rfl
theorem oldNode5487 (p : Pattern) : NetHack.Sokoban22Refined85.d5487 p = d253490 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5277 p else NetHack.Sokoban22Refined85.d5348 p) = d253490 p
  rw [oldNode5277, oldNode5348]
  rfl
theorem oldNode5488 (p : Pattern) : NetHack.Sokoban22Refined85.d5488 p = d253491 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5487 p) = d253491 p
  rw [oldNode12, oldNode5487]
  rfl
theorem oldNode5489 (p : Pattern) : NetHack.Sokoban22Refined85.d5489 p = d253492 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5488 p else NetHack.Sokoban22Refined85.d5486 p) = d253492 p
  rw [oldNode5488, oldNode5486]
  rfl
theorem oldNode5490 (p : Pattern) : NetHack.Sokoban22Refined85.d5490 p = d253493 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5305 p else NetHack.Sokoban22Refined85.d5383 p) = d253493 p
  rw [oldNode5305, oldNode5383]
  rfl
theorem oldNode5491 (p : Pattern) : NetHack.Sokoban22Refined85.d5491 p = d253494 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5490 p) = d253494 p
  rw [oldNode12, oldNode5490]
  rfl
theorem oldNode5492 (p : Pattern) : NetHack.Sokoban22Refined85.d5492 p = d253495 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5491 p) = d253495 p
  rw [oldNode12, oldNode5491]
  rfl
theorem oldNode5493 (p : Pattern) : NetHack.Sokoban22Refined85.d5493 p = d253496 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5492 p else NetHack.Sokoban22Refined85.d5489 p) = d253496 p
  rw [oldNode5492, oldNode5489]
  rfl
theorem oldNode5494 (p : Pattern) : NetHack.Sokoban22Refined85.d5494 p = d253497 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5482 p else NetHack.Sokoban22Refined85.d5493 p) = d253497 p
  rw [oldNode5482, oldNode5493]
  rfl
theorem oldNode5495 (p : Pattern) : NetHack.Sokoban22Refined85.d5495 p = d253498 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5494 p) = d253498 p
  rw [oldNode12, oldNode5494]
  rfl
theorem oldNode5496 (p : Pattern) : NetHack.Sokoban22Refined85.d5496 p = d253499 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5495 p else NetHack.Sokoban22Refined85.d5484 p) = d253499 p
  rw [oldNode5495, oldNode5484]
  rfl
theorem oldNode5497 (p : Pattern) : NetHack.Sokoban22Refined85.d5497 p = d253500 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5496 p else NetHack.Sokoban22Refined85.d5458 p) = d253500 p
  rw [oldNode5496, oldNode5458]
  rfl
theorem oldNode5498 (p : Pattern) : NetHack.Sokoban22Refined85.d5498 p = d253501 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5497 p else NetHack.Sokoban22Refined85.d5344 p) = d253501 p
  rw [oldNode5497, oldNode5344]
  rfl
theorem oldNode5499 (p : Pattern) : NetHack.Sokoban22Refined85.d5499 p = d253502 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d5498 p else NetHack.Sokoban22Refined85.d5443 p) = d253502 p
  rw [oldNode5498, oldNode5443]
  rfl
theorem oldNode5500 (p : Pattern) : NetHack.Sokoban22Refined85.d5500 p = d253503 p := by
  change (if p 48 then NetHack.Sokoban22Refined85.d5499 p else NetHack.Sokoban22Refined85.d5404 p) = d253503 p
  rw [oldNode5499, oldNode5404]
  rfl
theorem oldNode5504 (p : Pattern) : NetHack.Sokoban22Refined85.d5504 p = d267811 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4496 p else NetHack.Sokoban22Refined85.d4492 p) = d267811 p
  rw [oldNode4496, oldNode4492]
  rfl
theorem oldNode5505 (p : Pattern) : NetHack.Sokoban22Refined85.d5505 p = d267812 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5504 p else NetHack.Sokoban22Refined85.d4489 p) = d267812 p
  rw [oldNode5504, oldNode4489]
  rfl
theorem oldNode5506 (p : Pattern) : NetHack.Sokoban22Refined85.d5506 p = d267813 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d4504 p) = d267813 p
  rw [oldNode12, oldNode4504]
  rfl
theorem oldNode5507 (p : Pattern) : NetHack.Sokoban22Refined85.d5507 p = d267814 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5506 p else NetHack.Sokoban22Refined85.d5504 p) = d267814 p
  rw [oldNode5506, oldNode5504]
  rfl
theorem oldNode5508 (p : Pattern) : NetHack.Sokoban22Refined85.d5508 p = d267815 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5507 p else NetHack.Sokoban22Refined85.d5505 p) = d267815 p
  rw [oldNode5507, oldNode5505]
  rfl
theorem oldNode5509 (p : Pattern) : NetHack.Sokoban22Refined85.d5509 p = d267816 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5504 p) = d267816 p
  rw [oldNode12, oldNode5504]
  rfl
theorem oldNode5510 (p : Pattern) : NetHack.Sokoban22Refined85.d5510 p = d267817 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5509 p else NetHack.Sokoban22Refined85.d5505 p) = d267817 p
  rw [oldNode5509, oldNode5505]
  rfl
theorem oldNode5511 (p : Pattern) : NetHack.Sokoban22Refined85.d5511 p = d267818 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5510 p else NetHack.Sokoban22Refined85.d5508 p) = d267818 p
  rw [oldNode5510, oldNode5508]
  rfl
theorem oldNode5512 (p : Pattern) : NetHack.Sokoban22Refined85.d5512 p = d267819 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4531 p else NetHack.Sokoban22Refined85.d4527 p) = d267819 p
  rw [oldNode4531, oldNode4527]
  rfl
theorem oldNode5513 (p : Pattern) : NetHack.Sokoban22Refined85.d5513 p = d267820 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5512 p else NetHack.Sokoban22Refined85.d4524 p) = d267820 p
  rw [oldNode5512, oldNode4524]
  rfl
theorem oldNode5514 (p : Pattern) : NetHack.Sokoban22Refined85.d5514 p = d267821 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5512 p) = d267821 p
  rw [oldNode12, oldNode5512]
  rfl
theorem oldNode5515 (p : Pattern) : NetHack.Sokoban22Refined85.d5515 p = d267822 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5514 p else NetHack.Sokoban22Refined85.d5513 p) = d267822 p
  rw [oldNode5514, oldNode5513]
  rfl
theorem oldNode5516 (p : Pattern) : NetHack.Sokoban22Refined85.d5516 p = d267823 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5515 p else NetHack.Sokoban22Refined85.d5511 p) = d267823 p
  rw [oldNode5515, oldNode5511]
  rfl
theorem oldNode5517 (p : Pattern) : NetHack.Sokoban22Refined85.d5517 p = d267824 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d5516 p else NetHack.Sokoban22Refined85.d5511 p) = d267824 p
  rw [oldNode5516, oldNode5511]
  rfl
theorem oldNode5518 (p : Pattern) : NetHack.Sokoban22Refined85.d5518 p = d267825 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4552 p else NetHack.Sokoban22Refined85.d4547 p) = d267825 p
  rw [oldNode4552, oldNode4547]
  rfl
theorem oldNode5519 (p : Pattern) : NetHack.Sokoban22Refined85.d5519 p = d267826 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4566 p else NetHack.Sokoban22Refined85.d4559 p) = d267826 p
  rw [oldNode4566, oldNode4559]
  rfl
theorem oldNode5520 (p : Pattern) : NetHack.Sokoban22Refined85.d5520 p = d267827 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5519 p else NetHack.Sokoban22Refined85.d5518 p) = d267827 p
  rw [oldNode5519, oldNode5518]
  rfl
theorem oldNode5521 (p : Pattern) : NetHack.Sokoban22Refined85.d5521 p = d267828 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5519 p) = d267828 p
  rw [oldNode12, oldNode5519]
  rfl
theorem oldNode5522 (p : Pattern) : NetHack.Sokoban22Refined85.d5522 p = d267829 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5521 p else NetHack.Sokoban22Refined85.d5520 p) = d267829 p
  rw [oldNode5521, oldNode5520]
  rfl
theorem oldNode5523 (p : Pattern) : NetHack.Sokoban22Refined85.d5523 p = d267830 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5522 p else NetHack.Sokoban22Refined85.d5508 p) = d267830 p
  rw [oldNode5522, oldNode5508]
  rfl
theorem oldNode5524 (p : Pattern) : NetHack.Sokoban22Refined85.d5524 p = d267831 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5523 p else NetHack.Sokoban22Refined85.d5511 p) = d267831 p
  rw [oldNode5523, oldNode5511]
  rfl
theorem oldNode5525 (p : Pattern) : NetHack.Sokoban22Refined85.d5525 p = d267832 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5512 p else NetHack.Sokoban22Refined85.d4578 p) = d267832 p
  rw [oldNode5512, oldNode4578]
  rfl
theorem oldNode5526 (p : Pattern) : NetHack.Sokoban22Refined85.d5526 p = d267833 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5514 p else NetHack.Sokoban22Refined85.d5525 p) = d267833 p
  rw [oldNode5514, oldNode5525]
  rfl
theorem oldNode5527 (p : Pattern) : NetHack.Sokoban22Refined85.d5527 p = d267834 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4589 p else NetHack.Sokoban22Refined85.d4585 p) = d267834 p
  rw [oldNode4589, oldNode4585]
  rfl
theorem oldNode5528 (p : Pattern) : NetHack.Sokoban22Refined85.d5528 p = d267835 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4596 p else NetHack.Sokoban22Refined85.d4531 p) = d267835 p
  rw [oldNode4596, oldNode4531]
  rfl
theorem oldNode5529 (p : Pattern) : NetHack.Sokoban22Refined85.d5529 p = d267836 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5528 p else NetHack.Sokoban22Refined85.d5527 p) = d267836 p
  rw [oldNode5528, oldNode5527]
  rfl
theorem oldNode5530 (p : Pattern) : NetHack.Sokoban22Refined85.d5530 p = d267837 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d4596 p else NetHack.Sokoban22Refined85.d4607 p) = d267837 p
  rw [oldNode4596, oldNode4607]
  rfl
theorem oldNode5531 (p : Pattern) : NetHack.Sokoban22Refined85.d5531 p = d267838 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5530 p) = d267838 p
  rw [oldNode12, oldNode5530]
  rfl
theorem oldNode5532 (p : Pattern) : NetHack.Sokoban22Refined85.d5532 p = d267839 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5531 p else NetHack.Sokoban22Refined85.d5529 p) = d267839 p
  rw [oldNode5531, oldNode5529]
  rfl
theorem oldNode5533 (p : Pattern) : NetHack.Sokoban22Refined85.d5533 p = d267840 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5532 p else NetHack.Sokoban22Refined85.d5526 p) = d267840 p
  rw [oldNode5532, oldNode5526]
  rfl
theorem oldNode5534 (p : Pattern) : NetHack.Sokoban22Refined85.d5534 p = d267841 p := by
  change (if p 71 then NetHack.Sokoban22Refined85.d5533 p else NetHack.Sokoban22Refined85.d5511 p) = d267841 p
  rw [oldNode5533, oldNode5511]
  rfl
theorem oldNode5535 (p : Pattern) : NetHack.Sokoban22Refined85.d5535 p = d267842 p := by
  change (if p 49 then NetHack.Sokoban22Refined85.d5534 p else NetHack.Sokoban22Refined85.d5524 p) = d267842 p
  rw [oldNode5534, oldNode5524]
  rfl
theorem oldNode5536 (p : Pattern) : NetHack.Sokoban22Refined85.d5536 p = d267843 p := by
  change (if p 48 then NetHack.Sokoban22Refined85.d5535 p else NetHack.Sokoban22Refined85.d5517 p) = d267843 p
  rw [oldNode5535, oldNode5517]
  rfl
theorem oldNode5541 (p : Pattern) : NetHack.Sokoban22Refined85.d5541 p = d300101 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1770 p else NetHack.Sokoban22Refined85.d14 p) = d300101 p
  rw [oldNode1770, oldNode14]
  rfl
theorem oldNode5542 (p : Pattern) : NetHack.Sokoban22Refined85.d5542 p = d300102 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5541 p else NetHack.Sokoban22Refined85.d14 p) = d300102 p
  rw [oldNode5541, oldNode14]
  rfl
theorem oldNode5543 (p : Pattern) : NetHack.Sokoban22Refined85.d5543 p = d300103 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1684 p else NetHack.Sokoban22Refined85.d14 p) = d300103 p
  rw [oldNode1684, oldNode14]
  rfl
theorem oldNode5544 (p : Pattern) : NetHack.Sokoban22Refined85.d5544 p = d300104 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5543 p) = d300104 p
  rw [oldNode12, oldNode5543]
  rfl
theorem oldNode5545 (p : Pattern) : NetHack.Sokoban22Refined85.d5545 p = d300105 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5544 p else NetHack.Sokoban22Refined85.d5542 p) = d300105 p
  rw [oldNode5544, oldNode5542]
  rfl
theorem oldNode5546 (p : Pattern) : NetHack.Sokoban22Refined85.d5546 p = d300106 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1795 p else NetHack.Sokoban22Refined85.d18 p) = d300106 p
  rw [oldNode1795, oldNode18]
  rfl
theorem oldNode5547 (p : Pattern) : NetHack.Sokoban22Refined85.d5547 p = d300107 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5546 p else NetHack.Sokoban22Refined85.d18 p) = d300107 p
  rw [oldNode5546, oldNode18]
  rfl
theorem oldNode5548 (p : Pattern) : NetHack.Sokoban22Refined85.d5548 p = d300108 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1694 p else NetHack.Sokoban22Refined85.d18 p) = d300108 p
  rw [oldNode1694, oldNode18]
  rfl
theorem oldNode5549 (p : Pattern) : NetHack.Sokoban22Refined85.d5549 p = d300109 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5548 p) = d300109 p
  rw [oldNode12, oldNode5548]
  rfl
theorem oldNode5550 (p : Pattern) : NetHack.Sokoban22Refined85.d5550 p = d300110 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5549 p else NetHack.Sokoban22Refined85.d5547 p) = d300110 p
  rw [oldNode5549, oldNode5547]
  rfl
theorem oldNode5551 (p : Pattern) : NetHack.Sokoban22Refined85.d5551 p = d300111 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5550 p else NetHack.Sokoban22Refined85.d5545 p) = d300111 p
  rw [oldNode5550, oldNode5545]
  rfl
theorem oldNode5552 (p : Pattern) : NetHack.Sokoban22Refined85.d5552 p = d300112 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5551 p else NetHack.Sokoban22Refined85.d5545 p) = d300112 p
  rw [oldNode5551, oldNode5545]
  rfl
theorem oldNode5553 (p : Pattern) : NetHack.Sokoban22Refined85.d5553 p = d300113 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d356 p else NetHack.Sokoban22Refined85.d24 p) = d300113 p
  rw [oldNode356, oldNode24]
  rfl
theorem oldNode5554 (p : Pattern) : NetHack.Sokoban22Refined85.d5554 p = d300114 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5553 p else NetHack.Sokoban22Refined85.d24 p) = d300114 p
  rw [oldNode5553, oldNode24]
  rfl
theorem oldNode5555 (p : Pattern) : NetHack.Sokoban22Refined85.d5555 p = d300115 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1702 p else NetHack.Sokoban22Refined85.d24 p) = d300115 p
  rw [oldNode1702, oldNode24]
  rfl
theorem oldNode5556 (p : Pattern) : NetHack.Sokoban22Refined85.d5556 p = d300116 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5555 p) = d300116 p
  rw [oldNode12, oldNode5555]
  rfl
theorem oldNode5557 (p : Pattern) : NetHack.Sokoban22Refined85.d5557 p = d300117 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5556 p else NetHack.Sokoban22Refined85.d5554 p) = d300117 p
  rw [oldNode5556, oldNode5554]
  rfl
theorem oldNode5558 (p : Pattern) : NetHack.Sokoban22Refined85.d5558 p = d300118 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5557 p) = d300118 p
  rw [oldNode12, oldNode5557]
  rfl
theorem oldNode5559 (p : Pattern) : NetHack.Sokoban22Refined85.d5559 p = d300119 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5558 p else NetHack.Sokoban22Refined85.d5551 p) = d300119 p
  rw [oldNode5558, oldNode5551]
  rfl
theorem oldNode5560 (p : Pattern) : NetHack.Sokoban22Refined85.d5560 p = d300120 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5559 p else NetHack.Sokoban22Refined85.d5552 p) = d300120 p
  rw [oldNode5559, oldNode5552]
  rfl
theorem oldNode5561 (p : Pattern) : NetHack.Sokoban22Refined85.d5561 p = d300121 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1714 p else NetHack.Sokoban22Refined85.d31 p) = d300121 p
  rw [oldNode1714, oldNode31]
  rfl
theorem oldNode5562 (p : Pattern) : NetHack.Sokoban22Refined85.d5562 p = d300122 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5561 p) = d300122 p
  rw [oldNode12, oldNode5561]
  rfl
theorem oldNode5563 (p : Pattern) : NetHack.Sokoban22Refined85.d5563 p = d300123 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5562 p else NetHack.Sokoban22Refined85.d5542 p) = d300123 p
  rw [oldNode5562, oldNode5542]
  rfl
theorem oldNode5564 (p : Pattern) : NetHack.Sokoban22Refined85.d5564 p = d300124 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1722 p else NetHack.Sokoban22Refined85.d35 p) = d300124 p
  rw [oldNode1722, oldNode35]
  rfl
theorem oldNode5565 (p : Pattern) : NetHack.Sokoban22Refined85.d5565 p = d300125 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5564 p) = d300125 p
  rw [oldNode12, oldNode5564]
  rfl
theorem oldNode5566 (p : Pattern) : NetHack.Sokoban22Refined85.d5566 p = d300126 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5565 p else NetHack.Sokoban22Refined85.d5542 p) = d300126 p
  rw [oldNode5565, oldNode5542]
  rfl
theorem oldNode5567 (p : Pattern) : NetHack.Sokoban22Refined85.d5567 p = d300127 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5566 p else NetHack.Sokoban22Refined85.d5563 p) = d300127 p
  rw [oldNode5566, oldNode5563]
  rfl
theorem oldNode5568 (p : Pattern) : NetHack.Sokoban22Refined85.d5568 p = d300128 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d327 p else NetHack.Sokoban22Refined85.d40 p) = d300128 p
  rw [oldNode327, oldNode40]
  rfl
theorem oldNode5569 (p : Pattern) : NetHack.Sokoban22Refined85.d5569 p = d300129 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5568 p) = d300129 p
  rw [oldNode12, oldNode5568]
  rfl
theorem oldNode5570 (p : Pattern) : NetHack.Sokoban22Refined85.d5570 p = d300130 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5569 p else NetHack.Sokoban22Refined85.d5542 p) = d300130 p
  rw [oldNode5569, oldNode5542]
  rfl
theorem oldNode5571 (p : Pattern) : NetHack.Sokoban22Refined85.d5571 p = d300131 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5547 p) = d300131 p
  rw [oldNode12, oldNode5547]
  rfl
theorem oldNode5572 (p : Pattern) : NetHack.Sokoban22Refined85.d5572 p = d300132 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5571 p else NetHack.Sokoban22Refined85.d5570 p) = d300132 p
  rw [oldNode5571, oldNode5570]
  rfl
theorem oldNode5573 (p : Pattern) : NetHack.Sokoban22Refined85.d5573 p = d300133 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5572 p else NetHack.Sokoban22Refined85.d5567 p) = d300133 p
  rw [oldNode5572, oldNode5567]
  rfl
theorem oldNode5574 (p : Pattern) : NetHack.Sokoban22Refined85.d5574 p = d300134 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5542 p) = d300134 p
  rw [oldNode12, oldNode5542]
  rfl
theorem oldNode5575 (p : Pattern) : NetHack.Sokoban22Refined85.d5575 p = d300135 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5571 p else NetHack.Sokoban22Refined85.d5574 p) = d300135 p
  rw [oldNode5571, oldNode5574]
  rfl
theorem oldNode5576 (p : Pattern) : NetHack.Sokoban22Refined85.d5576 p = d300136 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5554 p) = d300136 p
  rw [oldNode12, oldNode5554]
  rfl
theorem oldNode5577 (p : Pattern) : NetHack.Sokoban22Refined85.d5577 p = d300137 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5576 p) = d300137 p
  rw [oldNode12, oldNode5576]
  rfl
theorem oldNode5578 (p : Pattern) : NetHack.Sokoban22Refined85.d5578 p = d300138 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5577 p else NetHack.Sokoban22Refined85.d5575 p) = d300138 p
  rw [oldNode5577, oldNode5575]
  rfl
theorem oldNode5579 (p : Pattern) : NetHack.Sokoban22Refined85.d5579 p = d300139 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5578 p else NetHack.Sokoban22Refined85.d5573 p) = d300139 p
  rw [oldNode5578, oldNode5573]
  rfl
theorem oldNode5580 (p : Pattern) : NetHack.Sokoban22Refined85.d5580 p = d300140 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5579 p else NetHack.Sokoban22Refined85.d5560 p) = d300140 p
  rw [oldNode5579, oldNode5560]
  rfl
theorem oldNode5581 (p : Pattern) : NetHack.Sokoban22Refined85.d5581 p = d300141 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5561 p else NetHack.Sokoban22Refined85.d31 p) = d300141 p
  rw [oldNode5561, oldNode31]
  rfl
theorem oldNode5582 (p : Pattern) : NetHack.Sokoban22Refined85.d5582 p = d300142 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1743 p else NetHack.Sokoban22Refined85.d31 p) = d300142 p
  rw [oldNode1743, oldNode31]
  rfl
theorem oldNode5583 (p : Pattern) : NetHack.Sokoban22Refined85.d5583 p = d300143 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5582 p) = d300143 p
  rw [oldNode12, oldNode5582]
  rfl
theorem oldNode5584 (p : Pattern) : NetHack.Sokoban22Refined85.d5584 p = d300144 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5583 p else NetHack.Sokoban22Refined85.d5581 p) = d300144 p
  rw [oldNode5583, oldNode5581]
  rfl
theorem oldNode5585 (p : Pattern) : NetHack.Sokoban22Refined85.d5585 p = d300145 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5584 p else NetHack.Sokoban22Refined85.d5545 p) = d300145 p
  rw [oldNode5584, oldNode5545]
  rfl
theorem oldNode5586 (p : Pattern) : NetHack.Sokoban22Refined85.d5586 p = d300146 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5557 p else NetHack.Sokoban22Refined85.d5550 p) = d300146 p
  rw [oldNode5557, oldNode5550]
  rfl
theorem oldNode5587 (p : Pattern) : NetHack.Sokoban22Refined85.d5587 p = d300147 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5586 p else NetHack.Sokoban22Refined85.d5585 p) = d300147 p
  rw [oldNode5586, oldNode5585]
  rfl
theorem oldNode5588 (p : Pattern) : NetHack.Sokoban22Refined85.d5588 p = d300148 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d329 p else NetHack.Sokoban22Refined85.d58 p) = d300148 p
  rw [oldNode329, oldNode58]
  rfl
theorem oldNode5589 (p : Pattern) : NetHack.Sokoban22Refined85.d5589 p = d300149 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5588 p else NetHack.Sokoban22Refined85.d58 p) = d300149 p
  rw [oldNode5588, oldNode58]
  rfl
theorem oldNode5590 (p : Pattern) : NetHack.Sokoban22Refined85.d5590 p = d300150 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5588 p) = d300150 p
  rw [oldNode12, oldNode5588]
  rfl
theorem oldNode5591 (p : Pattern) : NetHack.Sokoban22Refined85.d5591 p = d300151 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5590 p else NetHack.Sokoban22Refined85.d5589 p) = d300151 p
  rw [oldNode5590, oldNode5589]
  rfl
theorem oldNode5592 (p : Pattern) : NetHack.Sokoban22Refined85.d5592 p = d300152 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5591 p else NetHack.Sokoban22Refined85.d5550 p) = d300152 p
  rw [oldNode5591, oldNode5550]
  rfl
theorem oldNode5593 (p : Pattern) : NetHack.Sokoban22Refined85.d5593 p = d300153 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5568 p else NetHack.Sokoban22Refined85.d40 p) = d300153 p
  rw [oldNode5568, oldNode40]
  rfl
theorem oldNode5594 (p : Pattern) : NetHack.Sokoban22Refined85.d5594 p = d300154 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5569 p else NetHack.Sokoban22Refined85.d5593 p) = d300154 p
  rw [oldNode5569, oldNode5593]
  rfl
theorem oldNode5595 (p : Pattern) : NetHack.Sokoban22Refined85.d5595 p = d300155 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5594 p) = d300155 p
  rw [oldNode12, oldNode5594]
  rfl
theorem oldNode5596 (p : Pattern) : NetHack.Sokoban22Refined85.d5596 p = d300156 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5595 p else NetHack.Sokoban22Refined85.d5592 p) = d300156 p
  rw [oldNode5595, oldNode5592]
  rfl
theorem oldNode5597 (p : Pattern) : NetHack.Sokoban22Refined85.d5597 p = d300157 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5596 p else NetHack.Sokoban22Refined85.d5587 p) = d300157 p
  rw [oldNode5596, oldNode5587]
  rfl
theorem oldNode5598 (p : Pattern) : NetHack.Sokoban22Refined85.d5598 p = d300158 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5581 p) = d300158 p
  rw [oldNode12, oldNode5581]
  rfl
theorem oldNode5599 (p : Pattern) : NetHack.Sokoban22Refined85.d5599 p = d300159 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5598 p else NetHack.Sokoban22Refined85.d5566 p) = d300159 p
  rw [oldNode5598, oldNode5566]
  rfl
theorem oldNode5600 (p : Pattern) : NetHack.Sokoban22Refined85.d5600 p = d300160 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5576 p else NetHack.Sokoban22Refined85.d5571 p) = d300160 p
  rw [oldNode5576, oldNode5571]
  rfl
theorem oldNode5601 (p : Pattern) : NetHack.Sokoban22Refined85.d5601 p = d300161 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5600 p else NetHack.Sokoban22Refined85.d5599 p) = d300161 p
  rw [oldNode5600, oldNode5599]
  rfl
theorem oldNode5602 (p : Pattern) : NetHack.Sokoban22Refined85.d5602 p = d300162 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5589 p) = d300162 p
  rw [oldNode12, oldNode5589]
  rfl
theorem oldNode5603 (p : Pattern) : NetHack.Sokoban22Refined85.d5603 p = d300163 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5602 p else NetHack.Sokoban22Refined85.d5571 p) = d300163 p
  rw [oldNode5602, oldNode5571]
  rfl
theorem oldNode5604 (p : Pattern) : NetHack.Sokoban22Refined85.d5604 p = d300164 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5593 p) = d300164 p
  rw [oldNode12, oldNode5593]
  rfl
theorem oldNode5605 (p : Pattern) : NetHack.Sokoban22Refined85.d5605 p = d300165 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5604 p) = d300165 p
  rw [oldNode12, oldNode5604]
  rfl
theorem oldNode5606 (p : Pattern) : NetHack.Sokoban22Refined85.d5606 p = d300166 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5605 p else NetHack.Sokoban22Refined85.d5603 p) = d300166 p
  rw [oldNode5605, oldNode5603]
  rfl
theorem oldNode5607 (p : Pattern) : NetHack.Sokoban22Refined85.d5607 p = d300167 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5606 p else NetHack.Sokoban22Refined85.d5601 p) = d300167 p
  rw [oldNode5606, oldNode5601]
  rfl
theorem oldNode5608 (p : Pattern) : NetHack.Sokoban22Refined85.d5608 p = d300168 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5607 p else NetHack.Sokoban22Refined85.d5597 p) = d300168 p
  rw [oldNode5607, oldNode5597]
  rfl
theorem oldNode5609 (p : Pattern) : NetHack.Sokoban22Refined85.d5609 p = d300169 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5608 p else NetHack.Sokoban22Refined85.d5580 p) = d300169 p
  rw [oldNode5608, oldNode5580]
  rfl
theorem oldNode5610 (p : Pattern) : NetHack.Sokoban22Refined85.d5610 p = d300170 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5541 p) = d300170 p
  rw [oldNode12, oldNode5541]
  rfl
theorem oldNode5611 (p : Pattern) : NetHack.Sokoban22Refined85.d5611 p = d300171 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5610 p else NetHack.Sokoban22Refined85.d5542 p) = d300171 p
  rw [oldNode5610, oldNode5542]
  rfl
theorem oldNode5612 (p : Pattern) : NetHack.Sokoban22Refined85.d5612 p = d300172 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5546 p) = d300172 p
  rw [oldNode12, oldNode5546]
  rfl
theorem oldNode5613 (p : Pattern) : NetHack.Sokoban22Refined85.d5613 p = d300173 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5612 p else NetHack.Sokoban22Refined85.d5547 p) = d300173 p
  rw [oldNode5612, oldNode5547]
  rfl
theorem oldNode5614 (p : Pattern) : NetHack.Sokoban22Refined85.d5614 p = d300174 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5613 p else NetHack.Sokoban22Refined85.d5611 p) = d300174 p
  rw [oldNode5613, oldNode5611]
  rfl
theorem oldNode5615 (p : Pattern) : NetHack.Sokoban22Refined85.d5615 p = d300175 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5614 p else NetHack.Sokoban22Refined85.d5611 p) = d300175 p
  rw [oldNode5614, oldNode5611]
  rfl
theorem oldNode5616 (p : Pattern) : NetHack.Sokoban22Refined85.d5616 p = d300176 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5553 p) = d300176 p
  rw [oldNode12, oldNode5553]
  rfl
theorem oldNode5617 (p : Pattern) : NetHack.Sokoban22Refined85.d5617 p = d300177 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5616 p else NetHack.Sokoban22Refined85.d5554 p) = d300177 p
  rw [oldNode5616, oldNode5554]
  rfl
theorem oldNode5618 (p : Pattern) : NetHack.Sokoban22Refined85.d5618 p = d300178 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5617 p) = d300178 p
  rw [oldNode12, oldNode5617]
  rfl
theorem oldNode5619 (p : Pattern) : NetHack.Sokoban22Refined85.d5619 p = d300179 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5618 p else NetHack.Sokoban22Refined85.d5614 p) = d300179 p
  rw [oldNode5618, oldNode5614]
  rfl
theorem oldNode5620 (p : Pattern) : NetHack.Sokoban22Refined85.d5620 p = d300180 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5619 p else NetHack.Sokoban22Refined85.d5615 p) = d300180 p
  rw [oldNode5619, oldNode5615]
  rfl
theorem oldNode5621 (p : Pattern) : NetHack.Sokoban22Refined85.d5621 p = d300181 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5562 p else NetHack.Sokoban22Refined85.d5581 p) = d300181 p
  rw [oldNode5562, oldNode5581]
  rfl
theorem oldNode5622 (p : Pattern) : NetHack.Sokoban22Refined85.d5622 p = d300182 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5564 p else NetHack.Sokoban22Refined85.d35 p) = d300182 p
  rw [oldNode5564, oldNode35]
  rfl
theorem oldNode5623 (p : Pattern) : NetHack.Sokoban22Refined85.d5623 p = d300183 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5565 p else NetHack.Sokoban22Refined85.d5622 p) = d300183 p
  rw [oldNode5565, oldNode5622]
  rfl
theorem oldNode5624 (p : Pattern) : NetHack.Sokoban22Refined85.d5624 p = d300184 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5623 p else NetHack.Sokoban22Refined85.d5621 p) = d300184 p
  rw [oldNode5623, oldNode5621]
  rfl
theorem oldNode5625 (p : Pattern) : NetHack.Sokoban22Refined85.d5625 p = d300185 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5595 p else NetHack.Sokoban22Refined85.d5624 p) = d300185 p
  rw [oldNode5595, oldNode5624]
  rfl
theorem oldNode5626 (p : Pattern) : NetHack.Sokoban22Refined85.d5626 p = d300186 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5625 p) = d300186 p
  rw [oldNode12, oldNode5625]
  rfl
theorem oldNode5627 (p : Pattern) : NetHack.Sokoban22Refined85.d5627 p = d300187 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5626 p else NetHack.Sokoban22Refined85.d5620 p) = d300187 p
  rw [oldNode5626, oldNode5620]
  rfl
theorem oldNode5628 (p : Pattern) : NetHack.Sokoban22Refined85.d5628 p = d300188 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5621 p else NetHack.Sokoban22Refined85.d5611 p) = d300188 p
  rw [oldNode5621, oldNode5611]
  rfl
theorem oldNode5629 (p : Pattern) : NetHack.Sokoban22Refined85.d5629 p = d300189 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5617 p else NetHack.Sokoban22Refined85.d5613 p) = d300189 p
  rw [oldNode5617, oldNode5613]
  rfl
theorem oldNode5630 (p : Pattern) : NetHack.Sokoban22Refined85.d5630 p = d300190 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5629 p else NetHack.Sokoban22Refined85.d5628 p) = d300190 p
  rw [oldNode5629, oldNode5628]
  rfl
theorem oldNode5631 (p : Pattern) : NetHack.Sokoban22Refined85.d5631 p = d300191 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5591 p else NetHack.Sokoban22Refined85.d5613 p) = d300191 p
  rw [oldNode5591, oldNode5613]
  rfl
theorem oldNode5632 (p : Pattern) : NetHack.Sokoban22Refined85.d5632 p = d300192 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5595 p else NetHack.Sokoban22Refined85.d5631 p) = d300192 p
  rw [oldNode5595, oldNode5631]
  rfl
theorem oldNode5633 (p : Pattern) : NetHack.Sokoban22Refined85.d5633 p = d300193 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5632 p else NetHack.Sokoban22Refined85.d5630 p) = d300193 p
  rw [oldNode5632, oldNode5630]
  rfl
theorem oldNode5634 (p : Pattern) : NetHack.Sokoban22Refined85.d5634 p = d300194 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5623 p) = d300194 p
  rw [oldNode12, oldNode5623]
  rfl
theorem oldNode5635 (p : Pattern) : NetHack.Sokoban22Refined85.d5635 p = d300195 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5634 p) = d300195 p
  rw [oldNode12, oldNode5634]
  rfl
theorem oldNode5636 (p : Pattern) : NetHack.Sokoban22Refined85.d5636 p = d300196 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5635 p) = d300196 p
  rw [oldNode12, oldNode5635]
  rfl
theorem oldNode5637 (p : Pattern) : NetHack.Sokoban22Refined85.d5637 p = d300197 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5636 p else NetHack.Sokoban22Refined85.d5633 p) = d300197 p
  rw [oldNode5636, oldNode5633]
  rfl
theorem oldNode5638 (p : Pattern) : NetHack.Sokoban22Refined85.d5638 p = d300198 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5637 p else NetHack.Sokoban22Refined85.d5627 p) = d300198 p
  rw [oldNode5637, oldNode5627]
  rfl
theorem oldNode5639 (p : Pattern) : NetHack.Sokoban22Refined85.d5639 p = d300199 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5638 p else NetHack.Sokoban22Refined85.d5609 p) = d300199 p
  rw [oldNode5638, oldNode5609]
  rfl
theorem oldNode5640 (p : Pattern) : NetHack.Sokoban22Refined85.d5640 p = d300200 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5594 p else NetHack.Sokoban22Refined85.d5617 p) = d300200 p
  rw [oldNode5594, oldNode5617]
  rfl
theorem oldNode5641 (p : Pattern) : NetHack.Sokoban22Refined85.d5641 p = d300201 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5595 p else NetHack.Sokoban22Refined85.d5640 p) = d300201 p
  rw [oldNode5595, oldNode5640]
  rfl
theorem oldNode5642 (p : Pattern) : NetHack.Sokoban22Refined85.d5642 p = d300202 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5595 p) = d300202 p
  rw [oldNode12, oldNode5595]
  rfl
theorem oldNode5643 (p : Pattern) : NetHack.Sokoban22Refined85.d5643 p = d300203 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5642 p else NetHack.Sokoban22Refined85.d5641 p) = d300203 p
  rw [oldNode5642, oldNode5641]
  rfl
theorem oldNode5644 (p : Pattern) : NetHack.Sokoban22Refined85.d5644 p = d300204 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5642 p) = d300204 p
  rw [oldNode12, oldNode5642]
  rfl
theorem oldNode5645 (p : Pattern) : NetHack.Sokoban22Refined85.d5645 p = d300205 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5644 p else NetHack.Sokoban22Refined85.d5643 p) = d300205 p
  rw [oldNode5644, oldNode5643]
  rfl
theorem oldNode5646 (p : Pattern) : NetHack.Sokoban22Refined85.d5646 p = d300206 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5644 p) = d300206 p
  rw [oldNode12, oldNode5644]
  rfl
theorem oldNode5647 (p : Pattern) : NetHack.Sokoban22Refined85.d5647 p = d300207 p := by
  change (if p 141 then NetHack.Sokoban22Refined85.d5646 p else NetHack.Sokoban22Refined85.d5645 p) = d300207 p
  rw [oldNode5646, oldNode5645]
  rfl
theorem oldNode5648 (p : Pattern) : NetHack.Sokoban22Refined85.d5648 p = d300208 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d5647 p else NetHack.Sokoban22Refined85.d5638 p) = d300208 p
  rw [oldNode5647, oldNode5638]
  rfl
theorem oldNode5649 (p : Pattern) : NetHack.Sokoban22Refined85.d5649 p = d300209 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5648 p else NetHack.Sokoban22Refined85.d5639 p) = d300209 p
  rw [oldNode5648, oldNode5639]
  rfl
theorem oldNode5650 (p : Pattern) : NetHack.Sokoban22Refined85.d5650 p = d300210 p := by
  change (if p 138 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5638 p) = d300210 p
  rw [oldNode12, oldNode5638]
  rfl
theorem oldNode5651 (p : Pattern) : NetHack.Sokoban22Refined85.d5651 p = d300211 p := by
  change (if p 116 then NetHack.Sokoban22Refined85.d5650 p else NetHack.Sokoban22Refined85.d5639 p) = d300211 p
  rw [oldNode5650, oldNode5639]
  rfl
theorem oldNode5652 (p : Pattern) : NetHack.Sokoban22Refined85.d5652 p = d300212 p := by
  change (if p 115 then NetHack.Sokoban22Refined85.d5651 p else NetHack.Sokoban22Refined85.d5649 p) = d300212 p
  rw [oldNode5651, oldNode5649]
  rfl
theorem oldNode5653 (p : Pattern) : NetHack.Sokoban22Refined85.d5653 p = d300213 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1940 p else NetHack.Sokoban22Refined85.d103 p) = d300213 p
  rw [oldNode1940, oldNode103]
  rfl
theorem oldNode5654 (p : Pattern) : NetHack.Sokoban22Refined85.d5654 p = d300214 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5653 p else NetHack.Sokoban22Refined85.d103 p) = d300214 p
  rw [oldNode5653, oldNode103]
  rfl
theorem oldNode5655 (p : Pattern) : NetHack.Sokoban22Refined85.d5655 p = d300215 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1873 p else NetHack.Sokoban22Refined85.d103 p) = d300215 p
  rw [oldNode1873, oldNode103]
  rfl
theorem oldNode5656 (p : Pattern) : NetHack.Sokoban22Refined85.d5656 p = d300216 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5655 p) = d300216 p
  rw [oldNode12, oldNode5655]
  rfl
theorem oldNode5657 (p : Pattern) : NetHack.Sokoban22Refined85.d5657 p = d300217 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5656 p else NetHack.Sokoban22Refined85.d5654 p) = d300217 p
  rw [oldNode5656, oldNode5654]
  rfl
theorem oldNode5658 (p : Pattern) : NetHack.Sokoban22Refined85.d5658 p = d300218 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1964 p else NetHack.Sokoban22Refined85.d107 p) = d300218 p
  rw [oldNode1964, oldNode107]
  rfl
theorem oldNode5659 (p : Pattern) : NetHack.Sokoban22Refined85.d5659 p = d300219 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5658 p else NetHack.Sokoban22Refined85.d107 p) = d300219 p
  rw [oldNode5658, oldNode107]
  rfl
theorem oldNode5660 (p : Pattern) : NetHack.Sokoban22Refined85.d5660 p = d300220 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1881 p else NetHack.Sokoban22Refined85.d107 p) = d300220 p
  rw [oldNode1881, oldNode107]
  rfl
theorem oldNode5661 (p : Pattern) : NetHack.Sokoban22Refined85.d5661 p = d300221 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5660 p) = d300221 p
  rw [oldNode12, oldNode5660]
  rfl
theorem oldNode5662 (p : Pattern) : NetHack.Sokoban22Refined85.d5662 p = d300222 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5661 p else NetHack.Sokoban22Refined85.d5659 p) = d300222 p
  rw [oldNode5661, oldNode5659]
  rfl
theorem oldNode5663 (p : Pattern) : NetHack.Sokoban22Refined85.d5663 p = d300223 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5662 p else NetHack.Sokoban22Refined85.d5657 p) = d300223 p
  rw [oldNode5662, oldNode5657]
  rfl
theorem oldNode5664 (p : Pattern) : NetHack.Sokoban22Refined85.d5664 p = d300224 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5663 p else NetHack.Sokoban22Refined85.d5657 p) = d300224 p
  rw [oldNode5663, oldNode5657]
  rfl
theorem oldNode5665 (p : Pattern) : NetHack.Sokoban22Refined85.d5665 p = d300225 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5591 p) = d300225 p
  rw [oldNode12, oldNode5591]
  rfl
theorem oldNode5666 (p : Pattern) : NetHack.Sokoban22Refined85.d5666 p = d300226 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5665 p else NetHack.Sokoban22Refined85.d5663 p) = d300226 p
  rw [oldNode5665, oldNode5663]
  rfl
theorem oldNode5667 (p : Pattern) : NetHack.Sokoban22Refined85.d5667 p = d300227 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5666 p else NetHack.Sokoban22Refined85.d5664 p) = d300227 p
  rw [oldNode5666, oldNode5664]
  rfl
theorem oldNode5668 (p : Pattern) : NetHack.Sokoban22Refined85.d5668 p = d300228 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1895 p else NetHack.Sokoban22Refined85.d116 p) = d300228 p
  rw [oldNode1895, oldNode116]
  rfl
theorem oldNode5669 (p : Pattern) : NetHack.Sokoban22Refined85.d5669 p = d300229 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5668 p) = d300229 p
  rw [oldNode12, oldNode5668]
  rfl
theorem oldNode5670 (p : Pattern) : NetHack.Sokoban22Refined85.d5670 p = d300230 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5669 p else NetHack.Sokoban22Refined85.d5654 p) = d300230 p
  rw [oldNode5669, oldNode5654]
  rfl
theorem oldNode5671 (p : Pattern) : NetHack.Sokoban22Refined85.d5671 p = d300231 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1903 p else NetHack.Sokoban22Refined85.d120 p) = d300231 p
  rw [oldNode1903, oldNode120]
  rfl
theorem oldNode5672 (p : Pattern) : NetHack.Sokoban22Refined85.d5672 p = d300232 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5671 p) = d300232 p
  rw [oldNode12, oldNode5671]
  rfl
theorem oldNode5673 (p : Pattern) : NetHack.Sokoban22Refined85.d5673 p = d300233 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5672 p else NetHack.Sokoban22Refined85.d5654 p) = d300233 p
  rw [oldNode5672, oldNode5654]
  rfl
theorem oldNode5674 (p : Pattern) : NetHack.Sokoban22Refined85.d5674 p = d300234 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5673 p else NetHack.Sokoban22Refined85.d5670 p) = d300234 p
  rw [oldNode5673, oldNode5670]
  rfl
theorem oldNode5675 (p : Pattern) : NetHack.Sokoban22Refined85.d5675 p = d300235 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5654 p) = d300235 p
  rw [oldNode12, oldNode5654]
  rfl
theorem oldNode5676 (p : Pattern) : NetHack.Sokoban22Refined85.d5676 p = d300236 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5659 p) = d300236 p
  rw [oldNode12, oldNode5659]
  rfl
theorem oldNode5677 (p : Pattern) : NetHack.Sokoban22Refined85.d5677 p = d300237 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5676 p else NetHack.Sokoban22Refined85.d5675 p) = d300237 p
  rw [oldNode5676, oldNode5675]
  rfl
theorem oldNode5678 (p : Pattern) : NetHack.Sokoban22Refined85.d5678 p = d300238 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5677 p else NetHack.Sokoban22Refined85.d5674 p) = d300238 p
  rw [oldNode5677, oldNode5674]
  rfl
theorem oldNode5679 (p : Pattern) : NetHack.Sokoban22Refined85.d5679 p = d300239 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5602 p) = d300239 p
  rw [oldNode12, oldNode5602]
  rfl
theorem oldNode5680 (p : Pattern) : NetHack.Sokoban22Refined85.d5680 p = d300240 p := by
  change (if p 162 then NetHack.Sokoban22Refined85.d5679 p else NetHack.Sokoban22Refined85.d5677 p) = d300240 p
  rw [oldNode5679, oldNode5677]
  rfl
theorem oldNode5681 (p : Pattern) : NetHack.Sokoban22Refined85.d5681 p = d300241 p := by
  change (if p 161 then NetHack.Sokoban22Refined85.d5680 p else NetHack.Sokoban22Refined85.d5678 p) = d300241 p
  rw [oldNode5680, oldNode5678]
  rfl
theorem oldNode5682 (p : Pattern) : NetHack.Sokoban22Refined85.d5682 p = d300242 p := by
  change (if p 160 then NetHack.Sokoban22Refined85.d5681 p else NetHack.Sokoban22Refined85.d5667 p) = d300242 p
  rw [oldNode5681, oldNode5667]
  rfl
theorem oldNode5683 (p : Pattern) : NetHack.Sokoban22Refined85.d5683 p = d300243 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d5668 p else NetHack.Sokoban22Refined85.d116 p) = d300243 p
  rw [oldNode5668, oldNode116]
  rfl
theorem oldNode5684 (p : Pattern) : NetHack.Sokoban22Refined85.d5684 p = d300244 p := by
  change (if p 224 then NetHack.Sokoban22Refined85.d1919 p else NetHack.Sokoban22Refined85.d116 p) = d300244 p
  rw [oldNode1919, oldNode116]
  rfl
theorem oldNode5685 (p : Pattern) : NetHack.Sokoban22Refined85.d5685 p = d300245 p := by
  change (if p 204 then NetHack.Sokoban22Refined85.d12 p else NetHack.Sokoban22Refined85.d5684 p) = d300245 p
  rw [oldNode12, oldNode5684]
  rfl
theorem oldNode5686 (p : Pattern) : NetHack.Sokoban22Refined85.d5686 p = d300246 p := by
  change (if p 182 then NetHack.Sokoban22Refined85.d5685 p else NetHack.Sokoban22Refined85.d5683 p) = d300246 p
  rw [oldNode5685, oldNode5683]
  rfl
theorem oldNode5687 (p : Pattern) : NetHack.Sokoban22Refined85.d5687 p = d300247 p := by
  change (if p 163 then NetHack.Sokoban22Refined85.d5686 p else NetHack.Sokoban22Refined85.d5657 p) = d300247 p
  rw [oldNode5686, oldNode5657]
  rfl
end NetHack.Soko22Hazard87
