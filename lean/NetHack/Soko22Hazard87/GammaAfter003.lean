import NetHack.Soko22Hazard87.GammaAfter002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter300 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) = d0 p := by
  change bonus 83 _ = _
  rw [at83]
  rfl
theorem gammaAfter301 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 81)) (HazardPattern.afterPattern 10000 p (.walk 81)) = d0 p := by
  change bonus 81 _ = _
  rw [at81]
  rfl
theorem gammaAfter302 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter303 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter304 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) = d0 p := by
  change bonus 83 _ = _
  rw [at83]
  rfl
theorem gammaAfter305 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter306 (p : Pattern) : bonus (HazardPattern.nextHero (.push 127 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 149))) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  change d0 (u125 p) = d0 p
  exact allUpdate77 p
theorem gammaAfter307 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) = d0 p := by
  change bonus 106 _ = _
  rw [at106]
  rfl
theorem gammaAfter308 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  rfl
theorem gammaAfter309 (p : Pattern) : bonus (HazardPattern.nextHero (.push 104 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 103))) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  change d0 (u81 p) = d0 p
  exact allUpdate39 p
theorem gammaAfter310 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) = d0 p := by
  change bonus 84 _ = _
  rw [at84]
  rfl
theorem gammaAfter311 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 82)) (HazardPattern.afterPattern 10000 p (.walk 82)) = d0 p := by
  change bonus 82 _ = _
  rw [at82]
  rfl
theorem gammaAfter312 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  rfl
theorem gammaAfter313 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter314 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 84)) (HazardPattern.afterPattern 10000 p (.walk 84)) = d0 p := by
  change bonus 84 _ = _
  rw [at84]
  rfl
theorem gammaAfter315 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  rfl
theorem gammaAfter316 (p : Pattern) : bonus (HazardPattern.nextHero (.push 128 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 150))) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  change d0 (u127 p) = d0 p
  exact allUpdate79 p
theorem gammaAfter317 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  rfl
theorem gammaAfter318 (p : Pattern) : bonus (HazardPattern.nextHero (.push 105 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 104))) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  change d0 (u85 p) = d0 p
  exact allUpdate43 p
theorem gammaAfter319 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 83)) (HazardPattern.afterPattern 10000 p (.walk 83)) = d0 p := by
  change bonus 83 _ = _
  rw [at83]
  rfl
theorem gammaAfter320 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter321 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 89)) (HazardPattern.afterPattern 10000 p (.walk 89)) = d4334 p := by
  change bonus 89 _ = _
  rw [at89]
  rfl
theorem gammaAfter322 (p : Pattern) : bonus (HazardPattern.nextHero (.push 89 (.stay 67))) (HazardPattern.afterPattern 10000 p (.push 89 (.stay 67))) = d0 p := by
  change bonus 89 _ = _
  rw [at89]
  change d4334 (u46 p) = d0 p
  exact allUpdate4167 p
theorem gammaAfter323 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) = d5849 p := by
  change bonus 133 _ = _
  rw [at133]
  rfl
theorem gammaAfter324 (p : Pattern) : bonus (HazardPattern.nextHero (.push 133 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 155))) = d0 p := by
  change bonus 133 _ = _
  rw [at133]
  change d5849 (u129 p) = d0 p
  exact allUpdate5304 p
theorem gammaAfter325 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) = d4650 p := by
  change bonus 90 _ = _
  rw [at90]
  rfl
theorem gammaAfter326 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter327 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) = d5349 p := by
  change bonus 91 _ = _
  rw [at91]
  rfl
theorem gammaAfter328 (p : Pattern) : bonus (HazardPattern.nextHero (.push 91 (.stay 69))) (HazardPattern.afterPattern 10000 p (.push 91 (.stay 69))) = d83150 p := by
  change bonus 91 _ = _
  rw [at91]
  change d5349 (u50 p) = d83150 p
  exact allUpdate4696 p
theorem gammaAfter329 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter330 (p : Pattern) : bonus (HazardPattern.nextHero (.push 135 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 157))) = d87043 p := by
  change bonus 135 _ = _
  rw [at135]
  change d8234 (u135 p) = d87043 p
  exact allUpdate9847 p
theorem gammaAfter331 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter332 (p : Pattern) : bonus (HazardPattern.nextHero (.push 114 (.stay 115))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 115))) = d90845 p := by
  change bonus 114 _ = _
  rw [at114]
  change d7239 (u95 p) = d90845 p
  exact allUpdate8539 p
theorem gammaAfter333 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 90)) (HazardPattern.afterPattern 10000 p (.walk 90)) = d4650 p := by
  change bonus 90 _ = _
  rw [at90]
  rfl
theorem gammaAfter334 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter335 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter336 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter337 (p : Pattern) : bonus (HazardPattern.nextHero (.push 136 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 158))) = d96219 p := by
  change bonus 136 _ = _
  rw [at136]
  change d9291 (u137 p) = d96219 p
  exact allUpdate10348 p
theorem gammaAfter338 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter339 (p : Pattern) : bonus (HazardPattern.nextHero (.push 115 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 116))) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  change d0 (u97 p) = d0 p
  exact allUpdate49 p
theorem gammaAfter340 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) = d6737 p := by
  change bonus 113 _ = _
  rw [at113]
  rfl
theorem gammaAfter341 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) = d0 p := by
  change bonus 93 _ = _
  rw [at93]
  rfl
theorem gammaAfter342 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 91)) (HazardPattern.afterPattern 10000 p (.walk 91)) = d5349 p := by
  change bonus 91 _ = _
  rw [at91]
  rfl
theorem gammaAfter343 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter344 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) = d0 p := by
  change bonus 93 _ = _
  rw [at93]
  rfl
theorem gammaAfter345 (p : Pattern) : bonus (HazardPattern.nextHero (.push 93 (.stay 71))) (HazardPattern.afterPattern 10000 p (.push 93 (.stay 71))) = d0 p := by
  change bonus 93 _ = _
  rw [at93]
  change d0 (u52 p) = d0 p
  exact allUpdate10 p
theorem gammaAfter346 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  rfl
theorem gammaAfter347 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter348 (p : Pattern) : bonus (HazardPattern.nextHero (.push 114 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 114 (.stay 113))) = d100016 p := by
  change bonus 114 _ = _
  rw [at114]
  change d7239 (u94 p) = d100016 p
  exact allUpdate8010 p
theorem gammaAfter349 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  rfl
theorem gammaAfter350 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  rfl
theorem gammaAfter351 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter352 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 94)) (HazardPattern.afterPattern 10000 p (.walk 94)) = d0 p := by
  change bonus 94 _ = _
  rw [at94]
  rfl
theorem gammaAfter353 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  rfl
theorem gammaAfter354 (p : Pattern) : bonus (HazardPattern.nextHero (.push 138 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 160))) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  change d0 (u139 p) = d0 p
  exact allUpdate81 p
theorem gammaAfter355 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter356 (p : Pattern) : bonus (HazardPattern.nextHero (.push 115 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 115 (.stay 114))) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  change d0 (u96 p) = d0 p
  exact allUpdate48 p
theorem gammaAfter357 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  rfl
theorem gammaAfter358 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 93)) (HazardPattern.afterPattern 10000 p (.walk 93)) = d0 p := by
  change bonus 93 _ = _
  rw [at93]
  rfl
theorem gammaAfter359 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  rfl
theorem gammaAfter360 (p : Pattern) : bonus (HazardPattern.nextHero (.push 96 (.stay 74))) (HazardPattern.afterPattern 10000 p (.push 96 (.stay 74))) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  change d0 (u58 p) = d0 p
  exact allUpdate16 p
theorem gammaAfter361 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter362 (p : Pattern) : bonus (HazardPattern.nextHero (.push 119 (.stay 120))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 120))) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  change d0 (u102 p) = d0 p
  exact allUpdate54 p
theorem gammaAfter363 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  rfl
theorem gammaAfter364 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 95)) (HazardPattern.afterPattern 10000 p (.walk 95)) = d0 p := by
  change bonus 95 _ = _
  rw [at95]
  rfl
theorem gammaAfter365 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter366 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  rfl
theorem gammaAfter367 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter368 (p : Pattern) : bonus (HazardPattern.nextHero (.push 141 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 163))) = d0 p := by
  change bonus 141 _ = _
  rw [at141]
  change d10648 (u141 p) = d0 p
  exact allUpdate10807 p
theorem gammaAfter369 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) = d0 p := by
  change bonus 120 _ = _
  rw [at120]
  rfl
theorem gammaAfter370 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) = d0 p := by
  change bonus 118 _ = _
  rw [at118]
  rfl
theorem gammaAfter371 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) = d0 p := by
  change bonus 98 _ = _
  rw [at98]
  rfl
theorem gammaAfter372 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 96)) (HazardPattern.afterPattern 10000 p (.walk 96)) = d0 p := by
  change bonus 96 _ = _
  rw [at96]
  rfl
theorem gammaAfter373 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 98)) (HazardPattern.afterPattern 10000 p (.walk 98)) = d0 p := by
  change bonus 98 _ = _
  rw [at98]
  rfl
theorem gammaAfter374 (p : Pattern) : bonus (HazardPattern.nextHero (.push 98 (.stay 76))) (HazardPattern.afterPattern 10000 p (.push 98 (.stay 76))) = d0 p := by
  change bonus 98 _ = _
  rw [at98]
  change d0 (u64 p) = d0 p
  exact allUpdate22 p
theorem gammaAfter375 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter376 (p : Pattern) : bonus (HazardPattern.nextHero (.push 119 (.stay 118))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 118))) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  change d0 (u101 p) = d0 p
  exact allUpdate53 p
theorem gammaAfter377 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 97)) (HazardPattern.afterPattern 10000 p (.walk 97)) = d0 p := by
  change bonus 97 _ = _
  rw [at97]
  rfl
theorem gammaAfter378 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter379 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) = d0 p := by
  change bonus 100 _ = _
  rw [at100]
  rfl
theorem gammaAfter380 (p : Pattern) : bonus (HazardPattern.nextHero (.push 100 (.stay 78))) (HazardPattern.afterPattern 10000 p (.push 100 (.stay 78))) = d0 p := by
  change bonus 100 _ = _
  rw [at100]
  change d0 (u66 p) = d0 p
  exact allUpdate24 p
theorem gammaAfter381 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  rfl
theorem gammaAfter382 (p : Pattern) : bonus (HazardPattern.nextHero (.push 144 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 166))) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  change d0 (u143 p) = d0 p
  exact allUpdate83 p
theorem gammaAfter383 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter384 (p : Pattern) : bonus (HazardPattern.nextHero (.push 123 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 124))) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  change d0 (u108 p) = d0 p
  exact allUpdate60 p
theorem gammaAfter385 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  rfl
theorem gammaAfter386 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter387 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  rfl
theorem gammaAfter388 (p : Pattern) : bonus (HazardPattern.nextHero (.push 101 (.stay 79))) (HazardPattern.afterPattern 10000 p (.push 101 (.stay 79))) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  change d0 (u68 p) = d0 p
  exact allUpdate26 p
theorem gammaAfter389 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter390 (p : Pattern) : bonus (HazardPattern.nextHero (.push 145 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 167))) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  change d0 (u147 p) = d0 p
  exact allUpdate87 p
theorem gammaAfter391 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter392 (p : Pattern) : bonus (HazardPattern.nextHero (.push 124 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 125))) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  change d0 (u112 p) = d0 p
  exact allUpdate64 p
theorem gammaAfter393 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  rfl
theorem gammaAfter394 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  rfl
theorem gammaAfter395 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 100)) (HazardPattern.afterPattern 10000 p (.walk 100)) = d0 p := by
  change bonus 100 _ = _
  rw [at100]
  rfl
theorem gammaAfter396 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter397 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  rfl
theorem gammaAfter398 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  rfl
theorem gammaAfter399 (p : Pattern) : bonus (HazardPattern.nextHero (.push 102 (.stay 80))) (HazardPattern.afterPattern 10000 p (.push 102 (.stay 80))) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  change d0 (u72 p) = d0 p
  exact allUpdate30 p
end NetHack.Soko22Hazard87
