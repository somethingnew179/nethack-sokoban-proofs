/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions95
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub11520 (p : Pattern) : d3315 (change p 246 (some 247)) = d6389 p := by
  change (if p 163 then d3283 (change p 246 (some 247)) else d3246 (change p 246 (some 247))) = d6389 p
  rw [sub11488, sub11447]
  rfl
theorem sub11521 (p : Pattern) : d3316 (change p 246 (some 247)) = d6390 p := by
  change (if p 162 then d3284 (change p 246 (some 247)) else d3315 (change p 246 (some 247))) = d6390 p
  rw [sub11489, sub11520]
  rfl
theorem sub11522 (p : Pattern) : d3317 (change p 246 (some 247)) = d6391 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3284 (change p 246 (some 247))) = d6391 p
  rw [sub11428, sub11489]
  rfl
theorem sub11523 (p : Pattern) : d3318 (change p 246 (some 247)) = d6392 p := by
  change (if p 161 then d3317 (change p 246 (some 247)) else d3316 (change p 246 (some 247))) = d6392 p
  rw [sub11522, sub11521]
  rfl
theorem sub11524 (p : Pattern) : d3319 (change p 246 (some 247)) = d6393 p := by
  change (if p 161 then d12 (change p 246 (some 247)) else d3317 (change p 246 (some 247))) = d6393 p
  rw [sub11428, sub11522]
  rfl
theorem sub11525 (p : Pattern) : d3320 (change p 246 (some 247)) = d6394 p := by
  change (if p 160 then d3319 (change p 246 (some 247)) else d3318 (change p 246 (some 247))) = d6394 p
  rw [sub11524, sub11523]
  rfl
theorem sub11526 (p : Pattern) : d3321 (change p 246 (some 247)) = d6395 p := by
  change (if p 160 then d12 (change p 246 (some 247)) else d3319 (change p 246 (some 247))) = d6395 p
  rw [sub11428, sub11524]
  rfl
theorem sub11527 (p : Pattern) : d3322 (change p 246 (some 247)) = d6396 p := by
  change (if p 141 then d3321 (change p 246 (some 247)) else d3320 (change p 246 (some 247))) = d6396 p
  rw [sub11526, sub11525]
  rfl
theorem sub11528 (p : Pattern) : d3323 (change p 246 (some 247)) = d6397 p := by
  change (if p 138 then d3322 (change p 246 (some 247)) else d3313 (change p 246 (some 247))) = d6397 p
  rw [sub11527, sub11518]
  rfl
theorem sub11529 (p : Pattern) : d3324 (change p 246 (some 247)) = d6398 p := by
  change (if p 116 then d3323 (change p 246 (some 247)) else d3314 (change p 246 (some 247))) = d6398 p
  rw [sub11528, sub11519]
  rfl
theorem sub11530 (p : Pattern) : d3325 (change p 246 (some 247)) = d6328 p := by
  change (if p 163 then d3238 (change p 246 (some 247)) else d3236 (change p 246 (some 247))) = d6328 p
  rw [sub11437, sub11435]
  simp only [ite_self]
theorem sub11531 (p : Pattern) : d3326 (change p 246 (some 247)) = d6332 p := by
  change (if p 162 then d3242 (change p 246 (some 247)) else d3325 (change p 246 (some 247))) = d6332 p
  rw [sub11442, sub11530]
  rfl
theorem sub11532 (p : Pattern) : d3327 (change p 246 (some 247)) = d6337 p := by
  change (if p 161 then d3248 (change p 246 (some 247)) else d3326 (change p 246 (some 247))) = d6337 p
  rw [sub11449, sub11531]
  rfl
theorem sub11533 (p : Pattern) : d3328 (change p 246 (some 247)) = d6354 p := by
  change (if p 160 then d3268 (change p 246 (some 247)) else d3327 (change p 246 (some 247))) = d6354 p
  rw [sub11472, sub11532]
  rfl
theorem sub11534 (p : Pattern) : d3329 (change p 246 (some 247)) = d6376 p := by
  change (if p 160 then d3296 (change p 246 (some 247)) else d3308 (change p 246 (some 247))) = d6376 p
  rw [sub11501, sub11513]
  rfl
theorem sub11535 (p : Pattern) : d3330 (change p 246 (some 247)) = d6377 p := by
  change (if p 141 then d3329 (change p 246 (some 247)) else d3328 (change p 246 (some 247))) = d6377 p
  rw [sub11534, sub11533]
  rfl
theorem sub11536 (p : Pattern) : d3331 (change p 246 (some 247)) = d6388 p := by
  change (if p 138 then d3313 (change p 246 (some 247)) else d3330 (change p 246 (some 247))) = d6388 p
  rw [sub11518, sub11535]
  rfl
theorem sub11537 (p : Pattern) : d3332 (change p 246 (some 247)) = d6399 p := by
  change (if p 138 then d12 (change p 246 (some 247)) else d3313 (change p 246 (some 247))) = d6399 p
  rw [sub11428, sub11518]
  rfl
theorem sub11538 (p : Pattern) : d3333 (change p 246 (some 247)) = d6400 p := by
  change (if p 116 then d3332 (change p 246 (some 247)) else d3331 (change p 246 (some 247))) = d6400 p
  rw [sub11537, sub11536]
  rfl
theorem sub11539 (p : Pattern) : d3334 (change p 246 (some 247)) = d6401 p := by
  change (if p 115 then d3333 (change p 246 (some 247)) else d3324 (change p 246 (some 247))) = d6401 p
  rw [sub11538, sub11529]
  rfl
theorem sub11540 (p : Pattern) : d3335 (change p 246 (some 247)) = d0 p := by
  change d0 (change p 246 (some 247)) = d0 p
  exact sub11422 p
theorem sub11541 (p : Pattern) : d3336 (change p 246 (some 247)) = d0 p := by
  change (if p 225 then d3226 (change p 246 (some 247)) else d3335 (change p 246 (some 247))) = d0 p
  rw [sub11424, sub11540]
  simp only [ite_self]
theorem sub11542 (p : Pattern) : d3337 (change p 246 (some 247)) = d0 p := by
  change (if p 224 then d3226 (change p 246 (some 247)) else d3336 (change p 246 (some 247))) = d0 p
  rw [sub11424, sub11541]
  simp only [ite_self]
theorem sub11543 (p : Pattern) : d3338 (change p 246 (some 247)) = d0 p := by
  change (if p 204 then d3226 (change p 246 (some 247)) else d3337 (change p 246 (some 247))) = d0 p
  rw [sub11424, sub11542]
  simp only [ite_self]
theorem sub11544 (p : Pattern) : d3339 (change p 246 (some 247)) = d6328 p := by
  change (if p 182 then d3230 (change p 246 (some 247)) else d3338 (change p 246 (some 247))) = d6328 p
  rw [sub11429, sub11543]
  rfl
theorem sub11545 (p : Pattern) : d3340 (change p 246 (some 247)) = d6328 p := by
  change (if p 163 then d3238 (change p 246 (some 247)) else d3339 (change p 246 (some 247))) = d6328 p
  rw [sub11437, sub11544]
  simp only [ite_self]
theorem sub11546 (p : Pattern) : d3341 (change p 246 (some 247)) = d6332 p := by
  change (if p 162 then d3242 (change p 246 (some 247)) else d3340 (change p 246 (some 247))) = d6332 p
  rw [sub11442, sub11545]
  rfl
theorem sub11547 (p : Pattern) : d3342 (change p 246 (some 247)) = d6337 p := by
  change (if p 161 then d3248 (change p 246 (some 247)) else d3341 (change p 246 (some 247))) = d6337 p
  rw [sub11449, sub11546]
  rfl
theorem sub11548 (p : Pattern) : d3343 (change p 246 (some 247)) = d6354 p := by
  change (if p 160 then d3268 (change p 246 (some 247)) else d3342 (change p 246 (some 247))) = d6354 p
  rw [sub11472, sub11547]
  rfl
theorem sub11549 (p : Pattern) : d3344 (change p 246 (some 247)) = d6356 p := by
  change (if p 163 then d3275 (change p 246 (some 247)) else d3236 (change p 246 (some 247))) = d6356 p
  rw [sub11479, sub11435]
  rfl
theorem sub11550 (p : Pattern) : d3345 (change p 246 (some 247)) = d6358 p := by
  change (if p 162 then d3277 (change p 246 (some 247)) else d3344 (change p 246 (some 247))) = d6358 p
  rw [sub11481, sub11549]
  rfl
theorem sub11551 (p : Pattern) : d3346 (change p 246 (some 247)) = d6365 p := by
  change (if p 161 then d3285 (change p 246 (some 247)) else d3345 (change p 246 (some 247))) = d6365 p
  rw [sub11490, sub11550]
  rfl
theorem sub11552 (p : Pattern) : d3347 (change p 246 (some 247)) = d6376 p := by
  change (if p 160 then d3296 (change p 246 (some 247)) else d3346 (change p 246 (some 247))) = d6376 p
  rw [sub11501, sub11551]
  rfl
theorem sub11553 (p : Pattern) : d3348 (change p 246 (some 247)) = d6377 p := by
  change (if p 141 then d3347 (change p 246 (some 247)) else d3343 (change p 246 (some 247))) = d6377 p
  rw [sub11552, sub11548]
  rfl
theorem sub11554 (p : Pattern) : d3349 (change p 246 (some 247)) = d6388 p := by
  change (if p 138 then d3313 (change p 246 (some 247)) else d3348 (change p 246 (some 247))) = d6388 p
  rw [sub11518, sub11553]
  rfl
theorem sub11555 (p : Pattern) : d3350 (change p 246 (some 247)) = d6398 p := by
  change (if p 116 then d3323 (change p 246 (some 247)) else d3349 (change p 246 (some 247))) = d6398 p
  rw [sub11528, sub11554]
  rfl
theorem sub11556 (p : Pattern) : d3351 (change p 246 (some 247)) = d6354 p := by
  change (if p 160 then d3268 (change p 246 (some 247)) else d3300 (change p 246 (some 247))) = d6354 p
  rw [sub11472, sub11505]
  rfl
theorem sub11557 (p : Pattern) : d3352 (change p 246 (some 247)) = d6377 p := by
  change (if p 141 then d3329 (change p 246 (some 247)) else d3351 (change p 246 (some 247))) = d6377 p
  rw [sub11534, sub11556]
  rfl
theorem sub11558 (p : Pattern) : d3353 (change p 246 (some 247)) = d6388 p := by
  change (if p 138 then d3313 (change p 246 (some 247)) else d3352 (change p 246 (some 247))) = d6388 p
  rw [sub11518, sub11557]
  rfl
theorem sub11559 (p : Pattern) : d3354 (change p 246 (some 247)) = d6400 p := by
  change (if p 116 then d3332 (change p 246 (some 247)) else d3353 (change p 246 (some 247))) = d6400 p
  rw [sub11537, sub11558]
  rfl
theorem sub11560 (p : Pattern) : d3355 (change p 246 (some 247)) = d6401 p := by
  change (if p 115 then d3354 (change p 246 (some 247)) else d3350 (change p 246 (some 247))) = d6401 p
  rw [sub11559, sub11555]
  rfl
theorem sub11561 (p : Pattern) : d3356 (change p 246 (some 247)) = d6401 p := by
  change (if p 71 then d3355 (change p 246 (some 247)) else d3334 (change p 246 (some 247))) = d6401 p
  rw [sub11560, sub11539]
  simp only [ite_self]
theorem sub11562 (p : Pattern) : d1 (change p 246 (some 247)) = d1 p := by
  rfl
theorem sub11563 (p : Pattern) : d3357 (change p 246 (some 247)) = d1 p := by
  change d1 (change p 246 (some 247)) = d1 p
  exact sub11562 p
theorem sub11564 (p : Pattern) : d3358 (change p 246 (some 247)) = d1 p := by
  change d1 (change p 246 (some 247)) = d1 p
  exact sub11562 p
theorem sub11565 (p : Pattern) : d3359 (change p 246 (some 247)) = d1 p := by
  change (if p 225 then d3358 (change p 246 (some 247)) else d3357 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11563]
  simp only [ite_self]
theorem sub11566 (p : Pattern) : d3360 (change p 246 (some 247)) = d1 p := by
  change (if p 224 then d3358 (change p 246 (some 247)) else d3359 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11565]
  simp only [ite_self]
theorem sub11567 (p : Pattern) : d3361 (change p 246 (some 247)) = d1 p := by
  change (if p 204 then d3358 (change p 246 (some 247)) else d3360 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11566]
  simp only [ite_self]
theorem sub11568 (p : Pattern) : d3362 (change p 246 (some 247)) = d6402 p := by
  change (if p 204 then d12 (change p 246 (some 247)) else d3358 (change p 246 (some 247))) = d6402 p
  rw [sub11428, sub11564]
  rfl
theorem sub11569 (p : Pattern) : d3363 (change p 246 (some 247)) = d6403 p := by
  change (if p 182 then d3362 (change p 246 (some 247)) else d3361 (change p 246 (some 247))) = d6403 p
  rw [sub11568, sub11567]
  rfl
theorem sub11570 (p : Pattern) : d3364 (change p 246 (some 247)) = d6403 p := by
  change (if p 182 then d3362 (change p 246 (some 247)) else d3358 (change p 246 (some 247))) = d6403 p
  rw [sub11568, sub11564]
  rfl
theorem sub11571 (p : Pattern) : d3365 (change p 246 (some 247)) = d6403 p := by
  change (if p 163 then d3364 (change p 246 (some 247)) else d3363 (change p 246 (some 247))) = d6403 p
  rw [sub11570, sub11569]
  simp only [ite_self]
theorem sub11572 (p : Pattern) : d5 (change p 246 (some 247)) = d5 p := by
  rfl
theorem sub11573 (p : Pattern) : d3366 (change p 246 (some 247)) = d5 p := by
  change d5 (change p 246 (some 247)) = d5 p
  exact sub11572 p
theorem sub11574 (p : Pattern) : d3367 (change p 246 (some 247)) = d6404 p := by
  change (if p 204 then d12 (change p 246 (some 247)) else d3366 (change p 246 (some 247))) = d6404 p
  rw [sub11428, sub11573]
  rfl
theorem sub11575 (p : Pattern) : d3368 (change p 246 (some 247)) = d6405 p := by
  change (if p 182 then d3367 (change p 246 (some 247)) else d3366 (change p 246 (some 247))) = d6405 p
  rw [sub11574, sub11573]
  rfl
theorem sub11576 (p : Pattern) : d3369 (change p 246 (some 247)) = d6406 p := by
  change (if p 163 then d3368 (change p 246 (some 247)) else d3364 (change p 246 (some 247))) = d6406 p
  rw [sub11575, sub11570]
  rfl
theorem sub11577 (p : Pattern) : d3370 (change p 246 (some 247)) = d6407 p := by
  change (if p 162 then d3369 (change p 246 (some 247)) else d3365 (change p 246 (some 247))) = d6407 p
  rw [sub11576, sub11571]
  rfl
theorem sub11578 (p : Pattern) : d3371 (change p 246 (some 247)) = d6408 p := by
  change (if p 163 then d12 (change p 246 (some 247)) else d3281 (change p 246 (some 247))) = d6408 p
  rw [sub11428, sub11486]
  rfl
theorem sub11579 (p : Pattern) : d3372 (change p 246 (some 247)) = d6409 p := by
  change (if p 162 then d3371 (change p 246 (some 247)) else d3369 (change p 246 (some 247))) = d6409 p
  rw [sub11578, sub11576]
  rfl
theorem sub11580 (p : Pattern) : d3373 (change p 246 (some 247)) = d6410 p := by
  change (if p 161 then d3372 (change p 246 (some 247)) else d3370 (change p 246 (some 247))) = d6410 p
  rw [sub11579, sub11577]
  rfl
theorem sub11581 (p : Pattern) : d3 (change p 246 (some 247)) = d3 p := by
  rfl
theorem sub11582 (p : Pattern) : d3374 (change p 246 (some 247)) = d3 p := by
  change d3 (change p 246 (some 247)) = d3 p
  exact sub11581 p
theorem sub11583 (p : Pattern) : d3375 (change p 246 (some 247)) = d6411 p := by
  change (if p 204 then d12 (change p 246 (some 247)) else d3374 (change p 246 (some 247))) = d6411 p
  rw [sub11428, sub11582]
  rfl
theorem sub11584 (p : Pattern) : d3376 (change p 246 (some 247)) = d6412 p := by
  change (if p 182 then d3375 (change p 246 (some 247)) else d3358 (change p 246 (some 247))) = d6412 p
  rw [sub11583, sub11564]
  rfl
theorem sub11585 (p : Pattern) : d7 (change p 246 (some 247)) = d7 p := by
  rfl
theorem sub11586 (p : Pattern) : d3377 (change p 246 (some 247)) = d7 p := by
  change d7 (change p 246 (some 247)) = d7 p
  exact sub11585 p
theorem sub11587 (p : Pattern) : d3378 (change p 246 (some 247)) = d6413 p := by
  change (if p 204 then d12 (change p 246 (some 247)) else d3377 (change p 246 (some 247))) = d6413 p
  rw [sub11428, sub11586]
  rfl
theorem sub11588 (p : Pattern) : d3379 (change p 246 (some 247)) = d6414 p := by
  change (if p 182 then d3378 (change p 246 (some 247)) else d3358 (change p 246 (some 247))) = d6414 p
  rw [sub11587, sub11564]
  rfl
theorem sub11589 (p : Pattern) : d3380 (change p 246 (some 247)) = d6415 p := by
  change (if p 163 then d3379 (change p 246 (some 247)) else d3376 (change p 246 (some 247))) = d6415 p
  rw [sub11588, sub11584]
  rfl
theorem sub11590 (p : Pattern) : d3381 (change p 246 (some 247)) = d6416 p := by
  change (if p 182 then d12 (change p 246 (some 247)) else d3358 (change p 246 (some 247))) = d6416 p
  rw [sub11428, sub11564]
  rfl
theorem sub11591 (p : Pattern) : d3382 (change p 246 (some 247)) = d6417 p := by
  change (if p 182 then d12 (change p 246 (some 247)) else d3366 (change p 246 (some 247))) = d6417 p
  rw [sub11428, sub11573]
  rfl
theorem sub11592 (p : Pattern) : d3383 (change p 246 (some 247)) = d6418 p := by
  change (if p 163 then d3382 (change p 246 (some 247)) else d3381 (change p 246 (some 247))) = d6418 p
  rw [sub11591, sub11590]
  rfl
theorem sub11593 (p : Pattern) : d3384 (change p 246 (some 247)) = d6419 p := by
  change (if p 162 then d3383 (change p 246 (some 247)) else d3380 (change p 246 (some 247))) = d6419 p
  rw [sub11592, sub11589]
  rfl
theorem sub11594 (p : Pattern) : d3385 (change p 246 (some 247)) = d6420 p := by
  change (if p 163 then d12 (change p 246 (some 247)) else d3291 (change p 246 (some 247))) = d6420 p
  rw [sub11428, sub11496]
  rfl
theorem sub11595 (p : Pattern) : d3386 (change p 246 (some 247)) = d6421 p := by
  change (if p 162 then d3385 (change p 246 (some 247)) else d3383 (change p 246 (some 247))) = d6421 p
  rw [sub11594, sub11592]
  rfl
theorem sub11596 (p : Pattern) : d3387 (change p 246 (some 247)) = d6422 p := by
  change (if p 161 then d3386 (change p 246 (some 247)) else d3384 (change p 246 (some 247))) = d6422 p
  rw [sub11595, sub11593]
  rfl
theorem sub11597 (p : Pattern) : d3388 (change p 246 (some 247)) = d6423 p := by
  change (if p 160 then d3387 (change p 246 (some 247)) else d3373 (change p 246 (some 247))) = d6423 p
  rw [sub11596, sub11580]
  rfl
theorem sub11598 (p : Pattern) : d3389 (change p 246 (some 247)) = d1 p := by
  change d1 (change p 246 (some 247)) = d1 p
  exact sub11562 p
theorem sub11599 (p : Pattern) : d3390 (change p 246 (some 247)) = d1 p := by
  change (if p 225 then d3358 (change p 246 (some 247)) else d3389 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11598]
  simp only [ite_self]
theorem sub11600 (p : Pattern) : d3391 (change p 246 (some 247)) = d1 p := by
  change (if p 224 then d3358 (change p 246 (some 247)) else d3390 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11599]
  simp only [ite_self]
theorem sub11601 (p : Pattern) : d3392 (change p 246 (some 247)) = d1 p := by
  change (if p 204 then d3358 (change p 246 (some 247)) else d3391 (change p 246 (some 247))) = d1 p
  rw [sub11564, sub11600]
  simp only [ite_self]
theorem sub11602 (p : Pattern) : d3393 (change p 246 (some 247)) = d6403 p := by
  change (if p 182 then d3362 (change p 246 (some 247)) else d3392 (change p 246 (some 247))) = d6403 p
  rw [sub11568, sub11601]
  rfl
theorem sub11603 (p : Pattern) : d3394 (change p 246 (some 247)) = d6424 p := by
  change (if p 182 then d3375 (change p 246 (some 247)) else d3374 (change p 246 (some 247))) = d6424 p
  rw [sub11583, sub11582]
  rfl
theorem sub11604 (p : Pattern) : d3395 (change p 246 (some 247)) = d6425 p := by
  change (if p 163 then d3394 (change p 246 (some 247)) else d3393 (change p 246 (some 247))) = d6425 p
  rw [sub11603, sub11602]
  rfl
theorem sub11605 (p : Pattern) : d3396 (change p 246 (some 247)) = d6426 p := by
  change (if p 163 then d3281 (change p 246 (some 247)) else d3368 (change p 246 (some 247))) = d6426 p
  rw [sub11486, sub11575]
  rfl
theorem sub11606 (p : Pattern) : d3397 (change p 246 (some 247)) = d6427 p := by
  change (if p 162 then d3396 (change p 246 (some 247)) else d3395 (change p 246 (some 247))) = d6427 p
  rw [sub11605, sub11604]
  rfl
theorem sub11607 (p : Pattern) : d3398 (change p 246 (some 247)) = d6428 p := by
  change (if p 163 then d3283 (change p 246 (some 247)) else d3368 (change p 246 (some 247))) = d6428 p
  rw [sub11488, sub11575]
  rfl
theorem sub11608 (p : Pattern) : d3399 (change p 246 (some 247)) = d6429 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3398 (change p 246 (some 247))) = d6429 p
  rw [sub11428, sub11607]
  rfl
theorem sub11609 (p : Pattern) : d3400 (change p 246 (some 247)) = d6430 p := by
  change (if p 161 then d3399 (change p 246 (some 247)) else d3397 (change p 246 (some 247))) = d6430 p
  rw [sub11608, sub11606]
  rfl
theorem sub11610 (p : Pattern) : d3401 (change p 246 (some 247)) = d6431 p := by
  change (if p 182 then d12 (change p 246 (some 247)) else d3374 (change p 246 (some 247))) = d6431 p
  rw [sub11428, sub11582]
  rfl
theorem sub11611 (p : Pattern) : d3402 (change p 246 (some 247)) = d6432 p := by
  change (if p 163 then d3401 (change p 246 (some 247)) else d3379 (change p 246 (some 247))) = d6432 p
  rw [sub11610, sub11588]
  rfl
theorem sub11612 (p : Pattern) : d3403 (change p 246 (some 247)) = d6433 p := by
  change (if p 163 then d3291 (change p 246 (some 247)) else d3382 (change p 246 (some 247))) = d6433 p
  rw [sub11496, sub11591]
  rfl
theorem sub11613 (p : Pattern) : d3404 (change p 246 (some 247)) = d6434 p := by
  change (if p 162 then d3403 (change p 246 (some 247)) else d3402 (change p 246 (some 247))) = d6434 p
  rw [sub11612, sub11611]
  rfl
theorem sub11614 (p : Pattern) : d3405 (change p 246 (some 247)) = d6435 p := by
  change (if p 163 then d3293 (change p 246 (some 247)) else d3382 (change p 246 (some 247))) = d6435 p
  rw [sub11498, sub11591]
  rfl
theorem sub11615 (p : Pattern) : d3406 (change p 246 (some 247)) = d6436 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3405 (change p 246 (some 247))) = d6436 p
  rw [sub11428, sub11614]
  rfl
theorem sub11616 (p : Pattern) : d3407 (change p 246 (some 247)) = d6437 p := by
  change (if p 161 then d3406 (change p 246 (some 247)) else d3404 (change p 246 (some 247))) = d6437 p
  rw [sub11615, sub11613]
  rfl
theorem sub11617 (p : Pattern) : d3408 (change p 246 (some 247)) = d6438 p := by
  change (if p 160 then d3407 (change p 246 (some 247)) else d3400 (change p 246 (some 247))) = d6438 p
  rw [sub11616, sub11609]
  rfl
theorem sub11618 (p : Pattern) : d3409 (change p 246 (some 247)) = d6439 p := by
  change (if p 141 then d3408 (change p 246 (some 247)) else d3388 (change p 246 (some 247))) = d6439 p
  rw [sub11617, sub11597]
  rfl
theorem sub11619 (p : Pattern) : d3410 (change p 246 (some 247)) = d6407 p := by
  change (if p 162 then d3369 (change p 246 (some 247)) else d3364 (change p 246 (some 247))) = d6407 p
  rw [sub11576, sub11570]
  rfl
theorem sub11620 (p : Pattern) : d3411 (change p 246 (some 247)) = d6410 p := by
  change (if p 161 then d3372 (change p 246 (some 247)) else d3410 (change p 246 (some 247))) = d6410 p
  rw [sub11579, sub11619]
  rfl
theorem sub11621 (p : Pattern) : d3412 (change p 246 (some 247)) = d6440 p := by
  change (if p 182 then d3378 (change p 246 (some 247)) else d3377 (change p 246 (some 247))) = d6440 p
  rw [sub11587, sub11586]
  rfl
theorem sub11622 (p : Pattern) : d3413 (change p 246 (some 247)) = d6441 p := by
  change (if p 163 then d3412 (change p 246 (some 247)) else d3394 (change p 246 (some 247))) = d6441 p
  rw [sub11621, sub11603]
  rfl
theorem sub11623 (p : Pattern) : d3414 (change p 246 (some 247)) = d6442 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3413 (change p 246 (some 247))) = d6442 p
  rw [sub11428, sub11622]
  rfl
theorem sub11624 (p : Pattern) : d3415 (change p 246 (some 247)) = d6443 p := by
  change (if p 161 then d12 (change p 246 (some 247)) else d3414 (change p 246 (some 247))) = d6443 p
  rw [sub11428, sub11623]
  rfl
theorem sub11625 (p : Pattern) : d3416 (change p 246 (some 247)) = d6444 p := by
  change (if p 160 then d3415 (change p 246 (some 247)) else d3411 (change p 246 (some 247))) = d6444 p
  rw [sub11624, sub11620]
  rfl
theorem sub11626 (p : Pattern) : d3417 (change p 246 (some 247)) = d6425 p := by
  change (if p 163 then d3394 (change p 246 (some 247)) else d3364 (change p 246 (some 247))) = d6425 p
  rw [sub11603, sub11570]
  rfl
theorem sub11627 (p : Pattern) : d3418 (change p 246 (some 247)) = d6427 p := by
  change (if p 162 then d3396 (change p 246 (some 247)) else d3417 (change p 246 (some 247))) = d6427 p
  rw [sub11605, sub11626]
  rfl
theorem sub11628 (p : Pattern) : d3419 (change p 246 (some 247)) = d6430 p := by
  change (if p 161 then d3399 (change p 246 (some 247)) else d3418 (change p 246 (some 247))) = d6430 p
  rw [sub11608, sub11627]
  rfl
theorem sub11629 (p : Pattern) : d3420 (change p 246 (some 247)) = d6445 p := by
  change (if p 163 then d12 (change p 246 (some 247)) else d3412 (change p 246 (some 247))) = d6445 p
  rw [sub11428, sub11621]
  rfl
theorem sub11630 (p : Pattern) : d3421 (change p 246 (some 247)) = d6446 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3420 (change p 246 (some 247))) = d6446 p
  rw [sub11428, sub11629]
  rfl
theorem sub11631 (p : Pattern) : d3422 (change p 246 (some 247)) = d6447 p := by
  change (if p 161 then d12 (change p 246 (some 247)) else d3421 (change p 246 (some 247))) = d6447 p
  rw [sub11428, sub11630]
  rfl
theorem sub11632 (p : Pattern) : d3423 (change p 246 (some 247)) = d6448 p := by
  change (if p 160 then d3422 (change p 246 (some 247)) else d3419 (change p 246 (some 247))) = d6448 p
  rw [sub11631, sub11628]
  rfl
theorem sub11633 (p : Pattern) : d3424 (change p 246 (some 247)) = d6449 p := by
  change (if p 141 then d3423 (change p 246 (some 247)) else d3416 (change p 246 (some 247))) = d6449 p
  rw [sub11632, sub11625]
  rfl
theorem sub11634 (p : Pattern) : d3425 (change p 246 (some 247)) = d6450 p := by
  change (if p 138 then d3424 (change p 246 (some 247)) else d3409 (change p 246 (some 247))) = d6450 p
  rw [sub11633, sub11618]
  rfl
theorem sub11635 (p : Pattern) : d3426 (change p 246 (some 247)) = d6451 p := by
  change (if p 162 then d12 (change p 246 (some 247)) else d3371 (change p 246 (some 247))) = d6451 p
  rw [sub11428, sub11578]
  rfl
theorem sub11636 (p : Pattern) : d3427 (change p 246 (some 247)) = d6452 p := by
  change (if p 161 then d12 (change p 246 (some 247)) else d3426 (change p 246 (some 247))) = d6452 p
  rw [sub11428, sub11635]
  rfl
theorem sub11637 (p : Pattern) : d3428 (change p 246 (some 247)) = d6453 p := by
  change (if p 160 then d12 (change p 246 (some 247)) else d3427 (change p 246 (some 247))) = d6453 p
  rw [sub11428, sub11636]
  rfl
theorem sub11638 (p : Pattern) : d3429 (change p 246 (some 247)) = d6454 p := by
  change (if p 141 then d12 (change p 246 (some 247)) else d3428 (change p 246 (some 247))) = d6454 p
  rw [sub11428, sub11637]
  rfl
theorem sub11639 (p : Pattern) : d3430 (change p 246 (some 247)) = d6455 p := by
  change (if p 138 then d3429 (change p 246 (some 247)) else d3424 (change p 246 (some 247))) = d6455 p
  rw [sub11638, sub11633]
  rfl
end NetHack.Sokoban22Refined85
