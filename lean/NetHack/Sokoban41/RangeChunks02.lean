/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.RangeChunks01
namespace NetHack.Sokoban41.Diagram
theorem range360 (pattern : Ten) : 0 ≤ d360 pattern ∧ d360 pattern ≤ 10 := by
  unfold d360
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range361 (pattern : Ten) : 0 ≤ d361 pattern ∧ d361 pattern ≤ 10 := by
  unfold d361
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range362 (pattern : Ten) : 0 ≤ d362 pattern ∧ d362 pattern ≤ 10 := by
  unfold d362
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range363 (pattern : Ten) : 0 ≤ d363 pattern ∧ d363 pattern ≤ 10 := by
  unfold d363
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range364 (pattern : Ten) : 0 ≤ d364 pattern ∧ d364 pattern ≤ 10 := by
  unfold d364
  split
  · exact range355 pattern
  · exact range0 pattern
theorem range365 (pattern : Ten) : 0 ≤ d365 pattern ∧ d365 pattern ≤ 10 := by
  unfold d365
  split
  · exact range353 pattern
  · exact range1 pattern
theorem range366 (pattern : Ten) : 0 ≤ d366 pattern ∧ d366 pattern ≤ 10 := by
  unfold d366
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range367 (pattern : Ten) : 0 ≤ d367 pattern ∧ d367 pattern ≤ 10 := by
  unfold d367
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range368 (pattern : Ten) : 0 ≤ d368 pattern ∧ d368 pattern ≤ 10 := by
  unfold d368
  split
  · exact range0 pattern
  · exact range354 pattern
theorem range369 (pattern : Ten) : 0 ≤ d369 pattern ∧ d369 pattern ≤ 10 := by
  unfold d369
  split
  · exact range368 pattern
  · exact range367 pattern
theorem range370 (pattern : Ten) : 0 ≤ d370 pattern ∧ d370 pattern ≤ 10 := by
  unfold d370
  split
  · exact range0 pattern
  · exact range353 pattern
theorem range371 (pattern : Ten) : 0 ≤ d371 pattern ∧ d371 pattern ≤ 10 := by
  unfold d371
  split
  · exact range370 pattern
  · exact range366 pattern
theorem range372 (pattern : Ten) : 0 ≤ d372 pattern ∧ d372 pattern ≤ 10 := by
  unfold d372
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range373 (pattern : Ten) : 0 ≤ d373 pattern ∧ d373 pattern ≤ 10 := by
  unfold d373
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range374 (pattern : Ten) : 0 ≤ d374 pattern ∧ d374 pattern ≤ 10 := by
  unfold d374
  split
  · exact range0 pattern
  · exact range373 pattern
theorem range375 (pattern : Ten) : 0 ≤ d375 pattern ∧ d375 pattern ≤ 10 := by
  unfold d375
  split
  · exact range0 pattern
  · exact range372 pattern
theorem range376 (pattern : Ten) : 0 ≤ d376 pattern ∧ d376 pattern ≤ 10 := by
  unfold d376
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range377 (pattern : Ten) : 0 ≤ d377 pattern ∧ d377 pattern ≤ 10 := by
  unfold d377
  split
  · exact range0 pattern
  · exact range354 pattern
theorem range378 (pattern : Ten) : 0 ≤ d378 pattern ∧ d378 pattern ≤ 10 := by
  unfold d378
  split
  · exact range0 pattern
  · exact range353 pattern
theorem range379 (pattern : Ten) : 0 ≤ d379 pattern ∧ d379 pattern ≤ 10 := by
  unfold d379
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range380 (pattern : Ten) : 0 ≤ d380 pattern ∧ d380 pattern ≤ 10 := by
  unfold d380
  split
  · exact range379 pattern
  · exact range0 pattern
theorem range381 (pattern : Ten) : 0 ≤ d381 pattern ∧ d381 pattern ≤ 10 := by
  unfold d381
  split
  · exact range350 pattern
  · exact range1 pattern
theorem range382 (pattern : Ten) : 0 ≤ d382 pattern ∧ d382 pattern ≤ 10 := by
  unfold d382
  split
  · exact range0 pattern
  · exact range381 pattern
theorem range383 (pattern : Ten) : 0 ≤ d383 pattern ∧ d383 pattern ≤ 10 := by
  unfold d383
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range384 (pattern : Ten) : 0 ≤ d384 pattern ∧ d384 pattern ≤ 10 := by
  unfold d384
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range385 (pattern : Ten) : 0 ≤ d385 pattern ∧ d385 pattern ≤ 10 := by
  unfold d385
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range386 (pattern : Ten) : 0 ≤ d386 pattern ∧ d386 pattern ≤ 10 := by
  unfold d386
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range387 (pattern : Ten) : 0 ≤ d387 pattern ∧ d387 pattern ≤ 10 := by
  unfold d387
  split
  · exact range0 pattern
  · exact range384 pattern
theorem range388 (pattern : Ten) : 0 ≤ d388 pattern ∧ d388 pattern ≤ 10 := by
  unfold d388
  split
  · exact range0 pattern
  · exact range383 pattern
theorem range389 (pattern : Ten) : 0 ≤ d389 pattern ∧ d389 pattern ≤ 10 := by
  unfold d389
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range390 (pattern : Ten) : 0 ≤ d390 pattern ∧ d390 pattern ≤ 10 := by
  unfold d390
  split
  · exact range0 pattern
  · exact range389 pattern
theorem range391 (pattern : Ten) : 0 ≤ d391 pattern ∧ d391 pattern ≤ 10 := by
  unfold d391
  split
  · exact range0 pattern
  · exact range386 pattern
theorem range392 (pattern : Ten) : 0 ≤ d392 pattern ∧ d392 pattern ≤ 10 := by
  unfold d392
  split
  · exact range0 pattern
  · exact range367 pattern
theorem range393 (pattern : Ten) : 0 ≤ d393 pattern ∧ d393 pattern ≤ 10 := by
  unfold d393
  split
  · exact range0 pattern
  · exact range366 pattern
theorem range394 (pattern : Ten) : 0 ≤ d394 pattern ∧ d394 pattern ≤ 10 := by
  unfold d394
  split
  · exact range0 pattern
  · exact range1 pattern
theorem range395 (pattern : Ten) : 0 ≤ d395 pattern ∧ d395 pattern ≤ 10 := by
  unfold d395
  split
  · exact range0 pattern
  · exact range350 pattern
theorem range396 (pattern : Ten) : 0 ≤ d396 pattern ∧ d396 pattern ≤ 10 := by
  unfold d396
  split
  · exact range0 pattern
  · exact range395 pattern
theorem range397 (pattern : Ten) : 0 ≤ d397 pattern ∧ d397 pattern ≤ 10 := by
  unfold d397
  split
  · exact range0 pattern
  · exact range395 pattern
theorem range398 (pattern : Ten) : 0 ≤ d398 pattern ∧ d398 pattern ≤ 10 := by
  unfold d398
  split
  · exact range0 pattern
  · exact range397 pattern
theorem range399 (pattern : Ten) : 0 ≤ d399 pattern ∧ d399 pattern ≤ 10 := by
  unfold d399
  split
  · exact range0 pattern
  · exact range394 pattern
theorem range400 (pattern : Ten) : 0 ≤ d400 pattern ∧ d400 pattern ≤ 10 := by
  unfold d400
  split
  · exact range0 pattern
  · exact range394 pattern
theorem range401 (pattern : Ten) : 0 ≤ d401 pattern ∧ d401 pattern ≤ 10 := by
  unfold d401
  split
  · exact range0 pattern
  · exact range400 pattern
theorem range402 (pattern : Ten) : 0 ≤ d402 pattern ∧ d402 pattern ≤ 10 := by
  unfold d402
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range403 (pattern : Ten) : 0 ≤ d403 pattern ∧ d403 pattern ≤ 10 := by
  unfold d403
  split
  · exact range379 pattern
  · exact range0 pattern
theorem range404 (pattern : Ten) : 0 ≤ d404 pattern ∧ d404 pattern ≤ 10 := by
  unfold d404
  split
  · exact range350 pattern
  · exact range1 pattern
theorem range405 (pattern : Ten) : 0 ≤ d405 pattern ∧ d405 pattern ≤ 10 := by
  unfold d405
  split
  · exact range0 pattern
  · exact range404 pattern
theorem range406 (pattern : Ten) : 0 ≤ d406 pattern ∧ d406 pattern ≤ 10 := by
  unfold d406
  split
  · exact range356 pattern
  · exact range0 pattern
theorem range407 (pattern : Ten) : 0 ≤ d407 pattern ∧ d407 pattern ≤ 10 := by
  unfold d407
  split
  · exact range0 pattern
  · exact range406 pattern
theorem range408 (pattern : Ten) : 0 ≤ d408 pattern ∧ d408 pattern ≤ 10 := by
  unfold d408
  split
  · exact range26 pattern
  · exact range23 pattern
theorem range409 (pattern : Ten) : 0 ≤ d409 pattern ∧ d409 pattern ≤ 10 := by
  unfold d409
  split
  · exact range227 pattern
  · exact range408 pattern
theorem range410 (pattern : Ten) : 0 ≤ d410 pattern ∧ d410 pattern ≤ 10 := by
  unfold d410
  split
  · exact range231 pattern
  · exact range409 pattern
theorem range411 (pattern : Ten) : 0 ≤ d411 pattern ∧ d411 pattern ≤ 10 := by
  unfold d411
  split
  · exact range233 pattern
  · exact range410 pattern
theorem range412 (pattern : Ten) : 0 ≤ d412 pattern ∧ d412 pattern ≤ 10 := by
  unfold d412
  split
  · exact range10 pattern
  · exact range1 pattern
theorem range413 (pattern : Ten) : 0 ≤ d413 pattern ∧ d413 pattern ≤ 10 := by
  unfold d413
  split
  · exact range412 pattern
  · exact range1 pattern
theorem range414 (pattern : Ten) : 0 ≤ d414 pattern ∧ d414 pattern ≤ 10 := by
  unfold d414
  split
  · exact range10 pattern
  · exact range412 pattern
theorem range415 (pattern : Ten) : 0 ≤ d415 pattern ∧ d415 pattern ≤ 10 := by
  unfold d415
  split
  · exact range414 pattern
  · exact range413 pattern
theorem range416 (pattern : Ten) : 0 ≤ d416 pattern ∧ d416 pattern ≤ 10 := by
  unfold d416
  split
  · exact range10 pattern
  · exact range414 pattern
theorem range417 (pattern : Ten) : 0 ≤ d417 pattern ∧ d417 pattern ≤ 10 := by
  unfold d417
  split
  · exact range416 pattern
  · exact range415 pattern
theorem range418 (pattern : Ten) : 0 ≤ d418 pattern ∧ d418 pattern ≤ 10 := by
  unfold d418
  split
  · exact range3 pattern
  · exact range1 pattern
theorem range419 (pattern : Ten) : 0 ≤ d419 pattern ∧ d419 pattern ≤ 10 := by
  unfold d419
  split
  · exact range10 pattern
  · exact range3 pattern
theorem range420 (pattern : Ten) : 0 ≤ d420 pattern ∧ d420 pattern ≤ 10 := by
  unfold d420
  split
  · exact range419 pattern
  · exact range418 pattern
theorem range421 (pattern : Ten) : 0 ≤ d421 pattern ∧ d421 pattern ≤ 10 := by
  unfold d421
  split
  · exact range10 pattern
  · exact range419 pattern
theorem range422 (pattern : Ten) : 0 ≤ d422 pattern ∧ d422 pattern ≤ 10 := by
  unfold d422
  split
  · exact range421 pattern
  · exact range420 pattern
theorem range423 (pattern : Ten) : 0 ≤ d423 pattern ∧ d423 pattern ≤ 10 := by
  unfold d423
  split
  · exact range416 pattern
  · exact range422 pattern
theorem range424 (pattern : Ten) : 0 ≤ d424 pattern ∧ d424 pattern ≤ 10 := by
  unfold d424
  split
  · exact range423 pattern
  · exact range417 pattern
theorem range425 (pattern : Ten) : 0 ≤ d425 pattern ∧ d425 pattern ≤ 10 := by
  unfold d425
  split
  · exact range10 pattern
  · exact range416 pattern
theorem range426 (pattern : Ten) : 0 ≤ d426 pattern ∧ d426 pattern ≤ 10 := by
  unfold d426
  split
  · exact range10 pattern
  · exact range421 pattern
theorem range427 (pattern : Ten) : 0 ≤ d427 pattern ∧ d427 pattern ≤ 10 := by
  unfold d427
  split
  · exact range10 pattern
  · exact range426 pattern
theorem range428 (pattern : Ten) : 0 ≤ d428 pattern ∧ d428 pattern ≤ 10 := by
  unfold d428
  split
  · exact range427 pattern
  · exact range425 pattern
theorem range429 (pattern : Ten) : 0 ≤ d429 pattern ∧ d429 pattern ≤ 10 := by
  unfold d429
  split
  · exact range428 pattern
  · exact range424 pattern
theorem range430 (pattern : Ten) : 0 ≤ d430 pattern ∧ d430 pattern ≤ 10 := by
  unfold d430
  split
  · exact range10 pattern
  · exact range428 pattern
theorem range431 (pattern : Ten) : 0 ≤ d431 pattern ∧ d431 pattern ≤ 10 := by
  unfold d431
  split
  · exact range430 pattern
  · exact range429 pattern
theorem range432 (pattern : Ten) : 0 ≤ d432 pattern ∧ d432 pattern ≤ 10 := by
  unfold d432
  split
  · exact range350 pattern
  · exact range0 pattern
theorem range433 (pattern : Ten) : 0 ≤ d433 pattern ∧ d433 pattern ≤ 10 := by
  unfold d433
  split
  · exact range0 pattern
  · exact range432 pattern
theorem range434 (pattern : Ten) : 0 ≤ d434 pattern ∧ d434 pattern ≤ 10 := by
  unfold d434
  split
  · exact range211 pattern
  · exact range207 pattern
theorem range435 (pattern : Ten) : 0 ≤ d435 pattern ∧ d435 pattern ≤ 10 := by
  unfold d435
  split
  · exact range237 pattern
  · exact range434 pattern
theorem range436 (pattern : Ten) : 0 ≤ d436 pattern ∧ d436 pattern ≤ 10 := by
  unfold d436
  split
  · exact range0 pattern
  · exact range355 pattern
theorem range437 (pattern : Ten) : 0 ≤ d437 pattern ∧ d437 pattern ≤ 10 := by
  unfold d437
  split
  · exact range60 pattern
  · exact range58 pattern
theorem range438 (pattern : Ten) : 0 ≤ d438 pattern ∧ d438 pattern ≤ 10 := by
  unfold d438
  split
  · exact range214 pattern
  · exact range211 pattern
theorem range439 (pattern : Ten) : 0 ≤ d439 pattern ∧ d439 pattern ≤ 10 := by
  unfold d439
  split
  · exact range58 pattern
  · exact range54 pattern
theorem range440 (pattern : Ten) : 0 ≤ d440 pattern ∧ d440 pattern ≤ 10 := by
  unfold d440
  split
  · exact range84 pattern
  · exact range439 pattern
theorem range441 (pattern : Ten) : 0 ≤ d441 pattern ∧ d441 pattern ≤ 10 := by
  unfold d441
  split
  · exact range27 pattern
  · exact range209 pattern
theorem range442 (pattern : Ten) : 0 ≤ d442 pattern ∧ d442 pattern ≤ 10 := by
  unfold d442
  split
  · exact range441 pattern
  · exact range209 pattern
theorem range443 (pattern : Ten) : 0 ≤ d443 pattern ∧ d443 pattern ≤ 10 := by
  unfold d443
  split
  · exact range217 pattern
  · exact range442 pattern
theorem range444 (pattern : Ten) : 0 ≤ d444 pattern ∧ d444 pattern ≤ 10 := by
  unfold d444
  split
  · exact range443 pattern
  · exact range218 pattern
theorem range445 (pattern : Ten) : 0 ≤ d445 pattern ∧ d445 pattern ≤ 10 := by
  unfold d445
  split
  · exact range0 pattern
  · exact range360 pattern
theorem range446 (pattern : Ten) : 0 ≤ d446 pattern ∧ d446 pattern ≤ 10 := by
  unfold d446
  split
  · exact range0 pattern
  · exact range360 pattern
theorem range447 (pattern : Ten) : 0 ≤ d447 pattern ∧ d447 pattern ≤ 10 := by
  unfold d447
  split
  · exact range0 pattern
  · exact range446 pattern
theorem range448 (pattern : Ten) : 0 ≤ d448 pattern ∧ d448 pattern ≤ 10 := by
  unfold d448
  split
  · exact range10 pattern
  · exact range106 pattern
theorem range449 (pattern : Ten) : 0 ≤ d449 pattern ∧ d449 pattern ≤ 10 := by
  unfold d449
  split
  · exact range10 pattern
  · exact range264 pattern
theorem range450 (pattern : Ten) : 0 ≤ d450 pattern ∧ d450 pattern ≤ 10 := by
  unfold d450
  split
  · exact range350 pattern
  · exact range0 pattern
theorem range451 (pattern : Ten) : 0 ≤ d451 pattern ∧ d451 pattern ≤ 10 := by
  unfold d451
  split
  · exact range0 pattern
  · exact range450 pattern
theorem range452 (pattern : Ten) : 0 ≤ d452 pattern ∧ d452 pattern ≤ 10 := by
  unfold d452
  split
  · exact range10 pattern
  · exact range0 pattern
theorem range453 (pattern : Ten) : 0 ≤ d453 pattern ∧ d453 pattern ≤ 10 := by
  unfold d453
  split
  · exact range10 pattern
  · exact range11 pattern
theorem range454 (pattern : Ten) : 0 ≤ d454 pattern ∧ d454 pattern ≤ 10 := by
  unfold d454
  split
  · exact range453 pattern
  · exact range452 pattern
theorem range455 (pattern : Ten) : 0 ≤ d455 pattern ∧ d455 pattern ≤ 10 := by
  unfold d455
  split
  · exact range10 pattern
  · exact range2 pattern
theorem range456 (pattern : Ten) : 0 ≤ d456 pattern ∧ d456 pattern ≤ 10 := by
  unfold d456
  split
  · exact range453 pattern
  · exact range455 pattern
theorem range457 (pattern : Ten) : 0 ≤ d457 pattern ∧ d457 pattern ≤ 10 := by
  unfold d457
  split
  · exact range456 pattern
  · exact range454 pattern
theorem range458 (pattern : Ten) : 0 ≤ d458 pattern ∧ d458 pattern ≤ 10 := by
  unfold d458
  split
  · exact range10 pattern
  · exact range457 pattern
theorem range459 (pattern : Ten) : 0 ≤ d459 pattern ∧ d459 pattern ≤ 10 := by
  unfold d459
  split
  · exact range10 pattern
  · exact range458 pattern
theorem range460 (pattern : Ten) : 0 ≤ d460 pattern ∧ d460 pattern ≤ 10 := by
  unfold d460
  split
  · exact range0 pattern
  · exact range385 pattern
theorem range461 (pattern : Ten) : 0 ≤ d461 pattern ∧ d461 pattern ≤ 10 := by
  unfold d461
  split
  · exact range10 pattern
  · exact range171 pattern
theorem range462 (pattern : Ten) : 0 ≤ d462 pattern ∧ d462 pattern ≤ 10 := by
  unfold d462
  split
  · exact range10 pattern
  · exact range461 pattern
theorem range463 (pattern : Ten) : 0 ≤ d463 pattern ∧ d463 pattern ≤ 10 := by
  unfold d463
  split
  · exact range10 pattern
  · exact range172 pattern
theorem range464 (pattern : Ten) : 0 ≤ d464 pattern ∧ d464 pattern ≤ 10 := by
  unfold d464
  split
  · exact range10 pattern
  · exact range463 pattern
theorem range465 (pattern : Ten) : 0 ≤ d465 pattern ∧ d465 pattern ≤ 10 := by
  unfold d465
  split
  · exact range464 pattern
  · exact range462 pattern
theorem range466 (pattern : Ten) : 0 ≤ d466 pattern ∧ d466 pattern ≤ 10 := by
  unfold d466
  split
  · exact range10 pattern
  · exact range465 pattern
theorem range467 (pattern : Ten) : 0 ≤ d467 pattern ∧ d467 pattern ≤ 10 := by
  unfold d467
  split
  · exact range10 pattern
  · exact range466 pattern
theorem range468 (pattern : Ten) : 0 ≤ d468 pattern ∧ d468 pattern ≤ 10 := by
  unfold d468
  split
  · exact range88 pattern
  · exact range0 pattern
theorem range469 (pattern : Ten) : 0 ≤ d469 pattern ∧ d469 pattern ≤ 10 := by
  unfold d469
  split
  · exact range94 pattern
  · exact range468 pattern
theorem range470 (pattern : Ten) : 0 ≤ d470 pattern ∧ d470 pattern ≤ 10 := by
  unfold d470
  split
  · exact range100 pattern
  · exact range469 pattern
theorem range471 (pattern : Ten) : 0 ≤ d471 pattern ∧ d471 pattern ≤ 10 := by
  unfold d471
  split
  · exact range104 pattern
  · exact range470 pattern
theorem range472 (pattern : Ten) : 0 ≤ d472 pattern ∧ d472 pattern ≤ 10 := by
  unfold d472
  split
  · exact range106 pattern
  · exact range471 pattern
theorem range473 (pattern : Ten) : 0 ≤ d473 pattern ∧ d473 pattern ≤ 10 := by
  unfold d473
  split
  · exact range250 pattern
  · exact range171 pattern
theorem range474 (pattern : Ten) : 0 ≤ d474 pattern ∧ d474 pattern ≤ 10 := by
  unfold d474
  split
  · exact range254 pattern
  · exact range473 pattern
theorem range475 (pattern : Ten) : 0 ≤ d475 pattern ∧ d475 pattern ≤ 10 := by
  unfold d475
  split
  · exact range258 pattern
  · exact range474 pattern
theorem range476 (pattern : Ten) : 0 ≤ d476 pattern ∧ d476 pattern ≤ 10 := by
  unfold d476
  split
  · exact range262 pattern
  · exact range475 pattern
theorem range477 (pattern : Ten) : 0 ≤ d477 pattern ∧ d477 pattern ≤ 10 := by
  unfold d477
  split
  · exact range264 pattern
  · exact range476 pattern
theorem range478 (pattern : Ten) : 0 ≤ d478 pattern ∧ d478 pattern ≤ 10 := by
  unfold d478
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range479 (pattern : Ten) : 0 ≤ d479 pattern ∧ d479 pattern ≤ 10 := by
  unfold d479
  split
  · exact range384 pattern
  · exact range0 pattern
theorem range480 (pattern : Ten) : 0 ≤ d480 pattern ∧ d480 pattern ≤ 10 := by
  unfold d480
  split
  · exact range0 pattern
  · exact range479 pattern
theorem range481 (pattern : Ten) : 0 ≤ d481 pattern ∧ d481 pattern ≤ 10 := by
  unfold d481
  split
  · exact range14 pattern
  · exact range15 pattern
theorem range482 (pattern : Ten) : 0 ≤ d482 pattern ∧ d482 pattern ≤ 10 := by
  unfold d482
  split
  · exact range14 pattern
  · exact range44 pattern
theorem range483 (pattern : Ten) : 0 ≤ d483 pattern ∧ d483 pattern ≤ 10 := by
  unfold d483
  split
  · exact range482 pattern
  · exact range481 pattern
theorem range484 (pattern : Ten) : 0 ≤ d484 pattern ∧ d484 pattern ≤ 10 := by
  unfold d484
  split
  · exact range10 pattern
  · exact range483 pattern
theorem range485 (pattern : Ten) : 0 ≤ d485 pattern ∧ d485 pattern ≤ 10 := by
  unfold d485
  split
  · exact range10 pattern
  · exact range484 pattern
theorem range486 (pattern : Ten) : 0 ≤ d486 pattern ∧ d486 pattern ≤ 10 := by
  unfold d486
  split
  · exact range383 pattern
  · exact range0 pattern
theorem range487 (pattern : Ten) : 0 ≤ d487 pattern ∧ d487 pattern ≤ 10 := by
  unfold d487
  split
  · exact range0 pattern
  · exact range486 pattern
theorem range488 (pattern : Ten) : 0 ≤ d488 pattern ∧ d488 pattern ≤ 10 := by
  unfold d488
  split
  · exact range10 pattern
  · exact range174 pattern
theorem range489 (pattern : Ten) : 0 ≤ d489 pattern ∧ d489 pattern ≤ 10 := by
  unfold d489
  split
  · exact range10 pattern
  · exact range199 pattern
theorem range490 (pattern : Ten) : 0 ≤ d490 pattern ∧ d490 pattern ≤ 10 := by
  unfold d490
  split
  · exact range489 pattern
  · exact range488 pattern
theorem range491 (pattern : Ten) : 0 ≤ d491 pattern ∧ d491 pattern ≤ 10 := by
  unfold d491
  split
  · exact range10 pattern
  · exact range490 pattern
theorem range492 (pattern : Ten) : 0 ≤ d492 pattern ∧ d492 pattern ≤ 10 := by
  unfold d492
  split
  · exact range10 pattern
  · exact range491 pattern
theorem range493 (pattern : Ten) : 0 ≤ d493 pattern ∧ d493 pattern ≤ 10 := by
  unfold d493
  split
  · exact range350 pattern
  · exact range0 pattern
theorem range494 (pattern : Ten) : 0 ≤ d494 pattern ∧ d494 pattern ≤ 10 := by
  unfold d494
  split
  · exact range0 pattern
  · exact range493 pattern
theorem range495 (pattern : Ten) : 0 ≤ d495 pattern ∧ d495 pattern ≤ 10 := by
  unfold d495
  split
  · exact range455 pattern
  · exact range2 pattern
theorem range496 (pattern : Ten) : 0 ≤ d496 pattern ∧ d496 pattern ≤ 10 := by
  unfold d496
  split
  · exact range4 pattern
  · exact range2 pattern
theorem range497 (pattern : Ten) : 0 ≤ d497 pattern ∧ d497 pattern ≤ 10 := by
  unfold d497
  split
  · exact range455 pattern
  · exact range496 pattern
theorem range498 (pattern : Ten) : 0 ≤ d498 pattern ∧ d498 pattern ≤ 10 := by
  unfold d498
  split
  · exact range497 pattern
  · exact range495 pattern
theorem range499 (pattern : Ten) : 0 ≤ d499 pattern ∧ d499 pattern ≤ 10 := by
  unfold d499
  split
  · exact range10 pattern
  · exact range455 pattern
theorem range500 (pattern : Ten) : 0 ≤ d500 pattern ∧ d500 pattern ≤ 10 := by
  unfold d500
  split
  · exact range10 pattern
  · exact range4 pattern
theorem range501 (pattern : Ten) : 0 ≤ d501 pattern ∧ d501 pattern ≤ 10 := by
  unfold d501
  split
  · exact range10 pattern
  · exact range500 pattern
theorem range502 (pattern : Ten) : 0 ≤ d502 pattern ∧ d502 pattern ≤ 10 := by
  unfold d502
  split
  · exact range501 pattern
  · exact range499 pattern
theorem range503 (pattern : Ten) : 0 ≤ d503 pattern ∧ d503 pattern ≤ 10 := by
  unfold d503
  split
  · exact range502 pattern
  · exact range498 pattern
theorem range504 (pattern : Ten) : 0 ≤ d504 pattern ∧ d504 pattern ≤ 10 := by
  unfold d504
  split
  · exact range10 pattern
  · exact range502 pattern
theorem range505 (pattern : Ten) : 0 ≤ d505 pattern ∧ d505 pattern ≤ 10 := by
  unfold d505
  split
  · exact range504 pattern
  · exact range503 pattern
theorem range506 (pattern : Ten) : 0 ≤ d506 pattern ∧ d506 pattern ≤ 10 := by
  unfold d506
  split
  · exact range0 pattern
  · exact range478 pattern
theorem range507 (pattern : Ten) : 0 ≤ d507 pattern ∧ d507 pattern ≤ 10 := by
  unfold d507
  split
  · exact range463 pattern
  · exact range172 pattern
theorem range508 (pattern : Ten) : 0 ≤ d508 pattern ∧ d508 pattern ≤ 10 := by
  unfold d508
  split
  · exact range193 pattern
  · exact range172 pattern
theorem range509 (pattern : Ten) : 0 ≤ d509 pattern ∧ d509 pattern ≤ 10 := by
  unfold d509
  split
  · exact range463 pattern
  · exact range508 pattern
theorem range510 (pattern : Ten) : 0 ≤ d510 pattern ∧ d510 pattern ≤ 10 := by
  unfold d510
  split
  · exact range509 pattern
  · exact range507 pattern
theorem range511 (pattern : Ten) : 0 ≤ d511 pattern ∧ d511 pattern ≤ 10 := by
  unfold d511
  split
  · exact range10 pattern
  · exact range193 pattern
theorem range512 (pattern : Ten) : 0 ≤ d512 pattern ∧ d512 pattern ≤ 10 := by
  unfold d512
  split
  · exact range10 pattern
  · exact range511 pattern
theorem range513 (pattern : Ten) : 0 ≤ d513 pattern ∧ d513 pattern ≤ 10 := by
  unfold d513
  split
  · exact range512 pattern
  · exact range464 pattern
theorem range514 (pattern : Ten) : 0 ≤ d514 pattern ∧ d514 pattern ≤ 10 := by
  unfold d514
  split
  · exact range513 pattern
  · exact range510 pattern
theorem range515 (pattern : Ten) : 0 ≤ d515 pattern ∧ d515 pattern ≤ 10 := by
  unfold d515
  split
  · exact range10 pattern
  · exact range513 pattern
theorem range516 (pattern : Ten) : 0 ≤ d516 pattern ∧ d516 pattern ≤ 10 := by
  unfold d516
  split
  · exact range515 pattern
  · exact range514 pattern
theorem range517 (pattern : Ten) : 0 ≤ d517 pattern ∧ d517 pattern ≤ 10 := by
  unfold d517
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range518 (pattern : Ten) : 0 ≤ d518 pattern ∧ d518 pattern ≤ 10 := by
  unfold d518
  split
  · exact range389 pattern
  · exact range0 pattern
theorem range519 (pattern : Ten) : 0 ≤ d519 pattern ∧ d519 pattern ≤ 10 := by
  unfold d519
  split
  · exact range0 pattern
  · exact range518 pattern
theorem range520 (pattern : Ten) : 0 ≤ d520 pattern ∧ d520 pattern ≤ 10 := by
  unfold d520
  split
  · exact range386 pattern
  · exact range0 pattern
theorem range521 (pattern : Ten) : 0 ≤ d521 pattern ∧ d521 pattern ≤ 10 := by
  unfold d521
  split
  · exact range0 pattern
  · exact range520 pattern
theorem range522 (pattern : Ten) : 0 ≤ d522 pattern ∧ d522 pattern ≤ 10 := by
  unfold d522
  split
  · exact range350 pattern
  · exact range0 pattern
theorem range523 (pattern : Ten) : 0 ≤ d523 pattern ∧ d523 pattern ≤ 10 := by
  unfold d523
  split
  · exact range0 pattern
  · exact range522 pattern
theorem range524 (pattern : Ten) : 0 ≤ d524 pattern ∧ d524 pattern ≤ 10 := by
  unfold d524
  split
  · exact range10 pattern
  · exact range42 pattern
theorem range525 (pattern : Ten) : 0 ≤ d525 pattern ∧ d525 pattern ≤ 10 := by
  unfold d525
  split
  · exact range10 pattern
  · exact range43 pattern
theorem range526 (pattern : Ten) : 0 ≤ d526 pattern ∧ d526 pattern ≤ 10 := by
  unfold d526
  split
  · exact range525 pattern
  · exact range524 pattern
theorem range527 (pattern : Ten) : 0 ≤ d527 pattern ∧ d527 pattern ≤ 10 := by
  unfold d527
  split
  · exact range526 pattern
  · exact range42 pattern
theorem range528 (pattern : Ten) : 0 ≤ d528 pattern ∧ d528 pattern ≤ 10 := by
  unfold d528
  split
  · exact range10 pattern
  · exact range526 pattern
theorem range529 (pattern : Ten) : 0 ≤ d529 pattern ∧ d529 pattern ≤ 10 := by
  unfold d529
  split
  · exact range528 pattern
  · exact range527 pattern
theorem range530 (pattern : Ten) : 0 ≤ d530 pattern ∧ d530 pattern ≤ 10 := by
  unfold d530
  split
  · exact range0 pattern
  · exact range517 pattern
theorem range531 (pattern : Ten) : 0 ≤ d531 pattern ∧ d531 pattern ≤ 10 := by
  unfold d531
  split
  · exact range10 pattern
  · exact range197 pattern
theorem range532 (pattern : Ten) : 0 ≤ d532 pattern ∧ d532 pattern ≤ 10 := by
  unfold d532
  split
  · exact range10 pattern
  · exact range198 pattern
theorem range533 (pattern : Ten) : 0 ≤ d533 pattern ∧ d533 pattern ≤ 10 := by
  unfold d533
  split
  · exact range532 pattern
  · exact range531 pattern
theorem range534 (pattern : Ten) : 0 ≤ d534 pattern ∧ d534 pattern ≤ 10 := by
  unfold d534
  split
  · exact range533 pattern
  · exact range197 pattern
theorem range535 (pattern : Ten) : 0 ≤ d535 pattern ∧ d535 pattern ≤ 10 := by
  unfold d535
  split
  · exact range10 pattern
  · exact range533 pattern
theorem range536 (pattern : Ten) : 0 ≤ d536 pattern ∧ d536 pattern ≤ 10 := by
  unfold d536
  split
  · exact range535 pattern
  · exact range534 pattern
theorem range537 (pattern : Ten) : 0 ≤ d537 pattern ∧ d537 pattern ≤ 10 := by
  unfold d537
  split
  · exact range373 pattern
  · exact range0 pattern
theorem range538 (pattern : Ten) : 0 ≤ d538 pattern ∧ d538 pattern ≤ 10 := by
  unfold d538
  split
  · exact range0 pattern
  · exact range373 pattern
theorem range539 (pattern : Ten) : 0 ≤ d539 pattern ∧ d539 pattern ≤ 10 := by
  unfold d539
  split
  · exact range538 pattern
  · exact range0 pattern
end NetHack.Sokoban41.Diagram
