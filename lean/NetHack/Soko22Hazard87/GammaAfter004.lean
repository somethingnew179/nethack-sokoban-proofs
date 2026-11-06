import NetHack.Soko22Hazard87.GammaAfter003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter400 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter401 (p : Pattern) : bonus (HazardPattern.nextHero (.push 146 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 168))) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  change d0 (u151 p) = d0 p
  exact allUpdate91 p
theorem gammaAfter402 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter403 (p : Pattern) : bonus (HazardPattern.nextHero (.push 125 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 126))) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  change d0 (u116 p) = d0 p
  exact allUpdate68 p
theorem gammaAfter404 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter405 (p : Pattern) : bonus (HazardPattern.nextHero (.push 123 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 122))) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  change d0 (u107 p) = d0 p
  exact allUpdate59 p
theorem gammaAfter406 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  rfl
theorem gammaAfter407 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 101)) (HazardPattern.afterPattern 10000 p (.walk 101)) = d0 p := by
  change bonus 101 _ = _
  rw [at101]
  rfl
theorem gammaAfter408 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter409 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter410 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  rfl
theorem gammaAfter411 (p : Pattern) : bonus (HazardPattern.nextHero (.push 103 (.stay 81))) (HazardPattern.afterPattern 10000 p (.push 103 (.stay 81))) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  change d0 (u76 p) = d0 p
  exact allUpdate34 p
theorem gammaAfter412 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter413 (p : Pattern) : bonus (HazardPattern.nextHero (.push 147 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 169))) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  change d0 (u155 p) = d0 p
  exact allUpdate95 p
theorem gammaAfter414 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter415 (p : Pattern) : bonus (HazardPattern.nextHero (.push 126 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 127))) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  change d0 (u120 p) = d0 p
  exact allUpdate72 p
theorem gammaAfter416 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter417 (p : Pattern) : bonus (HazardPattern.nextHero (.push 124 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 123))) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  change d0 (u111 p) = d0 p
  exact allUpdate63 p
theorem gammaAfter418 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  rfl
theorem gammaAfter419 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 102)) (HazardPattern.afterPattern 10000 p (.walk 102)) = d0 p := by
  change bonus 102 _ = _
  rw [at102]
  rfl
theorem gammaAfter420 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter421 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter422 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  rfl
theorem gammaAfter423 (p : Pattern) : bonus (HazardPattern.nextHero (.push 104 (.stay 82))) (HazardPattern.afterPattern 10000 p (.push 104 (.stay 82))) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  change d0 (u80 p) = d0 p
  exact allUpdate38 p
theorem gammaAfter424 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter425 (p : Pattern) : bonus (HazardPattern.nextHero (.push 148 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 170))) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  change d0 (u159 p) = d0 p
  exact allUpdate99 p
theorem gammaAfter426 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter427 (p : Pattern) : bonus (HazardPattern.nextHero (.push 127 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 128))) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  change d0 (u124 p) = d0 p
  exact allUpdate76 p
theorem gammaAfter428 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter429 (p : Pattern) : bonus (HazardPattern.nextHero (.push 125 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 124))) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  change d0 (u115 p) = d0 p
  exact allUpdate67 p
theorem gammaAfter430 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  rfl
theorem gammaAfter431 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 103)) (HazardPattern.afterPattern 10000 p (.walk 103)) = d0 p := by
  change bonus 103 _ = _
  rw [at103]
  rfl
theorem gammaAfter432 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter433 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter434 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  rfl
theorem gammaAfter435 (p : Pattern) : bonus (HazardPattern.nextHero (.push 105 (.stay 83))) (HazardPattern.afterPattern 10000 p (.push 105 (.stay 83))) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  change d0 (u84 p) = d0 p
  exact allUpdate42 p
theorem gammaAfter436 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter437 (p : Pattern) : bonus (HazardPattern.nextHero (.push 149 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 171))) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  change d0 (u163 p) = d0 p
  exact allUpdate103 p
theorem gammaAfter438 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  rfl
theorem gammaAfter439 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter440 (p : Pattern) : bonus (HazardPattern.nextHero (.push 126 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 125))) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  change d0 (u119 p) = d0 p
  exact allUpdate71 p
theorem gammaAfter441 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) = d0 p := by
  change bonus 106 _ = _
  rw [at106]
  rfl
theorem gammaAfter442 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 104)) (HazardPattern.afterPattern 10000 p (.walk 104)) = d0 p := by
  change bonus 104 _ = _
  rw [at104]
  rfl
theorem gammaAfter443 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  rfl
theorem gammaAfter444 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter445 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 106)) (HazardPattern.afterPattern 10000 p (.walk 106)) = d0 p := by
  change bonus 106 _ = _
  rw [at106]
  rfl
theorem gammaAfter446 (p : Pattern) : bonus (HazardPattern.nextHero (.push 106 (.stay 84))) (HazardPattern.afterPattern 10000 p (.push 106 (.stay 84))) = d0 p := by
  change bonus 106 _ = _
  rw [at106]
  change d0 (u88 p) = d0 p
  exact allUpdate46 p
theorem gammaAfter447 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  rfl
theorem gammaAfter448 (p : Pattern) : bonus (HazardPattern.nextHero (.push 150 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 172))) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  change d0 (u165 p) = d0 p
  exact allUpdate105 p
theorem gammaAfter449 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter450 (p : Pattern) : bonus (HazardPattern.nextHero (.push 127 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 126))) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  change d0 (u123 p) = d0 p
  exact allUpdate75 p
theorem gammaAfter451 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 105)) (HazardPattern.afterPattern 10000 p (.walk 105)) = d0 p := by
  change bonus 105 _ = _
  rw [at105]
  rfl
theorem gammaAfter452 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter453 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) = d5849 p := by
  change bonus 111 _ = _
  rw [at111]
  rfl
theorem gammaAfter454 (p : Pattern) : bonus (HazardPattern.nextHero (.push 111 (.stay 89))) (HazardPattern.afterPattern 10000 p (.push 111 (.stay 89))) = d102349 p := by
  change bonus 111 _ = _
  rw [at111]
  change d5849 (u90 p) = d102349 p
  exact allUpdate5293 p
theorem gammaAfter455 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) = d5849 p := by
  change bonus 155 _ = _
  rw [at155]
  rfl
theorem gammaAfter456 (p : Pattern) : bonus (HazardPattern.nextHero (.push 155 (.stay 177))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 177))) = d0 p := by
  change bonus 155 _ = _
  rw [at155]
  change d5849 (u167 p) = d0 p
  exact allUpdate5788 p
theorem gammaAfter457 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter458 (p : Pattern) : bonus (HazardPattern.nextHero (.push 134 (.stay 135))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 135))) = d103455 p := by
  change bonus 134 _ = _
  rw [at134]
  change d5849 (u131 p) = d103455 p
  exact allUpdate5780 p
theorem gammaAfter459 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter460 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter461 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter462 (p : Pattern) : bonus (HazardPattern.nextHero (.push 135 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 136))) = d105434 p := by
  change bonus 135 _ = _
  rw [at135]
  change d8234 (u134 p) = d105434 p
  exact allUpdate9405 p
theorem gammaAfter463 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) = d5849 p := by
  change bonus 133 _ = _
  rw [at133]
  rfl
theorem gammaAfter464 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) = d6737 p := by
  change bonus 113 _ = _
  rw [at113]
  rfl
theorem gammaAfter465 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 111)) (HazardPattern.afterPattern 10000 p (.walk 111)) = d5849 p := by
  change bonus 111 _ = _
  rw [at111]
  rfl
theorem gammaAfter466 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter467 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) = d5849 p := by
  change bonus 155 _ = _
  rw [at155]
  rfl
theorem gammaAfter468 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) = d6737 p := by
  change bonus 113 _ = _
  rw [at113]
  rfl
theorem gammaAfter469 (p : Pattern) : bonus (HazardPattern.nextHero (.push 113 (.stay 91))) (HazardPattern.afterPattern 10000 p (.push 113 (.stay 91))) = d109664 p := by
  change bonus 113 _ = _
  rw [at113]
  change d6737 (u92 p) = d109664 p
  exact allUpdate7087 p
theorem gammaAfter470 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter471 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter472 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter473 (p : Pattern) : bonus (HazardPattern.nextHero (.push 134 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 134 (.stay 133))) = d0 p := by
  change bonus 134 _ = _
  rw [at134]
  change d5849 (u130 p) = d0 p
  exact allUpdate5308 p
theorem gammaAfter474 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter475 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter476 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter477 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 114)) (HazardPattern.afterPattern 10000 p (.walk 114)) = d7239 p := by
  change bonus 114 _ = _
  rw [at114]
  rfl
theorem gammaAfter478 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter479 (p : Pattern) : bonus (HazardPattern.nextHero (.push 158 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 180))) = d118614 p := by
  change bonus 158 _ = _
  rw [at158]
  change d13979 (u175 p) = d118614 p
  exact allUpdate13259 p
theorem gammaAfter480 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter481 (p : Pattern) : bonus (HazardPattern.nextHero (.push 135 (.stay 134))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 134))) = d0 p := by
  change bonus 135 _ = _
  rw [at135]
  change d8234 (u133 p) = d0 p
  exact allUpdate8963 p
theorem gammaAfter482 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter483 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 113)) (HazardPattern.afterPattern 10000 p (.walk 113)) = d6737 p := by
  change bonus 113 _ = _
  rw [at113]
  rfl
theorem gammaAfter484 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter485 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter486 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 116)) (HazardPattern.afterPattern 10000 p (.walk 116)) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  rfl
theorem gammaAfter487 (p : Pattern) : bonus (HazardPattern.nextHero (.push 116 (.stay 94))) (HazardPattern.afterPattern 10000 p (.push 116 (.stay 94))) = d0 p := by
  change bonus 116 _ = _
  rw [at116]
  change d0 (u98 p) = d0 p
  exact allUpdate50 p
theorem gammaAfter488 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) = d17560 p := by
  change bonus 160 _ = _
  rw [at160]
  rfl
theorem gammaAfter489 (p : Pattern) : bonus (HazardPattern.nextHero (.push 160 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 182))) = d0 p := by
  change bonus 160 _ = _
  rw [at160]
  change d17560 (u181 p) = d0 p
  exact allUpdate16350 p
theorem gammaAfter490 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 115)) (HazardPattern.afterPattern 10000 p (.walk 115)) = d0 p := by
  change bonus 115 _ = _
  rw [at115]
  rfl
theorem gammaAfter491 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) = d18533 p := by
  change bonus 161 _ = _
  rw [at161]
  rfl
theorem gammaAfter492 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter493 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 119)) (HazardPattern.afterPattern 10000 p (.walk 119)) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  rfl
theorem gammaAfter494 (p : Pattern) : bonus (HazardPattern.nextHero (.push 119 (.stay 97))) (HazardPattern.afterPattern 10000 p (.push 119 (.stay 97))) = d0 p := by
  change bonus 119 _ = _
  rw [at119]
  change d0 (u100 p) = d0 p
  exact allUpdate52 p
theorem gammaAfter495 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter496 (p : Pattern) : bonus (HazardPattern.nextHero (.push 163 (.stay 185))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 185))) = d0 p := by
  change bonus 163 _ = _
  rw [at163]
  change d20389 (u189 p) = d0 p
  exact allUpdate20141 p
theorem gammaAfter497 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 120)) (HazardPattern.afterPattern 10000 p (.walk 120)) = d0 p := by
  change bonus 120 _ = _
  rw [at120]
  rfl
theorem gammaAfter498 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 118)) (HazardPattern.afterPattern 10000 p (.walk 118)) = d0 p := by
  change bonus 118 _ = _
  rw [at118]
  rfl
theorem gammaAfter499 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) = d20891 p := by
  change bonus 164 _ = _
  rw [at164]
  rfl
end NetHack.Soko22Hazard87
