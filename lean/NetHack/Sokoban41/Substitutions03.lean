/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions02
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s450 (pattern : Ten) : d198 (change pattern 10 5) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 10 5) else d194 (change pattern 10 5)) = d198 pattern
  rw [s444, s449]
  rfl
theorem s451 (pattern : Ten) : d203 (change pattern 10 5) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 10 5) else d198 (change pattern 10 5)) = d203 pattern
  rw [s444, s450]
  rfl
theorem s452 (pattern : Ten) : d207 (change pattern 10 5) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 10 5) else d202 (change pattern 10 5)) = d207 pattern
  rw [s451, s446]
  rfl
theorem s453 (pattern : Ten) : d211 (change pattern 10 5) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 10 5) else d207 (change pattern 10 5)) = d211 pattern
  rw [s444, s452]
  rfl
theorem s454 (pattern : Ten) : d199 (change pattern 10 5) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 10 5) else d172 (change pattern 10 5)) = d199 pattern
  rw [s443, s439]
  rfl
theorem s455 (pattern : Ten) : d204 (change pattern 10 5) = d204 pattern := by
  change (if pattern.i then d198 (change pattern 10 5) else d199 (change pattern 10 5)) = d204 pattern
  rw [s450, s454]
  rfl
theorem s456 (pattern : Ten) : d8 (change pattern 10 5) = d8 pattern := by
  rfl
theorem s457 (pattern : Ten) : d9 (change pattern 10 5) = d9 pattern := by
  rfl
theorem s458 (pattern : Ten) : d195 (change pattern 10 5) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 10 5) else d8 (change pattern 10 5)) = d195 pattern
  rw [s457, s456]
  rfl
theorem s459 (pattern : Ten) : d200 (change pattern 10 5) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 10 5) else d195 (change pattern 10 5)) = d200 pattern
  rw [s444, s458]
  rfl
theorem s460 (pattern : Ten) : d205 (change pattern 10 5) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 10 5) else d200 (change pattern 10 5)) = d205 pattern
  rw [s444, s459]
  rfl
theorem s461 (pattern : Ten) : d208 (change pattern 10 5) = d208 pattern := by
  change (if pattern.h then d205 (change pattern 10 5) else d204 (change pattern 10 5)) = d208 pattern
  rw [s460, s455]
  rfl
theorem s462 (pattern : Ten) : d212 (change pattern 10 5) = d212 pattern := by
  change (if pattern.g then d10 (change pattern 10 5) else d208 (change pattern 10 5)) = d212 pattern
  rw [s444, s461]
  rfl
theorem s463 (pattern : Ten) : d215 (change pattern 10 5) = d215 pattern := by
  change (if pattern.c then d212 (change pattern 10 5) else d211 (change pattern 10 5)) = d215 pattern
  rw [s462, s453]
  rfl
theorem s464 (pattern : Ten) : d218 (change pattern 10 5) = d218 pattern := by
  change (if pattern.e then d215 (change pattern 10 5) else d207 (change pattern 10 5)) = d218 pattern
  rw [s463, s452]
  rfl
theorem s465 (pattern : Ten) : d209 (change pattern 10 5) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 10 5) else d205 (change pattern 10 5)) = d209 pattern
  rw [s444, s460]
  rfl
theorem s466 (pattern : Ten) : d11 (change pattern 10 5) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 5) else d9 (change pattern 10 5)) = d11 pattern
  rw [s444, s457]
  rfl
theorem s467 (pattern : Ten) : d196 (change pattern 10 5) = d11 pattern := by
  change d11 (change pattern 10 5) = d11 pattern
  exact s466 pattern
theorem s468 (pattern : Ten) : d201 (change pattern 10 5) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 10 5) else d196 (change pattern 10 5)) = d14 pattern
  rw [s444, s467]
  rfl
theorem s469 (pattern : Ten) : d206 (change pattern 10 5) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 10 5) else d201 (change pattern 10 5)) = d20 pattern
  rw [s444, s468]
  rfl
theorem s470 (pattern : Ten) : d210 (change pattern 10 5) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 10 5) else d206 (change pattern 10 5)) = d27 pattern
  rw [s444, s469]
  rfl
theorem s471 (pattern : Ten) : d213 (change pattern 10 5) = d441 pattern := by
  change (if pattern.g then d210 (change pattern 10 5) else d209 (change pattern 10 5)) = d441 pattern
  rw [s470, s465]
  rfl
theorem s472 (pattern : Ten) : d216 (change pattern 10 5) = d442 pattern := by
  change (if pattern.c then d213 (change pattern 10 5) else d209 (change pattern 10 5)) = d442 pattern
  rw [s471, s465]
  rfl
theorem s473 (pattern : Ten) : d214 (change pattern 10 5) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 10 5) else d209 (change pattern 10 5)) = d214 pattern
  rw [s444, s465]
  rfl
theorem s474 (pattern : Ten) : d217 (change pattern 10 5) = d217 pattern := by
  change (if pattern.c then d10 (change pattern 10 5) else d214 (change pattern 10 5)) = d217 pattern
  rw [s444, s473]
  rfl
theorem s475 (pattern : Ten) : d219 (change pattern 10 5) = d443 pattern := by
  change (if pattern.e then d217 (change pattern 10 5) else d216 (change pattern 10 5)) = d443 pattern
  rw [s474, s472]
  rfl
theorem s476 (pattern : Ten) : d220 (change pattern 10 5) = d444 pattern := by
  change (if pattern.d then d219 (change pattern 10 5) else d218 (change pattern 10 5)) = d444 pattern
  rw [s475, s464]
  rfl
theorem s477 (pattern : Ten) : d0 (change pattern 1 0) = d0 pattern := by
  rfl
theorem s478 (pattern : Ten) : d10 (change pattern 1 0) = d10 pattern := by
  rfl
theorem s479 (pattern : Ten) : d12 (change pattern 1 0) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 1 0) else d0 (change pattern 1 0)) = d12 pattern
  rw [s478, s477]
  rfl
theorem s480 (pattern : Ten) : d17 (change pattern 1 0) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 1 0) else d0 (change pattern 1 0)) = d17 pattern
  rw [s479, s477]
  rfl
theorem s481 (pattern : Ten) : d18 (change pattern 1 0) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 1 0) else d12 (change pattern 1 0)) = d18 pattern
  rw [s478, s479]
  rfl
theorem s482 (pattern : Ten) : d23 (change pattern 1 0) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 1 0) else d17 (change pattern 1 0)) = d23 pattern
  rw [s481, s480]
  rfl
theorem s483 (pattern : Ten) : d11 (change pattern 1 0) = d10 pattern := by
  change d10 (change pattern 1 0) = d10 pattern
  exact s478 pattern
theorem s484 (pattern : Ten) : d13 (change pattern 1 0) = d12 pattern := by
  change (if pattern.j then d11 (change pattern 1 0) else d0 (change pattern 1 0)) = d12 pattern
  rw [s483, s477]
  rfl
theorem s485 (pattern : Ten) : d14 (change pattern 1 0) = d10 pattern := by
  change (if pattern.j then d10 (change pattern 1 0) else d11 (change pattern 1 0)) = d10 pattern
  rw [s478, s483]
  simp only [ite_self]
theorem s486 (pattern : Ten) : d19 (change pattern 1 0) = d18 pattern := by
  change (if pattern.i then d14 (change pattern 1 0) else d13 (change pattern 1 0)) = d18 pattern
  rw [s485, s484]
  rfl
theorem s487 (pattern : Ten) : d20 (change pattern 1 0) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 1 0) else d14 (change pattern 1 0)) = d10 pattern
  rw [s478, s485]
  simp only [ite_self]
theorem s488 (pattern : Ten) : d24 (change pattern 1 0) = d26 pattern := by
  change (if pattern.h then d20 (change pattern 1 0) else d19 (change pattern 1 0)) = d26 pattern
  rw [s487, s486]
  rfl
theorem s489 (pattern : Ten) : d29 (change pattern 1 0) = d408 pattern := by
  change (if pattern.g then d24 (change pattern 1 0) else d23 (change pattern 1 0)) = d408 pattern
  rw [s488, s482]
  rfl
theorem s490 (pattern : Ten) : d2 (change pattern 1 0) = d2 pattern := by
  rfl
theorem s491 (pattern : Ten) : d15 (change pattern 1 0) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 1 0) else d0 (change pattern 1 0)) = d15 pattern
  rw [s490, s477]
  rfl
theorem s492 (pattern : Ten) : d16 (change pattern 1 0) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 1 0) else d2 (change pattern 1 0)) = d16 pattern
  rw [s478, s490]
  rfl
theorem s493 (pattern : Ten) : d21 (change pattern 1 0) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 1 0) else d15 (change pattern 1 0)) = d21 pattern
  rw [s492, s491]
  rfl
theorem s494 (pattern : Ten) : d22 (change pattern 1 0) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 1 0) else d16 (change pattern 1 0)) = d22 pattern
  rw [s478, s492]
  rfl
theorem s495 (pattern : Ten) : d25 (change pattern 1 0) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 1 0) else d21 (change pattern 1 0)) = d25 pattern
  rw [s494, s493]
  rfl
theorem s496 (pattern : Ten) : d30 (change pattern 1 0) = d227 pattern := by
  change (if pattern.g then d24 (change pattern 1 0) else d25 (change pattern 1 0)) = d227 pattern
  rw [s488, s495]
  rfl
theorem s497 (pattern : Ten) : d33 (change pattern 1 0) = d409 pattern := by
  change (if pattern.c then d30 (change pattern 1 0) else d29 (change pattern 1 0)) = d409 pattern
  rw [s496, s489]
  rfl
theorem s498 (pattern : Ten) : d26 (change pattern 1 0) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 1 0) else d18 (change pattern 1 0)) = d26 pattern
  rw [s478, s481]
  rfl
theorem s499 (pattern : Ten) : d27 (change pattern 1 0) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 1 0) else d20 (change pattern 1 0)) = d10 pattern
  rw [s478, s487]
  simp only [ite_self]
theorem s500 (pattern : Ten) : d31 (change pattern 1 0) = d228 pattern := by
  change (if pattern.g then d27 (change pattern 1 0) else d26 (change pattern 1 0)) = d228 pattern
  rw [s499, s498]
  rfl
theorem s501 (pattern : Ten) : d28 (change pattern 1 0) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 1 0) else d22 (change pattern 1 0)) = d28 pattern
  rw [s478, s494]
  rfl
theorem s502 (pattern : Ten) : d32 (change pattern 1 0) = d229 pattern := by
  change (if pattern.g then d27 (change pattern 1 0) else d28 (change pattern 1 0)) = d229 pattern
  rw [s499, s501]
  rfl
theorem s503 (pattern : Ten) : d34 (change pattern 1 0) = d231 pattern := by
  change (if pattern.c then d32 (change pattern 1 0) else d31 (change pattern 1 0)) = d231 pattern
  rw [s502, s500]
  rfl
theorem s504 (pattern : Ten) : d35 (change pattern 1 0) = d410 pattern := by
  change (if pattern.e then d34 (change pattern 1 0) else d33 (change pattern 1 0)) = d410 pattern
  rw [s503, s497]
  rfl
theorem s505 (pattern : Ten) : d36 (change pattern 1 0) = d233 pattern := by
  change (if pattern.e then d10 (change pattern 1 0) else d34 (change pattern 1 0)) = d233 pattern
  rw [s478, s503]
  rfl
theorem s506 (pattern : Ten) : d37 (change pattern 1 0) = d411 pattern := by
  change (if pattern.d then d36 (change pattern 1 0) else d35 (change pattern 1 0)) = d411 pattern
  rw [s505, s504]
  rfl
theorem s507 (pattern : Ten) : d1 (change pattern 1 0) = d1 pattern := by
  rfl
theorem s508 (pattern : Ten) : d240 (change pattern 1 0) = d1 pattern := by
  change d1 (change pattern 1 0) = d1 pattern
  exact s507 pattern
theorem s509 (pattern : Ten) : d171 (change pattern 1 0) = d1 pattern := by
  change d1 (change pattern 1 0) = d1 pattern
  exact s507 pattern
theorem s510 (pattern : Ten) : d241 (change pattern 1 0) = d1 pattern := by
  change (if pattern.f then d171 (change pattern 1 0) else d240 (change pattern 1 0)) = d1 pattern
  rw [s509, s508]
  simp only [ite_self]
theorem s511 (pattern : Ten) : d242 (change pattern 1 0) = d1 pattern := by
  change (if pattern.j then d171 (change pattern 1 0) else d241 (change pattern 1 0)) = d1 pattern
  rw [s509, s510]
  simp only [ite_self]
theorem s512 (pattern : Ten) : d173 (change pattern 1 0) = d412 pattern := by
  change (if pattern.j then d10 (change pattern 1 0) else d171 (change pattern 1 0)) = d412 pattern
  rw [s478, s509]
  rfl
theorem s513 (pattern : Ten) : d243 (change pattern 1 0) = d413 pattern := by
  change (if pattern.i then d173 (change pattern 1 0) else d242 (change pattern 1 0)) = d413 pattern
  rw [s512, s511]
  rfl
theorem s514 (pattern : Ten) : d177 (change pattern 1 0) = d414 pattern := by
  change (if pattern.i then d10 (change pattern 1 0) else d173 (change pattern 1 0)) = d414 pattern
  rw [s478, s512]
  rfl
theorem s515 (pattern : Ten) : d244 (change pattern 1 0) = d415 pattern := by
  change (if pattern.h then d177 (change pattern 1 0) else d243 (change pattern 1 0)) = d415 pattern
  rw [s514, s513]
  rfl
theorem s516 (pattern : Ten) : d181 (change pattern 1 0) = d416 pattern := by
  change (if pattern.h then d10 (change pattern 1 0) else d177 (change pattern 1 0)) = d416 pattern
  rw [s478, s514]
  rfl
theorem s517 (pattern : Ten) : d245 (change pattern 1 0) = d417 pattern := by
  change (if pattern.g then d181 (change pattern 1 0) else d244 (change pattern 1 0)) = d417 pattern
  rw [s516, s515]
  rfl
theorem s518 (pattern : Ten) : d3 (change pattern 1 0) = d3 pattern := by
  rfl
theorem s519 (pattern : Ten) : d172 (change pattern 1 0) = d3 pattern := by
  change d3 (change pattern 1 0) = d3 pattern
  exact s518 pattern
theorem s520 (pattern : Ten) : d174 (change pattern 1 0) = d418 pattern := by
  change (if pattern.j then d172 (change pattern 1 0) else d171 (change pattern 1 0)) = d418 pattern
  rw [s519, s509]
  rfl
theorem s521 (pattern : Ten) : d175 (change pattern 1 0) = d419 pattern := by
  change (if pattern.j then d10 (change pattern 1 0) else d172 (change pattern 1 0)) = d419 pattern
  rw [s478, s519]
  rfl
theorem s522 (pattern : Ten) : d178 (change pattern 1 0) = d420 pattern := by
  change (if pattern.i then d175 (change pattern 1 0) else d174 (change pattern 1 0)) = d420 pattern
  rw [s521, s520]
  rfl
theorem s523 (pattern : Ten) : d179 (change pattern 1 0) = d421 pattern := by
  change (if pattern.i then d10 (change pattern 1 0) else d175 (change pattern 1 0)) = d421 pattern
  rw [s478, s521]
  rfl
theorem s524 (pattern : Ten) : d182 (change pattern 1 0) = d422 pattern := by
  change (if pattern.h then d179 (change pattern 1 0) else d178 (change pattern 1 0)) = d422 pattern
  rw [s523, s522]
  rfl
theorem s525 (pattern : Ten) : d185 (change pattern 1 0) = d423 pattern := by
  change (if pattern.g then d181 (change pattern 1 0) else d182 (change pattern 1 0)) = d423 pattern
  rw [s516, s524]
  rfl
theorem s526 (pattern : Ten) : d246 (change pattern 1 0) = d424 pattern := by
  change (if pattern.c then d185 (change pattern 1 0) else d245 (change pattern 1 0)) = d424 pattern
  rw [s525, s517]
  rfl
theorem s527 (pattern : Ten) : d186 (change pattern 1 0) = d425 pattern := by
  change (if pattern.g then d10 (change pattern 1 0) else d181 (change pattern 1 0)) = d425 pattern
  rw [s478, s516]
  rfl
theorem s528 (pattern : Ten) : d183 (change pattern 1 0) = d426 pattern := by
  change (if pattern.h then d10 (change pattern 1 0) else d179 (change pattern 1 0)) = d426 pattern
  rw [s478, s523]
  rfl
theorem s529 (pattern : Ten) : d187 (change pattern 1 0) = d427 pattern := by
  change (if pattern.g then d10 (change pattern 1 0) else d183 (change pattern 1 0)) = d427 pattern
  rw [s478, s528]
  rfl
theorem s530 (pattern : Ten) : d189 (change pattern 1 0) = d428 pattern := by
  change (if pattern.c then d187 (change pattern 1 0) else d186 (change pattern 1 0)) = d428 pattern
  rw [s529, s527]
  rfl
theorem s531 (pattern : Ten) : d247 (change pattern 1 0) = d429 pattern := by
  change (if pattern.e then d189 (change pattern 1 0) else d246 (change pattern 1 0)) = d429 pattern
  rw [s530, s526]
  rfl
theorem s532 (pattern : Ten) : d191 (change pattern 1 0) = d430 pattern := by
  change (if pattern.e then d10 (change pattern 1 0) else d189 (change pattern 1 0)) = d430 pattern
  rw [s478, s530]
  rfl
theorem s533 (pattern : Ten) : d248 (change pattern 1 0) = d431 pattern := by
  change (if pattern.d then d191 (change pattern 1 0) else d247 (change pattern 1 0)) = d431 pattern
  rw [s532, s531]
  rfl
theorem s534 (pattern : Ten) : d0 (change pattern 1 10) = d0 pattern := by
  rfl
theorem s535 (pattern : Ten) : d10 (change pattern 1 10) = d10 pattern := by
  rfl
theorem s536 (pattern : Ten) : d12 (change pattern 1 10) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 1 10) else d0 (change pattern 1 10)) = d12 pattern
  rw [s535, s534]
  rfl
theorem s537 (pattern : Ten) : d17 (change pattern 1 10) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 1 10) else d0 (change pattern 1 10)) = d17 pattern
  rw [s536, s534]
  rfl
theorem s538 (pattern : Ten) : d18 (change pattern 1 10) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 1 10) else d12 (change pattern 1 10)) = d18 pattern
  rw [s535, s536]
  rfl
theorem s539 (pattern : Ten) : d23 (change pattern 1 10) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 1 10) else d17 (change pattern 1 10)) = d23 pattern
  rw [s538, s537]
  rfl
theorem s540 (pattern : Ten) : d9 (change pattern 1 10) = d9 pattern := by
  rfl
theorem s541 (pattern : Ten) : d11 (change pattern 1 10) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 1 10) else d9 (change pattern 1 10)) = d11 pattern
  rw [s535, s540]
  rfl
theorem s542 (pattern : Ten) : d13 (change pattern 1 10) = d13 pattern := by
  change (if pattern.j then d11 (change pattern 1 10) else d0 (change pattern 1 10)) = d13 pattern
  rw [s541, s534]
  rfl
theorem s543 (pattern : Ten) : d14 (change pattern 1 10) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 1 10) else d11 (change pattern 1 10)) = d14 pattern
  rw [s535, s541]
  rfl
theorem s544 (pattern : Ten) : d19 (change pattern 1 10) = d19 pattern := by
  change (if pattern.i then d14 (change pattern 1 10) else d13 (change pattern 1 10)) = d19 pattern
  rw [s543, s542]
  rfl
theorem s545 (pattern : Ten) : d20 (change pattern 1 10) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 1 10) else d14 (change pattern 1 10)) = d20 pattern
  rw [s535, s543]
  rfl
theorem s546 (pattern : Ten) : d24 (change pattern 1 10) = d24 pattern := by
  change (if pattern.h then d20 (change pattern 1 10) else d19 (change pattern 1 10)) = d24 pattern
  rw [s545, s544]
  rfl
theorem s547 (pattern : Ten) : d29 (change pattern 1 10) = d29 pattern := by
  change (if pattern.g then d24 (change pattern 1 10) else d23 (change pattern 1 10)) = d29 pattern
  rw [s546, s539]
  rfl
theorem s548 (pattern : Ten) : d2 (change pattern 1 10) = d2 pattern := by
  rfl
theorem s549 (pattern : Ten) : d15 (change pattern 1 10) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 1 10) else d0 (change pattern 1 10)) = d15 pattern
  rw [s548, s534]
  rfl
theorem s550 (pattern : Ten) : d16 (change pattern 1 10) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 1 10) else d2 (change pattern 1 10)) = d16 pattern
  rw [s535, s548]
  rfl
theorem s551 (pattern : Ten) : d21 (change pattern 1 10) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 1 10) else d15 (change pattern 1 10)) = d21 pattern
  rw [s550, s549]
  rfl
theorem s552 (pattern : Ten) : d22 (change pattern 1 10) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 1 10) else d16 (change pattern 1 10)) = d22 pattern
  rw [s535, s550]
  rfl
theorem s553 (pattern : Ten) : d25 (change pattern 1 10) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 1 10) else d21 (change pattern 1 10)) = d25 pattern
  rw [s552, s551]
  rfl
theorem s554 (pattern : Ten) : d30 (change pattern 1 10) = d30 pattern := by
  change (if pattern.g then d24 (change pattern 1 10) else d25 (change pattern 1 10)) = d30 pattern
  rw [s546, s553]
  rfl
theorem s555 (pattern : Ten) : d33 (change pattern 1 10) = d33 pattern := by
  change (if pattern.c then d30 (change pattern 1 10) else d29 (change pattern 1 10)) = d33 pattern
  rw [s554, s547]
  rfl
theorem s556 (pattern : Ten) : d26 (change pattern 1 10) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 1 10) else d18 (change pattern 1 10)) = d26 pattern
  rw [s535, s538]
  rfl
theorem s557 (pattern : Ten) : d27 (change pattern 1 10) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 1 10) else d20 (change pattern 1 10)) = d27 pattern
  rw [s535, s545]
  rfl
theorem s558 (pattern : Ten) : d31 (change pattern 1 10) = d31 pattern := by
  change (if pattern.g then d27 (change pattern 1 10) else d26 (change pattern 1 10)) = d31 pattern
  rw [s557, s556]
  rfl
theorem s559 (pattern : Ten) : d28 (change pattern 1 10) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 1 10) else d22 (change pattern 1 10)) = d28 pattern
  rw [s535, s552]
  rfl
theorem s560 (pattern : Ten) : d32 (change pattern 1 10) = d32 pattern := by
  change (if pattern.g then d27 (change pattern 1 10) else d28 (change pattern 1 10)) = d32 pattern
  rw [s557, s559]
  rfl
theorem s561 (pattern : Ten) : d34 (change pattern 1 10) = d34 pattern := by
  change (if pattern.c then d32 (change pattern 1 10) else d31 (change pattern 1 10)) = d34 pattern
  rw [s560, s558]
  rfl
theorem s562 (pattern : Ten) : d35 (change pattern 1 10) = d35 pattern := by
  change (if pattern.e then d34 (change pattern 1 10) else d33 (change pattern 1 10)) = d35 pattern
  rw [s561, s555]
  rfl
theorem s563 (pattern : Ten) : d36 (change pattern 1 10) = d36 pattern := by
  change (if pattern.e then d10 (change pattern 1 10) else d34 (change pattern 1 10)) = d36 pattern
  rw [s535, s561]
  rfl
theorem s564 (pattern : Ten) : d37 (change pattern 1 10) = d37 pattern := by
  change (if pattern.d then d36 (change pattern 1 10) else d35 (change pattern 1 10)) = d37 pattern
  rw [s563, s562]
  rfl
theorem s565 (pattern : Ten) : d239 (change pattern 1 10) = d0 pattern := by
  change d0 (change pattern 1 10) = d0 pattern
  exact s534 pattern
theorem s566 (pattern : Ten) : d1 (change pattern 1 10) = d1 pattern := by
  rfl
theorem s567 (pattern : Ten) : d240 (change pattern 1 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 1 10) else d239 (change pattern 1 10)) = d171 pattern
  rw [s566, s565]
  rfl
theorem s568 (pattern : Ten) : d171 (change pattern 1 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 1 10) else d0 (change pattern 1 10)) = d171 pattern
  rw [s566, s534]
  rfl
theorem s569 (pattern : Ten) : d241 (change pattern 1 10) = d171 pattern := by
  change (if pattern.f then d171 (change pattern 1 10) else d240 (change pattern 1 10)) = d171 pattern
  rw [s568, s567]
  simp only [ite_self]
theorem s570 (pattern : Ten) : d242 (change pattern 1 10) = d171 pattern := by
  change (if pattern.j then d171 (change pattern 1 10) else d241 (change pattern 1 10)) = d171 pattern
  rw [s568, s569]
  simp only [ite_self]
theorem s571 (pattern : Ten) : d173 (change pattern 1 10) = d173 pattern := by
  change (if pattern.j then d10 (change pattern 1 10) else d171 (change pattern 1 10)) = d173 pattern
  rw [s535, s568]
  rfl
theorem s572 (pattern : Ten) : d243 (change pattern 1 10) = d176 pattern := by
  change (if pattern.i then d173 (change pattern 1 10) else d242 (change pattern 1 10)) = d176 pattern
  rw [s571, s570]
  rfl
theorem s573 (pattern : Ten) : d177 (change pattern 1 10) = d177 pattern := by
  change (if pattern.i then d10 (change pattern 1 10) else d173 (change pattern 1 10)) = d177 pattern
  rw [s535, s571]
  rfl
theorem s574 (pattern : Ten) : d244 (change pattern 1 10) = d180 pattern := by
  change (if pattern.h then d177 (change pattern 1 10) else d243 (change pattern 1 10)) = d180 pattern
  rw [s573, s572]
  rfl
theorem s575 (pattern : Ten) : d181 (change pattern 1 10) = d181 pattern := by
  change (if pattern.h then d10 (change pattern 1 10) else d177 (change pattern 1 10)) = d181 pattern
  rw [s535, s573]
  rfl
theorem s576 (pattern : Ten) : d245 (change pattern 1 10) = d184 pattern := by
  change (if pattern.g then d181 (change pattern 1 10) else d244 (change pattern 1 10)) = d184 pattern
  rw [s575, s574]
  rfl
theorem s577 (pattern : Ten) : d3 (change pattern 1 10) = d3 pattern := by
  rfl
theorem s578 (pattern : Ten) : d172 (change pattern 1 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 1 10) else d2 (change pattern 1 10)) = d172 pattern
  rw [s577, s548]
  rfl
theorem s579 (pattern : Ten) : d174 (change pattern 1 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 1 10) else d171 (change pattern 1 10)) = d174 pattern
  rw [s578, s568]
  rfl
theorem s580 (pattern : Ten) : d175 (change pattern 1 10) = d175 pattern := by
  change (if pattern.j then d10 (change pattern 1 10) else d172 (change pattern 1 10)) = d175 pattern
  rw [s535, s578]
  rfl
theorem s581 (pattern : Ten) : d178 (change pattern 1 10) = d178 pattern := by
  change (if pattern.i then d175 (change pattern 1 10) else d174 (change pattern 1 10)) = d178 pattern
  rw [s580, s579]
  rfl
theorem s582 (pattern : Ten) : d179 (change pattern 1 10) = d179 pattern := by
  change (if pattern.i then d10 (change pattern 1 10) else d175 (change pattern 1 10)) = d179 pattern
  rw [s535, s580]
  rfl
theorem s583 (pattern : Ten) : d182 (change pattern 1 10) = d182 pattern := by
  change (if pattern.h then d179 (change pattern 1 10) else d178 (change pattern 1 10)) = d182 pattern
  rw [s582, s581]
  rfl
theorem s584 (pattern : Ten) : d185 (change pattern 1 10) = d185 pattern := by
  change (if pattern.g then d181 (change pattern 1 10) else d182 (change pattern 1 10)) = d185 pattern
  rw [s575, s583]
  rfl
theorem s585 (pattern : Ten) : d246 (change pattern 1 10) = d188 pattern := by
  change (if pattern.c then d185 (change pattern 1 10) else d245 (change pattern 1 10)) = d188 pattern
  rw [s584, s576]
  rfl
theorem s586 (pattern : Ten) : d186 (change pattern 1 10) = d186 pattern := by
  change (if pattern.g then d10 (change pattern 1 10) else d181 (change pattern 1 10)) = d186 pattern
  rw [s535, s575]
  rfl
theorem s587 (pattern : Ten) : d183 (change pattern 1 10) = d183 pattern := by
  change (if pattern.h then d10 (change pattern 1 10) else d179 (change pattern 1 10)) = d183 pattern
  rw [s535, s582]
  rfl
theorem s588 (pattern : Ten) : d187 (change pattern 1 10) = d187 pattern := by
  change (if pattern.g then d10 (change pattern 1 10) else d183 (change pattern 1 10)) = d187 pattern
  rw [s535, s587]
  rfl
theorem s589 (pattern : Ten) : d189 (change pattern 1 10) = d189 pattern := by
  change (if pattern.c then d187 (change pattern 1 10) else d186 (change pattern 1 10)) = d189 pattern
  rw [s588, s586]
  rfl
theorem s590 (pattern : Ten) : d247 (change pattern 1 10) = d190 pattern := by
  change (if pattern.e then d189 (change pattern 1 10) else d246 (change pattern 1 10)) = d190 pattern
  rw [s589, s585]
  rfl
theorem s591 (pattern : Ten) : d191 (change pattern 1 10) = d191 pattern := by
  change (if pattern.e then d10 (change pattern 1 10) else d189 (change pattern 1 10)) = d191 pattern
  rw [s535, s589]
  rfl
theorem s592 (pattern : Ten) : d248 (change pattern 1 10) = d192 pattern := by
  change (if pattern.d then d191 (change pattern 1 10) else d247 (change pattern 1 10)) = d192 pattern
  rw [s591, s590]
  rfl
theorem s593 (pattern : Ten) : d0 (change pattern 10 1) = d0 pattern := by
  rfl
theorem s594 (pattern : Ten) : d10 (change pattern 10 1) = d10 pattern := by
  rfl
theorem s595 (pattern : Ten) : d12 (change pattern 10 1) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 10 1) else d0 (change pattern 10 1)) = d12 pattern
  rw [s594, s593]
  rfl
theorem s596 (pattern : Ten) : d17 (change pattern 10 1) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 10 1) else d0 (change pattern 10 1)) = d17 pattern
  rw [s595, s593]
  rfl
theorem s597 (pattern : Ten) : d18 (change pattern 10 1) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 10 1) else d12 (change pattern 10 1)) = d18 pattern
  rw [s594, s595]
  rfl
theorem s598 (pattern : Ten) : d23 (change pattern 10 1) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 10 1) else d17 (change pattern 10 1)) = d23 pattern
  rw [s597, s596]
  rfl
theorem s599 (pattern : Ten) : d9 (change pattern 10 1) = d9 pattern := by
  rfl
end NetHack.Sokoban41.Diagram
