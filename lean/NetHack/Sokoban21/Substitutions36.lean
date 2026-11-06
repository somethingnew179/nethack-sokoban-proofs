/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions35
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5400 (pattern : Twelve) : d95 (change pattern 6 12) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 6 12) else d79 (change pattern 6 12)) = d95 pattern
  rw [s5399, s5398]
  rfl
theorem s5401 (pattern : Twelve) : d60 (change pattern 6 12) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 6 12) else d38 (change pattern 6 12)) = d60 pattern
  rw [s5203, s5193]
  rfl
theorem s5402 (pattern : Twelve) : d81 (change pattern 6 12) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 6 12) else d59 (change pattern 6 12)) = d81 pattern
  rw [s5401, s5195]
  rfl
theorem s5403 (pattern : Twelve) : d61 (change pattern 6 12) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 6 12) else d41 (change pattern 6 12)) = d61 pattern
  rw [s5170, s5198]
  rfl
theorem s5404 (pattern : Twelve) : d82 (change pattern 6 12) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 6 12) else d59 (change pattern 6 12)) = d82 pattern
  rw [s5403, s5195]
  rfl
theorem s5405 (pattern : Twelve) : d96 (change pattern 6 12) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 6 12) else d81 (change pattern 6 12)) = d96 pattern
  rw [s5404, s5402]
  rfl
theorem s5406 (pattern : Twelve) : d104 (change pattern 6 12) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 6 12) else d95 (change pattern 6 12)) = d104 pattern
  rw [s5405, s5400]
  rfl
theorem s5407 (pattern : Twelve) : d105 (change pattern 6 12) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d94 (change pattern 6 12)) = d105 pattern
  rw [s5169, s5393]
  rfl
theorem s5408 (pattern : Twelve) : d111 (change pattern 6 12) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 6 12) else d104 (change pattern 6 12)) = d111 pattern
  rw [s5407, s5406]
  rfl
theorem s5409 (pattern : Twelve) : d114 (change pattern 6 12) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 6 12) else d110 (change pattern 6 12)) = d114 pattern
  rw [s5408, s5395]
  rfl
theorem s5410 (pattern : Twelve) : d807 (change pattern 6 12) = d114 pattern := by
  change d114 (change pattern 6 12) = d114 pattern
  exact s5409 pattern
theorem s5411 (pattern : Twelve) : d120 (change pattern 6 12) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 6 12) else d17 (change pattern 6 12)) = d120 pattern
  rw [s5167, s5152]
  rfl
theorem s5412 (pattern : Twelve) : d129 (change pattern 6 12) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 6 12) else d120 (change pattern 6 12)) = d129 pattern
  rw [s5273, s5411]
  rfl
theorem s5413 (pattern : Twelve) : d136 (change pattern 6 12) = d136 pattern := by
  change (if pattern.f then d129 (change pattern 6 12) else d0 (change pattern 6 12)) = d136 pattern
  rw [s5412, s5149]
  rfl
theorem s5414 (pattern : Twelve) : d144 (change pattern 6 12) = d144 pattern := by
  change (if pattern.e then d136 (change pattern 6 12) else d72 (change pattern 6 12)) = d144 pattern
  rw [s5413, s5371]
  rfl
theorem s5415 (pattern : Twelve) : d121 (change pattern 6 12) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 6 12) else d0 (change pattern 6 12)) = d121 pattern
  rw [s5178, s5149]
  rfl
theorem s5416 (pattern : Twelve) : d130 (change pattern 6 12) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 6 12) else d121 (change pattern 6 12)) = d130 pattern
  rw [s5183, s5415]
  rfl
theorem s5417 (pattern : Twelve) : d137 (change pattern 6 12) = d137 pattern := by
  change (if pattern.f then d130 (change pattern 6 12) else d52 (change pattern 6 12)) = d137 pattern
  rw [s5416, s5378]
  rfl
theorem s5418 (pattern : Twelve) : d138 (change pattern 6 12) = d138 pattern := by
  change (if pattern.f then d129 (change pattern 6 12) else d56 (change pattern 6 12)) = d138 pattern
  rw [s5412, s5176]
  rfl
theorem s5419 (pattern : Twelve) : d145 (change pattern 6 12) = d145 pattern := by
  change (if pattern.e then d138 (change pattern 6 12) else d137 (change pattern 6 12)) = d145 pattern
  rw [s5418, s5417]
  rfl
theorem s5420 (pattern : Twelve) : d149 (change pattern 6 12) = d149 pattern := by
  change (if pattern.j then d145 (change pattern 6 12) else d144 (change pattern 6 12)) = d149 pattern
  rw [s5419, s5414]
  rfl
theorem s5421 (pattern : Twelve) : d139 (change pattern 6 12) = d139 pattern := by
  change (if pattern.f then d130 (change pattern 6 12) else d56 (change pattern 6 12)) = d139 pattern
  rw [s5416, s5176]
  rfl
theorem s5422 (pattern : Twelve) : d146 (change pattern 6 12) = d146 pattern := by
  change (if pattern.e then d138 (change pattern 6 12) else d139 (change pattern 6 12)) = d146 pattern
  rw [s5418, s5421]
  rfl
theorem s5423 (pattern : Twelve) : d150 (change pattern 6 12) = d150 pattern := by
  change (if pattern.j then d146 (change pattern 6 12) else d144 (change pattern 6 12)) = d150 pattern
  rw [s5422, s5414]
  rfl
theorem s5424 (pattern : Twelve) : d153 (change pattern 6 12) = d153 pattern := by
  change (if pattern.d then d150 (change pattern 6 12) else d149 (change pattern 6 12)) = d153 pattern
  rw [s5423, s5420]
  rfl
theorem s5425 (pattern : Twelve) : d122 (change pattern 6 12) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 6 12) else d17 (change pattern 6 12)) = d122 pattern
  rw [s5163, s5152]
  rfl
theorem s5426 (pattern : Twelve) : d131 (change pattern 6 12) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 6 12) else d121 (change pattern 6 12)) = d131 pattern
  rw [s5425, s5415]
  rfl
theorem s5427 (pattern : Twelve) : d140 (change pattern 6 12) = d140 pattern := by
  change (if pattern.f then d131 (change pattern 6 12) else d30 (change pattern 6 12)) = d140 pattern
  rw [s5426, s5174]
  rfl
theorem s5428 (pattern : Twelve) : d123 (change pattern 6 12) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 6 12) else d0 (change pattern 6 12)) = d123 pattern
  rw [s5160, s5149]
  rfl
theorem s5429 (pattern : Twelve) : d132 (change pattern 6 12) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 6 12) else d30 (change pattern 6 12)) = d132 pattern
  rw [s5428, s5174]
  rfl
theorem s5430 (pattern : Twelve) : d141 (change pattern 6 12) = d141 pattern := by
  change (if pattern.f then d129 (change pattern 6 12) else d132 (change pattern 6 12)) = d141 pattern
  rw [s5412, s5429]
  rfl
theorem s5431 (pattern : Twelve) : d147 (change pattern 6 12) = d147 pattern := by
  change (if pattern.e then d141 (change pattern 6 12) else d140 (change pattern 6 12)) = d147 pattern
  rw [s5430, s5427]
  rfl
theorem s5432 (pattern : Twelve) : d124 (change pattern 6 12) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 6 12) else d2 (change pattern 6 12)) = d124 pattern
  rw [s5249, s5158]
  rfl
theorem s5433 (pattern : Twelve) : d133 (change pattern 6 12) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 6 12) else d124 (change pattern 6 12)) = d133 pattern
  rw [s5251, s5432]
  rfl
theorem s5434 (pattern : Twelve) : d142 (change pattern 6 12) = d142 pattern := by
  change (if pattern.f then d133 (change pattern 6 12) else d59 (change pattern 6 12)) = d142 pattern
  rw [s5433, s5195]
  rfl
theorem s5435 (pattern : Twelve) : d126 (change pattern 6 12) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 6 12) else d2 (change pattern 6 12)) = d126 pattern
  rw [s5165, s5158]
  rfl
theorem s5436 (pattern : Twelve) : d47 (change pattern 6 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d3 (change pattern 6 12)) = d47 pattern
  rw [s5169, s5160]
  rfl
theorem s5437 (pattern : Twelve) : d134 (change pattern 6 12) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 6 12) else d126 (change pattern 6 12)) = d134 pattern
  rw [s5436, s5435]
  rfl
theorem s5438 (pattern : Twelve) : d135 (change pattern 6 12) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 6 12) else d127 (change pattern 6 12)) = d135 pattern
  rw [s5319, s5244]
  rfl
theorem s5439 (pattern : Twelve) : d143 (change pattern 6 12) = d143 pattern := by
  change (if pattern.f then d135 (change pattern 6 12) else d134 (change pattern 6 12)) = d143 pattern
  rw [s5438, s5437]
  rfl
theorem s5440 (pattern : Twelve) : d148 (change pattern 6 12) = d148 pattern := by
  change (if pattern.e then d143 (change pattern 6 12) else d142 (change pattern 6 12)) = d148 pattern
  rw [s5439, s5434]
  rfl
theorem s5441 (pattern : Twelve) : d151 (change pattern 6 12) = d151 pattern := by
  change (if pattern.j then d148 (change pattern 6 12) else d147 (change pattern 6 12)) = d151 pattern
  rw [s5440, s5431]
  rfl
theorem s5442 (pattern : Twelve) : d152 (change pattern 6 12) = d152 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d146 (change pattern 6 12)) = d152 pattern
  rw [s5169, s5422]
  rfl
theorem s5443 (pattern : Twelve) : d154 (change pattern 6 12) = d154 pattern := by
  change (if pattern.d then d152 (change pattern 6 12) else d151 (change pattern 6 12)) = d154 pattern
  rw [s5442, s5441]
  rfl
theorem s5444 (pattern : Twelve) : d155 (change pattern 6 12) = d155 pattern := by
  change (if pattern.c then d154 (change pattern 6 12) else d153 (change pattern 6 12)) = d155 pattern
  rw [s5443, s5424]
  rfl
theorem s5445 (pattern : Twelve) : d808 (change pattern 6 12) = d155 pattern := by
  change d155 (change pattern 6 12) = d155 pattern
  exact s5444 pattern
theorem s5446 (pattern : Twelve) : d809 (change pattern 6 12) = d156 pattern := by
  change (if pattern.a then d808 (change pattern 6 12) else d807 (change pattern 6 12)) = d156 pattern
  rw [s5445, s5410]
  rfl
theorem s5447 (pattern : Twelve) : d0 (change pattern 1 12) = d0 pattern := by
  rfl
theorem s5448 (pattern : Twelve) : d1 (change pattern 1 12) = d1 pattern := by
  rfl
theorem s5449 (pattern : Twelve) : d7 (change pattern 1 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 1 12) else d0 (change pattern 1 12)) = d7 pattern
  rw [s5448, s5447]
  rfl
theorem s5450 (pattern : Twelve) : d17 (change pattern 1 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 1 12) else d0 (change pattern 1 12)) = d17 pattern
  rw [s5449, s5447]
  rfl
theorem s5451 (pattern : Twelve) : d27 (change pattern 1 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 1 12) else d17 (change pattern 1 12)) = d27 pattern
  rw [s5448, s5450]
  rfl
theorem s5452 (pattern : Twelve) : d814 (change pattern 1 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 1 12) else d7 (change pattern 1 12)) = d814 pattern
  rw [s5448, s5449]
  rfl
theorem s5453 (pattern : Twelve) : d816 (change pattern 1 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 1 12) else d814 (change pattern 1 12)) = d816 pattern
  rw [s5448, s5452]
  rfl
theorem s5454 (pattern : Twelve) : d824 (change pattern 1 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 1 12) else d27 (change pattern 1 12)) = d824 pattern
  rw [s5453, s5451]
  rfl
theorem s5455 (pattern : Twelve) : d838 (change pattern 1 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 1 12) else d0 (change pattern 1 12)) = d838 pattern
  rw [s5454, s5447]
  rfl
theorem s5456 (pattern : Twelve) : d2 (change pattern 1 12) = d2 pattern := by
  rfl
theorem s5457 (pattern : Twelve) : d10 (change pattern 1 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 1 12) else d0 (change pattern 1 12)) = d10 pattern
  rw [s5456, s5447]
  rfl
theorem s5458 (pattern : Twelve) : d3 (change pattern 1 12) = d3 pattern := by
  rfl
theorem s5459 (pattern : Twelve) : d11 (change pattern 1 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 1 12) else d1 (change pattern 1 12)) = d11 pattern
  rw [s5458, s5448]
  rfl
theorem s5460 (pattern : Twelve) : d19 (change pattern 1 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 1 12) else d10 (change pattern 1 12)) = d19 pattern
  rw [s5459, s5457]
  rfl
theorem s5461 (pattern : Twelve) : d4 (change pattern 1 12) = d4 pattern := by
  rfl
theorem s5462 (pattern : Twelve) : d16 (change pattern 1 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 1 12) else d2 (change pattern 1 12)) = d16 pattern
  rw [s5461, s5456]
  rfl
theorem s5463 (pattern : Twelve) : d5 (change pattern 1 12) = d5 pattern := by
  rfl
theorem s5464 (pattern : Twelve) : d12 (change pattern 1 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 1 12) else d3 (change pattern 1 12)) = d12 pattern
  rw [s5463, s5458]
  rfl
theorem s5465 (pattern : Twelve) : d25 (change pattern 1 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 1 12) else d16 (change pattern 1 12)) = d25 pattern
  rw [s5464, s5462]
  rfl
theorem s5466 (pattern : Twelve) : d817 (change pattern 1 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 1 12) else d19 (change pattern 1 12)) = d817 pattern
  rw [s5465, s5460]
  rfl
theorem s5467 (pattern : Twelve) : d6 (change pattern 1 12) = d6 pattern := by
  rfl
theorem s5468 (pattern : Twelve) : d42 (change pattern 1 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d25 (change pattern 1 12)) = d42 pattern
  rw [s5467, s5465]
  rfl
theorem s5469 (pattern : Twelve) : d825 (change pattern 1 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 1 12) else d817 (change pattern 1 12)) = d825 pattern
  rw [s5468, s5466]
  rfl
theorem s5470 (pattern : Twelve) : d839 (change pattern 1 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d17 (change pattern 1 12)) = d839 pattern
  rw [s5469, s5450]
  rfl
theorem s5471 (pattern : Twelve) : d853 (change pattern 1 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 1 12) else d838 (change pattern 1 12)) = d853 pattern
  rw [s5470, s5455]
  rfl
theorem s5472 (pattern : Twelve) : d30 (change pattern 1 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 1 12) else d0 (change pattern 1 12)) = d30 pattern
  rw [s5456, s5447]
  rfl
theorem s5473 (pattern : Twelve) : d35 (change pattern 1 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d0 (change pattern 1 12)) = d35 pattern
  rw [s5467, s5447]
  rfl
theorem s5474 (pattern : Twelve) : d56 (change pattern 1 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 1 12) else d30 (change pattern 1 12)) = d56 pattern
  rw [s5473, s5472]
  rfl
theorem s5475 (pattern : Twelve) : d9 (change pattern 1 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 1 12) else d2 (change pattern 1 12)) = d9 pattern
  rw [s5458, s5456]
  rfl
theorem s5476 (pattern : Twelve) : d23 (change pattern 1 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 1 12) else d2 (change pattern 1 12)) = d23 pattern
  rw [s5475, s5456]
  rfl
theorem s5477 (pattern : Twelve) : d34 (change pattern 1 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 1 12) else d17 (change pattern 1 12)) = d34 pattern
  rw [s5476, s5450]
  rfl
theorem s5478 (pattern : Twelve) : d818 (change pattern 1 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d814 (change pattern 1 12)) = d818 pattern
  rw [s5467, s5452]
  rfl
theorem s5479 (pattern : Twelve) : d826 (change pattern 1 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 1 12) else d34 (change pattern 1 12)) = d826 pattern
  rw [s5478, s5477]
  rfl
theorem s5480 (pattern : Twelve) : d840 (change pattern 1 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 1 12) else d56 (change pattern 1 12)) = d840 pattern
  rw [s5479, s5474]
  rfl
theorem s5481 (pattern : Twelve) : d36 (change pattern 1 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d17 (change pattern 1 12)) = d36 pattern
  rw [s5467, s5450]
  rfl
theorem s5482 (pattern : Twelve) : d827 (change pattern 1 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 1 12) else d34 (change pattern 1 12)) = d827 pattern
  rw [s5481, s5477]
  rfl
theorem s5483 (pattern : Twelve) : d841 (change pattern 1 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d827 (change pattern 1 12)) = d841 pattern
  rw [s5469, s5482]
  rfl
theorem s5484 (pattern : Twelve) : d854 (change pattern 1 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 1 12) else d840 (change pattern 1 12)) = d854 pattern
  rw [s5483, s5480]
  rfl
theorem s5485 (pattern : Twelve) : d861 (change pattern 1 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 1 12) else d853 (change pattern 1 12)) = d861 pattern
  rw [s5484, s5471]
  rfl
theorem s5486 (pattern : Twelve) : d819 (change pattern 1 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d814 (change pattern 1 12)) = d819 pattern
  rw [s5458, s5452]
  rfl
theorem s5487 (pattern : Twelve) : d828 (change pattern 1 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 1 12) else d34 (change pattern 1 12)) = d828 pattern
  rw [s5486, s5477]
  rfl
theorem s5488 (pattern : Twelve) : d842 (change pattern 1 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 1 12) else d30 (change pattern 1 12)) = d842 pattern
  rw [s5487, s5472]
  rfl
theorem s5489 (pattern : Twelve) : d843 (change pattern 1 12) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d34 (change pattern 1 12)) = d843 pattern
  rw [s5469, s5477]
  rfl
theorem s5490 (pattern : Twelve) : d855 (change pattern 1 12) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 1 12) else d842 (change pattern 1 12)) = d855 pattern
  rw [s5489, s5488]
  rfl
theorem s5491 (pattern : Twelve) : d38 (change pattern 1 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 1 12) else d2 (change pattern 1 12)) = d38 pattern
  rw [s5461, s5456]
  rfl
theorem s5492 (pattern : Twelve) : d39 (change pattern 1 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d2 (change pattern 1 12)) = d39 pattern
  rw [s5467, s5456]
  rfl
theorem s5493 (pattern : Twelve) : d59 (change pattern 1 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 1 12) else d38 (change pattern 1 12)) = d59 pattern
  rw [s5492, s5491]
  rfl
theorem s5494 (pattern : Twelve) : d15 (change pattern 1 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 1 12) else d4 (change pattern 1 12)) = d15 pattern
  rw [s5463, s5461]
  rfl
theorem s5495 (pattern : Twelve) : d24 (change pattern 1 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 1 12) else d4 (change pattern 1 12)) = d24 pattern
  rw [s5494, s5461]
  rfl
theorem s5496 (pattern : Twelve) : d41 (change pattern 1 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 1 12) else d23 (change pattern 1 12)) = d41 pattern
  rw [s5495, s5476]
  rfl
theorem s5497 (pattern : Twelve) : d815 (change pattern 1 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 1 12) else d9 (change pattern 1 12)) = d815 pattern
  rw [s5458, s5475]
  rfl
theorem s5498 (pattern : Twelve) : d820 (change pattern 1 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d815 (change pattern 1 12)) = d820 pattern
  rw [s5467, s5497]
  rfl
theorem s5499 (pattern : Twelve) : d829 (change pattern 1 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 1 12) else d41 (change pattern 1 12)) = d829 pattern
  rw [s5498, s5496]
  rfl
theorem s5500 (pattern : Twelve) : d844 (change pattern 1 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 1 12) else d59 (change pattern 1 12)) = d844 pattern
  rw [s5499, s5493]
  rfl
theorem s5501 (pattern : Twelve) : d40 (change pattern 1 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d23 (change pattern 1 12)) = d40 pattern
  rw [s5467, s5476]
  rfl
theorem s5502 (pattern : Twelve) : d830 (change pattern 1 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 1 12) else d41 (change pattern 1 12)) = d830 pattern
  rw [s5501, s5496]
  rfl
theorem s5503 (pattern : Twelve) : d13 (change pattern 1 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 1 12) else d4 (change pattern 1 12)) = d13 pattern
  rw [s5467, s5461]
  rfl
theorem s5504 (pattern : Twelve) : d14 (change pattern 1 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 1 12) else d5 (change pattern 1 12)) = d14 pattern
  rw [s5467, s5463]
  rfl
theorem s5505 (pattern : Twelve) : d21 (change pattern 1 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 1 12) else d13 (change pattern 1 12)) = d21 pattern
  rw [s5504, s5503]
  rfl
theorem s5506 (pattern : Twelve) : d821 (change pattern 1 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 1 12) else d25 (change pattern 1 12)) = d821 pattern
  rw [s5505, s5465]
  rfl
theorem s5507 (pattern : Twelve) : d822 (change pattern 1 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d21 (change pattern 1 12)) = d822 pattern
  rw [s5467, s5505]
  rfl
theorem s5508 (pattern : Twelve) : d831 (change pattern 1 12) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 1 12) else d821 (change pattern 1 12)) = d831 pattern
  rw [s5507, s5506]
  rfl
theorem s5509 (pattern : Twelve) : d845 (change pattern 1 12) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 1 12) else d830 (change pattern 1 12)) = d845 pattern
  rw [s5508, s5502]
  rfl
theorem s5510 (pattern : Twelve) : d856 (change pattern 1 12) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 1 12) else d844 (change pattern 1 12)) = d856 pattern
  rw [s5509, s5500]
  rfl
theorem s5511 (pattern : Twelve) : d862 (change pattern 1 12) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 1 12) else d855 (change pattern 1 12)) = d862 pattern
  rw [s5510, s5490]
  rfl
theorem s5512 (pattern : Twelve) : d863 (change pattern 1 12) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d854 (change pattern 1 12)) = d863 pattern
  rw [s5467, s5484]
  rfl
theorem s5513 (pattern : Twelve) : d867 (change pattern 1 12) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 1 12) else d862 (change pattern 1 12)) = d867 pattern
  rw [s5512, s5511]
  rfl
theorem s5514 (pattern : Twelve) : d869 (change pattern 1 12) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 1 12) else d861 (change pattern 1 12)) = d869 pattern
  rw [s5513, s5485]
  rfl
theorem s5515 (pattern : Twelve) : d823 (change pattern 1 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 1 12) else d17 (change pattern 1 12)) = d823 pattern
  rw [s5456, s5450]
  rfl
theorem s5516 (pattern : Twelve) : d846 (change pattern 1 12) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d823 (change pattern 1 12)) = d846 pattern
  rw [s5469, s5515]
  rfl
theorem s5517 (pattern : Twelve) : d857 (change pattern 1 12) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 1 12) else d838 (change pattern 1 12)) = d857 pattern
  rw [s5516, s5455]
  rfl
theorem s5518 (pattern : Twelve) : d45 (change pattern 1 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d1 (change pattern 1 12)) = d45 pattern
  rw [s5467, s5448]
  rfl
theorem s5519 (pattern : Twelve) : d832 (change pattern 1 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 1 12) else d34 (change pattern 1 12)) = d832 pattern
  rw [s5518, s5477]
  rfl
theorem s5520 (pattern : Twelve) : d847 (change pattern 1 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 1 12) else d56 (change pattern 1 12)) = d847 pattern
  rw [s5519, s5474]
  rfl
theorem s5521 (pattern : Twelve) : d833 (change pattern 1 12) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 1 12) else d34 (change pattern 1 12)) = d833 pattern
  rw [s5492, s5477]
  rfl
theorem s5522 (pattern : Twelve) : d848 (change pattern 1 12) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d833 (change pattern 1 12)) = d848 pattern
  rw [s5469, s5521]
  rfl
theorem s5523 (pattern : Twelve) : d858 (change pattern 1 12) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 1 12) else d847 (change pattern 1 12)) = d858 pattern
  rw [s5522, s5520]
  rfl
theorem s5524 (pattern : Twelve) : d864 (change pattern 1 12) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 1 12) else d857 (change pattern 1 12)) = d864 pattern
  rw [s5523, s5517]
  rfl
theorem s5525 (pattern : Twelve) : d46 (change pattern 1 12) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d1 (change pattern 1 12)) = d46 pattern
  rw [s5458, s5448]
  rfl
theorem s5526 (pattern : Twelve) : d834 (change pattern 1 12) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 1 12) else d34 (change pattern 1 12)) = d834 pattern
  rw [s5525, s5477]
  rfl
theorem s5527 (pattern : Twelve) : d849 (change pattern 1 12) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 1 12) else d30 (change pattern 1 12)) = d849 pattern
  rw [s5526, s5472]
  rfl
theorem s5528 (pattern : Twelve) : d835 (change pattern 1 12) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 1 12) else d34 (change pattern 1 12)) = d835 pattern
  rw [s5491, s5477]
  rfl
theorem s5529 (pattern : Twelve) : d850 (change pattern 1 12) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 1 12) else d835 (change pattern 1 12)) = d850 pattern
  rw [s5469, s5528]
  rfl
theorem s5530 (pattern : Twelve) : d859 (change pattern 1 12) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 1 12) else d849 (change pattern 1 12)) = d859 pattern
  rw [s5529, s5527]
  rfl
theorem s5531 (pattern : Twelve) : d47 (change pattern 1 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d3 (change pattern 1 12)) = d47 pattern
  rw [s5467, s5458]
  rfl
theorem s5532 (pattern : Twelve) : d836 (change pattern 1 12) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 1 12) else d41 (change pattern 1 12)) = d836 pattern
  rw [s5531, s5496]
  rfl
theorem s5533 (pattern : Twelve) : d851 (change pattern 1 12) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 1 12) else d59 (change pattern 1 12)) = d851 pattern
  rw [s5532, s5493]
  rfl
theorem s5534 (pattern : Twelve) : d48 (change pattern 1 12) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d4 (change pattern 1 12)) = d48 pattern
  rw [s5467, s5461]
  rfl
theorem s5535 (pattern : Twelve) : d837 (change pattern 1 12) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 1 12) else d41 (change pattern 1 12)) = d837 pattern
  rw [s5534, s5496]
  rfl
theorem s5536 (pattern : Twelve) : d852 (change pattern 1 12) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 1 12) else d837 (change pattern 1 12)) = d852 pattern
  rw [s5508, s5535]
  rfl
theorem s5537 (pattern : Twelve) : d860 (change pattern 1 12) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 1 12) else d851 (change pattern 1 12)) = d860 pattern
  rw [s5536, s5533]
  rfl
theorem s5538 (pattern : Twelve) : d865 (change pattern 1 12) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 1 12) else d859 (change pattern 1 12)) = d865 pattern
  rw [s5537, s5530]
  rfl
theorem s5539 (pattern : Twelve) : d866 (change pattern 1 12) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d858 (change pattern 1 12)) = d866 pattern
  rw [s5467, s5523]
  rfl
theorem s5540 (pattern : Twelve) : d868 (change pattern 1 12) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 1 12) else d865 (change pattern 1 12)) = d868 pattern
  rw [s5539, s5538]
  rfl
theorem s5541 (pattern : Twelve) : d870 (change pattern 1 12) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 1 12) else d864 (change pattern 1 12)) = d870 pattern
  rw [s5540, s5524]
  rfl
theorem s5542 (pattern : Twelve) : d871 (change pattern 1 12) = d871 pattern := by
  change (if pattern.g then d870 (change pattern 1 12) else d869 (change pattern 1 12)) = d871 pattern
  rw [s5541, s5514]
  rfl
theorem s5543 (pattern : Twelve) : d1271 (change pattern 1 12) = d871 pattern := by
  change d871 (change pattern 1 12) = d871 pattern
  exact s5542 pattern
theorem s5544 (pattern : Twelve) : d8 (change pattern 1 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 1 12) else d1 (change pattern 1 12)) = d8 pattern
  rw [s5456, s5448]
  rfl
theorem s5545 (pattern : Twelve) : d872 (change pattern 1 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 1 12) else d1 (change pattern 1 12)) = d872 pattern
  rw [s5544, s5448]
  rfl
theorem s5546 (pattern : Twelve) : d874 (change pattern 1 12) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 1 12) else d17 (change pattern 1 12)) = d874 pattern
  rw [s5545, s5450]
  rfl
theorem s5547 (pattern : Twelve) : d875 (change pattern 1 12) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 1 12) else d814 (change pattern 1 12)) = d875 pattern
  rw [s5545, s5452]
  rfl
theorem s5548 (pattern : Twelve) : d882 (change pattern 1 12) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 1 12) else d874 (change pattern 1 12)) = d882 pattern
  rw [s5547, s5546]
  rfl
theorem s5549 (pattern : Twelve) : d890 (change pattern 1 12) = d890 pattern := by
  change (if pattern.f then d882 (change pattern 1 12) else d0 (change pattern 1 12)) = d890 pattern
  rw [s5548, s5447]
  rfl
end NetHack.Sokoban21.Diagram
