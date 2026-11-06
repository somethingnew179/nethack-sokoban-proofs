/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub480 (p : Pattern) : d12 (change p 133 (some 134)) = d12 p := by
  change (if p 168 then d11 (change p 133 (some 134)) else d7 (change p 133 (some 134))) = d12 p
  rw [sub479, sub467]
  rfl
theorem sub481 (p : Pattern) : d5 (change p 133 (some 134)) = d5 p := by
  rfl
theorem sub482 (p : Pattern) : d58 (change p 133 (some 134)) = d58 p := by
  change (if p 271 then d5 (change p 133 (some 134)) else d4 (change p 133 (some 134))) = d58 p
  rw [sub481, sub468]
  rfl
theorem sub483 (p : Pattern) : d59 (change p 133 (some 134)) = d59 p := by
  change (if p 193 then d58 (change p 133 (some 134)) else d9 (change p 133 (some 134))) = d59 p
  rw [sub482, sub477]
  rfl
theorem sub484 (p : Pattern) : d60 (change p 133 (some 134)) = d60 p := by
  change (if p 192 then d59 (change p 133 (some 134)) else d9 (change p 133 (some 134))) = d60 p
  rw [sub483, sub477]
  rfl
theorem sub485 (p : Pattern) : d65 (change p 133 (some 134)) = d65 p := by
  change (if p 168 then d60 (change p 133 (some 134)) else d55 (change p 133 (some 134))) = d65 p
  rw [sub484, sub470]
  rfl
theorem sub486 (p : Pattern) : d109 (change p 133 (some 134)) = d109 p := by
  change (if p 160 then d65 (change p 133 (some 134)) else d12 (change p 133 (some 134))) = d109 p
  rw [sub485, sub480]
  rfl
theorem sub487 (p : Pattern) : d110 (change p 133 (some 134)) = d110 p := by
  change (if p 159 then d65 (change p 133 (some 134)) else d109 (change p 133 (some 134))) = d110 p
  rw [sub485, sub486]
  rfl
theorem sub488 (p : Pattern) : d111 (change p 133 (some 134)) = d111 p := by
  change (if p 158 then d110 (change p 133 (some 134)) else d109 (change p 133 (some 134))) = d111 p
  rw [sub487, sub486]
  rfl
theorem sub489 (p : Pattern) : d112 (change p 133 (some 134)) = d112 p := by
  change (if p 141 then d111 (change p 133 (some 134)) else d108 (change p 133 (some 134))) = d112 p
  rw [sub488, sub473]
  rfl
theorem sub490 (p : Pattern) : d113 (change p 133 (some 134)) = d112 p := by
  change d112 (change p 133 (some 134)) = d112 p
  exact sub489 p
theorem sub491 (p : Pattern) : d210 (change p 133 (some 134)) = d112 p := by
  change d113 (change p 133 (some 134)) = d112 p
  exact sub490 p
theorem sub492 (p : Pattern) : d211 (change p 133 (some 134)) = d211 p := by
  change (if p 158 then d55 (change p 133 (some 134)) else d107 (change p 133 (some 134))) = d211 p
  rw [sub470, sub472]
  rfl
theorem sub493 (p : Pattern) : d212 (change p 133 (some 134)) = d212 p := by
  change (if p 158 then d65 (change p 133 (some 134)) else d110 (change p 133 (some 134))) = d212 p
  rw [sub485, sub487]
  rfl
theorem sub494 (p : Pattern) : d213 (change p 133 (some 134)) = d213 p := by
  change (if p 141 then d212 (change p 133 (some 134)) else d211 (change p 133 (some 134))) = d213 p
  rw [sub493, sub492]
  rfl
theorem sub495 (p : Pattern) : d214 (change p 133 (some 134)) = d213 p := by
  change d213 (change p 133 (some 134)) = d213 p
  exact sub494 p
theorem sub496 (p : Pattern) : d215 (change p 133 (some 134)) = d213 p := by
  change d214 (change p 133 (some 134)) = d213 p
  exact sub495 p
theorem sub497 (p : Pattern) : d216 (change p 133 (some 134)) = d791 p := by
  change (if p 132 then d215 (change p 133 (some 134)) else d210 (change p 133 (some 134))) = d791 p
  rw [sub496, sub491]
  rfl
theorem sub498 (p : Pattern) : d66 (change p 133 (some 134)) = d66 p := by
  change (if p 141 then d65 (change p 133 (some 134)) else d55 (change p 133 (some 134))) = d66 p
  rw [sub485, sub470]
  rfl
theorem sub499 (p : Pattern) : d67 (change p 133 (some 134)) = d66 p := by
  change d66 (change p 133 (some 134)) = d66 p
  exact sub498 p
theorem sub500 (p : Pattern) : d217 (change p 133 (some 134)) = d66 p := by
  change d67 (change p 133 (some 134)) = d66 p
  exact sub499 p
theorem sub501 (p : Pattern) : d71 (change p 133 (some 134)) = d66 p := by
  change d66 (change p 133 (some 134)) = d66 p
  exact sub498 p
theorem sub502 (p : Pattern) : d73 (change p 133 (some 134)) = d66 p := by
  change d71 (change p 133 (some 134)) = d66 p
  exact sub501 p
theorem sub503 (p : Pattern) : d218 (change p 133 (some 134)) = d66 p := by
  change (if p 132 then d73 (change p 133 (some 134)) else d217 (change p 133 (some 134))) = d66 p
  rw [sub502, sub500]
  simp only [ite_self]
theorem sub504 (p : Pattern) : d219 (change p 133 (some 134)) = d792 p := by
  change (if p 108 then d218 (change p 133 (some 134)) else d216 (change p 133 (some 134))) = d792 p
  rw [sub503, sub497]
  rfl
theorem sub505 (p : Pattern) : d0 (change p 159 none) = d0 p := by
  rfl
theorem sub506 (p : Pattern) : d2 (change p 159 none) = d2 p := by
  rfl
theorem sub507 (p : Pattern) : d6 (change p 159 none) = d6 p := by
  change (if p 193 then d2 (change p 159 none) else d0 (change p 159 none)) = d6 p
  rw [sub506, sub505]
  rfl
theorem sub508 (p : Pattern) : d7 (change p 159 none) = d7 p := by
  change (if p 192 then d6 (change p 159 none) else d0 (change p 159 none)) = d7 p
  rw [sub507, sub505]
  rfl
theorem sub509 (p : Pattern) : d4 (change p 159 none) = d4 p := by
  rfl
theorem sub510 (p : Pattern) : d54 (change p 159 none) = d54 p := by
  change (if p 193 then d4 (change p 159 none) else d2 (change p 159 none)) = d54 p
  rw [sub509, sub506]
  rfl
theorem sub511 (p : Pattern) : d55 (change p 159 none) = d55 p := by
  change (if p 192 then d54 (change p 159 none) else d2 (change p 159 none)) = d55 p
  rw [sub510, sub506]
  rfl
theorem sub512 (p : Pattern) : d56 (change p 159 none) = d56 p := by
  change (if p 186 then d55 (change p 159 none) else d7 (change p 159 none)) = d56 p
  rw [sub511, sub508]
  rfl
theorem sub513 (p : Pattern) : d57 (change p 159 none) = d57 p := by
  change (if p 160 then d56 (change p 159 none) else d7 (change p 159 none)) = d57 p
  rw [sub512, sub508]
  rfl
theorem sub514 (p : Pattern) : d114 (change p 159 none) = d57 p := by
  change d57 (change p 159 none) = d57 p
  exact sub513 p
theorem sub515 (p : Pattern) : d1 (change p 159 none) = d1 p := by
  rfl
theorem sub516 (p : Pattern) : d8 (change p 159 none) = d8 p := by
  change (if p 271 then d1 (change p 159 none) else d0 (change p 159 none)) = d8 p
  rw [sub515, sub505]
  rfl
theorem sub517 (p : Pattern) : d3 (change p 159 none) = d3 p := by
  rfl
theorem sub518 (p : Pattern) : d9 (change p 159 none) = d9 p := by
  change (if p 271 then d3 (change p 159 none) else d2 (change p 159 none)) = d9 p
  rw [sub517, sub506]
  rfl
theorem sub519 (p : Pattern) : d10 (change p 159 none) = d10 p := by
  change (if p 193 then d9 (change p 159 none) else d8 (change p 159 none)) = d10 p
  rw [sub518, sub516]
  rfl
theorem sub520 (p : Pattern) : d11 (change p 159 none) = d11 p := by
  change (if p 192 then d10 (change p 159 none) else d8 (change p 159 none)) = d11 p
  rw [sub519, sub516]
  rfl
theorem sub521 (p : Pattern) : d12 (change p 159 none) = d12 p := by
  change (if p 168 then d11 (change p 159 none) else d7 (change p 159 none)) = d12 p
  rw [sub520, sub508]
  rfl
theorem sub522 (p : Pattern) : d5 (change p 159 none) = d5 p := by
  rfl
theorem sub523 (p : Pattern) : d58 (change p 159 none) = d58 p := by
  change (if p 271 then d5 (change p 159 none) else d4 (change p 159 none)) = d58 p
  rw [sub522, sub509]
  rfl
theorem sub524 (p : Pattern) : d59 (change p 159 none) = d59 p := by
  change (if p 193 then d58 (change p 159 none) else d9 (change p 159 none)) = d59 p
  rw [sub523, sub518]
  rfl
theorem sub525 (p : Pattern) : d60 (change p 159 none) = d60 p := by
  change (if p 192 then d59 (change p 159 none) else d9 (change p 159 none)) = d60 p
  rw [sub524, sub518]
  rfl
theorem sub526 (p : Pattern) : d61 (change p 159 none) = d61 p := by
  change (if p 186 then d60 (change p 159 none) else d11 (change p 159 none)) = d61 p
  rw [sub525, sub520]
  rfl
theorem sub527 (p : Pattern) : d62 (change p 159 none) = d62 p := by
  change (if p 168 then d61 (change p 159 none) else d56 (change p 159 none)) = d62 p
  rw [sub526, sub512]
  rfl
theorem sub528 (p : Pattern) : d63 (change p 159 none) = d63 p := by
  change (if p 160 then d62 (change p 159 none) else d12 (change p 159 none)) = d63 p
  rw [sub527, sub521]
  rfl
theorem sub529 (p : Pattern) : d116 (change p 159 none) = d63 p := by
  change d63 (change p 159 none) = d63 p
  exact sub528 p
theorem sub530 (p : Pattern) : d335 (change p 159 none) = d64 p := by
  change (if p 141 then d116 (change p 159 none) else d114 (change p 159 none)) = d64 p
  rw [sub529, sub514]
  rfl
theorem sub531 (p : Pattern) : d106 (change p 159 none) = d106 p := by
  change (if p 160 then d55 (change p 159 none) else d7 (change p 159 none)) = d106 p
  rw [sub511, sub508]
  rfl
theorem sub532 (p : Pattern) : d107 (change p 159 none) = d106 p := by
  change d106 (change p 159 none) = d106 p
  exact sub531 p
theorem sub533 (p : Pattern) : d65 (change p 159 none) = d65 p := by
  change (if p 168 then d60 (change p 159 none) else d55 (change p 159 none)) = d65 p
  rw [sub525, sub511]
  rfl
theorem sub534 (p : Pattern) : d109 (change p 159 none) = d109 p := by
  change (if p 160 then d65 (change p 159 none) else d12 (change p 159 none)) = d109 p
  rw [sub533, sub521]
  rfl
theorem sub535 (p : Pattern) : d110 (change p 159 none) = d109 p := by
  change d109 (change p 159 none) = d109 p
  exact sub534 p
theorem sub536 (p : Pattern) : d336 (change p 159 none) = d227 p := by
  change (if p 141 then d110 (change p 159 none) else d107 (change p 159 none)) = d227 p
  rw [sub535, sub532]
  rfl
theorem sub537 (p : Pattern) : d337 (change p 159 none) = d228 p := by
  change (if p 134 then d336 (change p 159 none) else d335 (change p 159 none)) = d228 p
  rw [sub536, sub530]
  rfl
theorem sub538 (p : Pattern) : d338 (change p 159 none) = d68 p := by
  change (if p 158 then d55 (change p 159 none) else d114 (change p 159 none)) = d68 p
  rw [sub511, sub514]
  rfl
theorem sub539 (p : Pattern) : d339 (change p 159 none) = d69 p := by
  change (if p 158 then d65 (change p 159 none) else d116 (change p 159 none)) = d69 p
  rw [sub533, sub529]
  rfl
theorem sub540 (p : Pattern) : d340 (change p 159 none) = d70 p := by
  change (if p 141 then d339 (change p 159 none) else d338 (change p 159 none)) = d70 p
  rw [sub539, sub538]
  rfl
theorem sub541 (p : Pattern) : d211 (change p 159 none) = d229 p := by
  change (if p 158 then d55 (change p 159 none) else d107 (change p 159 none)) = d229 p
  rw [sub511, sub532]
  rfl
theorem sub542 (p : Pattern) : d212 (change p 159 none) = d230 p := by
  change (if p 158 then d65 (change p 159 none) else d110 (change p 159 none)) = d230 p
  rw [sub533, sub535]
  rfl
theorem sub543 (p : Pattern) : d213 (change p 159 none) = d231 p := by
  change (if p 141 then d212 (change p 159 none) else d211 (change p 159 none)) = d231 p
  rw [sub542, sub541]
  rfl
theorem sub544 (p : Pattern) : d341 (change p 159 none) = d232 p := by
  change (if p 134 then d213 (change p 159 none) else d340 (change p 159 none)) = d232 p
  rw [sub543, sub540]
  rfl
theorem sub545 (p : Pattern) : d342 (change p 159 none) = d233 p := by
  change (if p 133 then d341 (change p 159 none) else d337 (change p 159 none)) = d233 p
  rw [sub544, sub537]
  rfl
theorem sub546 (p : Pattern) : d66 (change p 159 none) = d66 p := by
  change (if p 141 then d65 (change p 159 none) else d55 (change p 159 none)) = d66 p
  rw [sub533, sub511]
  rfl
theorem sub547 (p : Pattern) : d343 (change p 159 none) = d234 p := by
  change (if p 133 then d66 (change p 159 none) else d341 (change p 159 none)) = d234 p
  rw [sub546, sub544]
  rfl
theorem sub548 (p : Pattern) : d344 (change p 159 none) = d235 p := by
  change (if p 132 then d343 (change p 159 none) else d342 (change p 159 none)) = d235 p
  rw [sub547, sub545]
  rfl
theorem sub549 (p : Pattern) : d345 (change p 159 none) = d67 p := by
  change (if p 134 then d66 (change p 159 none) else d335 (change p 159 none)) = d67 p
  rw [sub546, sub530]
  rfl
theorem sub550 (p : Pattern) : d119 (change p 159 none) = d119 p := by
  change (if p 187 then d55 (change p 159 none) else d7 (change p 159 none)) = d119 p
  rw [sub511, sub508]
  rfl
theorem sub551 (p : Pattern) : d137 (change p 159 none) = d137 p := by
  change (if p 186 then d55 (change p 159 none) else d119 (change p 159 none)) = d137 p
  rw [sub511, sub550]
  rfl
theorem sub552 (p : Pattern) : d138 (change p 159 none) = d138 p := by
  change (if p 160 then d137 (change p 159 none) else d7 (change p 159 none)) = d138 p
  rw [sub551, sub508]
  rfl
theorem sub553 (p : Pattern) : d346 (change p 159 none) = d138 p := by
  change d138 (change p 159 none) = d138 p
  exact sub552 p
theorem sub554 (p : Pattern) : d347 (change p 159 none) = d803 p := by
  change (if p 158 then d55 (change p 159 none) else d346 (change p 159 none)) = d803 p
  rw [sub511, sub553]
  rfl
theorem sub555 (p : Pattern) : d125 (change p 159 none) = d125 p := by
  change (if p 187 then d60 (change p 159 none) else d11 (change p 159 none)) = d125 p
  rw [sub525, sub520]
  rfl
theorem sub556 (p : Pattern) : d143 (change p 159 none) = d143 p := by
  change (if p 186 then d60 (change p 159 none) else d125 (change p 159 none)) = d143 p
  rw [sub525, sub555]
  rfl
theorem sub557 (p : Pattern) : d144 (change p 159 none) = d144 p := by
  change (if p 168 then d143 (change p 159 none) else d137 (change p 159 none)) = d144 p
  rw [sub556, sub551]
  rfl
theorem sub558 (p : Pattern) : d145 (change p 159 none) = d145 p := by
  change (if p 160 then d144 (change p 159 none) else d12 (change p 159 none)) = d145 p
  rw [sub557, sub521]
  rfl
theorem sub559 (p : Pattern) : d348 (change p 159 none) = d145 p := by
  change d145 (change p 159 none) = d145 p
  exact sub558 p
theorem sub560 (p : Pattern) : d349 (change p 159 none) = d804 p := by
  change (if p 158 then d65 (change p 159 none) else d348 (change p 159 none)) = d804 p
  rw [sub533, sub559]
  rfl
theorem sub561 (p : Pattern) : d350 (change p 159 none) = d805 p := by
  change (if p 141 then d349 (change p 159 none) else d347 (change p 159 none)) = d805 p
  rw [sub560, sub554]
  rfl
theorem sub562 (p : Pattern) : d351 (change p 159 none) = d806 p := by
  change (if p 134 then d66 (change p 159 none) else d350 (change p 159 none)) = d806 p
  rw [sub546, sub561]
  rfl
theorem sub563 (p : Pattern) : d352 (change p 159 none) = d807 p := by
  change (if p 133 then d351 (change p 159 none) else d345 (change p 159 none)) = d807 p
  rw [sub562, sub549]
  rfl
theorem sub564 (p : Pattern) : d353 (change p 159 none) = d71 p := by
  change (if p 134 then d66 (change p 159 none) else d340 (change p 159 none)) = d71 p
  rw [sub546, sub540]
  rfl
theorem sub565 (p : Pattern) : d354 (change p 159 none) = d73 p := by
  change (if p 133 then d66 (change p 159 none) else d353 (change p 159 none)) = d73 p
  rw [sub546, sub564]
  rfl
theorem sub566 (p : Pattern) : d355 (change p 159 none) = d808 p := by
  change (if p 132 then d354 (change p 159 none) else d352 (change p 159 none)) = d808 p
  rw [sub565, sub563]
  rfl
theorem sub567 (p : Pattern) : d356 (change p 159 none) = d809 p := by
  change (if p 108 then d355 (change p 159 none) else d344 (change p 159 none)) = d809 p
  rw [sub566, sub548]
  rfl
theorem sub568 (p : Pattern) : d0 (change p 134 none) = d0 p := by
  rfl
theorem sub569 (p : Pattern) : d2 (change p 134 none) = d2 p := by
  rfl
theorem sub570 (p : Pattern) : d6 (change p 134 none) = d6 p := by
  change (if p 193 then d2 (change p 134 none) else d0 (change p 134 none)) = d6 p
  rw [sub569, sub568]
  rfl
theorem sub571 (p : Pattern) : d7 (change p 134 none) = d7 p := by
  change (if p 192 then d6 (change p 134 none) else d0 (change p 134 none)) = d7 p
  rw [sub570, sub568]
  rfl
theorem sub572 (p : Pattern) : d4 (change p 134 none) = d4 p := by
  rfl
theorem sub573 (p : Pattern) : d54 (change p 134 none) = d54 p := by
  change (if p 193 then d4 (change p 134 none) else d2 (change p 134 none)) = d54 p
  rw [sub572, sub569]
  rfl
theorem sub574 (p : Pattern) : d55 (change p 134 none) = d55 p := by
  change (if p 192 then d54 (change p 134 none) else d2 (change p 134 none)) = d55 p
  rw [sub573, sub569]
  rfl
theorem sub575 (p : Pattern) : d56 (change p 134 none) = d56 p := by
  change (if p 186 then d55 (change p 134 none) else d7 (change p 134 none)) = d56 p
  rw [sub574, sub571]
  rfl
theorem sub576 (p : Pattern) : d57 (change p 134 none) = d57 p := by
  change (if p 160 then d56 (change p 134 none) else d7 (change p 134 none)) = d57 p
  rw [sub575, sub571]
  rfl
theorem sub577 (p : Pattern) : d1 (change p 134 none) = d1 p := by
  rfl
theorem sub578 (p : Pattern) : d8 (change p 134 none) = d8 p := by
  change (if p 271 then d1 (change p 134 none) else d0 (change p 134 none)) = d8 p
  rw [sub577, sub568]
  rfl
theorem sub579 (p : Pattern) : d3 (change p 134 none) = d3 p := by
  rfl
theorem sub580 (p : Pattern) : d9 (change p 134 none) = d9 p := by
  change (if p 271 then d3 (change p 134 none) else d2 (change p 134 none)) = d9 p
  rw [sub579, sub569]
  rfl
theorem sub581 (p : Pattern) : d10 (change p 134 none) = d10 p := by
  change (if p 193 then d9 (change p 134 none) else d8 (change p 134 none)) = d10 p
  rw [sub580, sub578]
  rfl
theorem sub582 (p : Pattern) : d11 (change p 134 none) = d11 p := by
  change (if p 192 then d10 (change p 134 none) else d8 (change p 134 none)) = d11 p
  rw [sub581, sub578]
  rfl
theorem sub583 (p : Pattern) : d12 (change p 134 none) = d12 p := by
  change (if p 168 then d11 (change p 134 none) else d7 (change p 134 none)) = d12 p
  rw [sub582, sub571]
  rfl
theorem sub584 (p : Pattern) : d5 (change p 134 none) = d5 p := by
  rfl
theorem sub585 (p : Pattern) : d58 (change p 134 none) = d58 p := by
  change (if p 271 then d5 (change p 134 none) else d4 (change p 134 none)) = d58 p
  rw [sub584, sub572]
  rfl
theorem sub586 (p : Pattern) : d59 (change p 134 none) = d59 p := by
  change (if p 193 then d58 (change p 134 none) else d9 (change p 134 none)) = d59 p
  rw [sub585, sub580]
  rfl
theorem sub587 (p : Pattern) : d60 (change p 134 none) = d60 p := by
  change (if p 192 then d59 (change p 134 none) else d9 (change p 134 none)) = d60 p
  rw [sub586, sub580]
  rfl
theorem sub588 (p : Pattern) : d61 (change p 134 none) = d61 p := by
  change (if p 186 then d60 (change p 134 none) else d11 (change p 134 none)) = d61 p
  rw [sub587, sub582]
  rfl
theorem sub589 (p : Pattern) : d62 (change p 134 none) = d62 p := by
  change (if p 168 then d61 (change p 134 none) else d56 (change p 134 none)) = d62 p
  rw [sub588, sub575]
  rfl
theorem sub590 (p : Pattern) : d63 (change p 134 none) = d63 p := by
  change (if p 160 then d62 (change p 134 none) else d12 (change p 134 none)) = d63 p
  rw [sub589, sub583]
  rfl
theorem sub591 (p : Pattern) : d64 (change p 134 none) = d64 p := by
  change (if p 141 then d63 (change p 134 none) else d57 (change p 134 none)) = d64 p
  rw [sub590, sub576]
  rfl
theorem sub592 (p : Pattern) : d67 (change p 134 none) = d64 p := by
  change d64 (change p 134 none) = d64 p
  exact sub591 p
theorem sub593 (p : Pattern) : d68 (change p 134 none) = d68 p := by
  change (if p 158 then d55 (change p 134 none) else d57 (change p 134 none)) = d68 p
  rw [sub574, sub576]
  rfl
theorem sub594 (p : Pattern) : d65 (change p 134 none) = d65 p := by
  change (if p 168 then d60 (change p 134 none) else d55 (change p 134 none)) = d65 p
  rw [sub587, sub574]
  rfl
theorem sub595 (p : Pattern) : d69 (change p 134 none) = d69 p := by
  change (if p 158 then d65 (change p 134 none) else d63 (change p 134 none)) = d69 p
  rw [sub594, sub590]
  rfl
theorem sub596 (p : Pattern) : d70 (change p 134 none) = d70 p := by
  change (if p 141 then d69 (change p 134 none) else d68 (change p 134 none)) = d70 p
  rw [sub595, sub593]
  rfl
theorem sub597 (p : Pattern) : d71 (change p 134 none) = d70 p := by
  change d70 (change p 134 none) = d70 p
  exact sub596 p
theorem sub598 (p : Pattern) : d72 (change p 134 none) = d811 p := by
  change (if p 133 then d71 (change p 134 none) else d67 (change p 134 none)) = d811 p
  rw [sub597, sub592]
  rfl
theorem sub599 (p : Pattern) : d66 (change p 134 none) = d66 p := by
  change (if p 141 then d65 (change p 134 none) else d55 (change p 134 none)) = d66 p
  rw [sub594, sub574]
  rfl
end NetHack.Sokoban12CostPartition
