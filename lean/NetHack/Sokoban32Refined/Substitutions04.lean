/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub480 (p : Pattern) : d69 (change p 106 (some 132)) = d69 p := by
  change (if p 138 then d68 (change p 106 (some 132)) else d40 (change p 106 (some 132))) = d69 p
  rw [sub479, sub434]
  rfl
theorem sub481 (p : Pattern) : d72 (change p 106 (some 132)) = d72 p := by
  change (if p 134 then d71 (change p 106 (some 132)) else d69 (change p 106 (some 132))) = d72 p
  rw [sub477, sub480]
  rfl
theorem sub482 (p : Pattern) : d101 (change p 106 (some 132)) = d101 p := by
  change (if p 133 then d72 (change p 106 (some 132)) else d99 (change p 106 (some 132))) = d101 p
  rw [sub481, sub478]
  rfl
theorem sub483 (p : Pattern) : d102 (change p 106 (some 132)) = d101 p := by
  change d101 (change p 106 (some 132)) = d101 p
  exact sub482 p
theorem sub484 (p : Pattern) : d103 (change p 106 (some 132)) = d847 p := by
  change (if p 112 then d102 (change p 106 (some 132)) else d96 (change p 106 (some 132))) = d847 p
  rw [sub483, sub473]
  rfl
theorem sub485 (p : Pattern) : d178 (change p 106 (some 132)) = d847 p := by
  change d103 (change p 106 (some 132)) = d847 p
  exact sub484 p
theorem sub486 (p : Pattern) : d179 (change p 106 (some 132)) = d848 p := by
  change (if p 86 then d178 (change p 106 (some 132)) else d177 (change p 106 (some 132))) = d848 p
  rw [sub485, sub464]
  rfl
theorem sub487 (p : Pattern) : d180 (change p 106 (some 132)) = d845 p := by
  change d67 (change p 106 (some 132)) = d845 p
  exact sub463 p
theorem sub488 (p : Pattern) : d119 (change p 106 (some 132)) = d119 p := by
  change (if p 139 then d20 (change p 106 (some 132)) else d33 (change p 106 (some 132))) = d119 p
  rw [sub440, sub423]
  rfl
theorem sub489 (p : Pattern) : d120 (change p 106 (some 132)) = d120 p := by
  change (if p 138 then d58 (change p 106 (some 132)) else d119 (change p 106 (some 132))) = d120 p
  rw [sub452, sub488]
  rfl
theorem sub490 (p : Pattern) : d121 (change p 106 (some 132)) = d121 p := by
  change (if p 134 then d120 (change p 106 (some 132)) else d86 (change p 106 (some 132))) = d121 p
  rw [sub489, sub465]
  rfl
theorem sub491 (p : Pattern) : d122 (change p 106 (some 132)) = d122 p := by
  change (if p 133 then d93 (change p 106 (some 132)) else d121 (change p 106 (some 132))) = d122 p
  rw [sub470, sub490]
  rfl
theorem sub492 (p : Pattern) : d123 (change p 106 (some 132)) = d122 p := by
  change d122 (change p 106 (some 132)) = d122 p
  exact sub491 p
theorem sub493 (p : Pattern) : d124 (change p 106 (some 132)) = d849 p := by
  change (if p 113 then d123 (change p 106 (some 132)) else d45 (change p 106 (some 132))) = d849 p
  rw [sub492, sub445]
  rfl
theorem sub494 (p : Pattern) : d109 (change p 106 (some 132)) = d109 p := by
  change (if p 134 then d70 (change p 106 (some 132)) else d97 (change p 106 (some 132))) = d109 p
  rw [sub476, sub474]
  rfl
theorem sub495 (p : Pattern) : d75 (change p 106 (some 132)) = d75 p := by
  change (if p 134 then d70 (change p 106 (some 132)) else d68 (change p 106 (some 132))) = d75 p
  rw [sub476, sub479]
  rfl
theorem sub496 (p : Pattern) : d125 (change p 106 (some 132)) = d125 p := by
  change (if p 133 then d75 (change p 106 (some 132)) else d109 (change p 106 (some 132))) = d125 p
  rw [sub495, sub494]
  rfl
theorem sub497 (p : Pattern) : d126 (change p 106 (some 132)) = d125 p := by
  change d125 (change p 106 (some 132)) = d125 p
  exact sub496 p
theorem sub498 (p : Pattern) : d127 (change p 106 (some 132)) = d850 p := by
  change (if p 113 then d126 (change p 106 (some 132)) else d102 (change p 106 (some 132))) = d850 p
  rw [sub497, sub483]
  rfl
theorem sub499 (p : Pattern) : d128 (change p 106 (some 132)) = d851 p := by
  change (if p 112 then d127 (change p 106 (some 132)) else d124 (change p 106 (some 132))) = d851 p
  rw [sub498, sub493]
  rfl
theorem sub500 (p : Pattern) : d181 (change p 106 (some 132)) = d851 p := by
  change d128 (change p 106 (some 132)) = d851 p
  exact sub499 p
theorem sub501 (p : Pattern) : d182 (change p 106 (some 132)) = d852 p := by
  change (if p 86 then d181 (change p 106 (some 132)) else d180 (change p 106 (some 132))) = d852 p
  rw [sub500, sub487]
  rfl
theorem sub502 (p : Pattern) : d183 (change p 106 (some 132)) = d853 p := by
  change (if p 80 then d182 (change p 106 (some 132)) else d179 (change p 106 (some 132))) = d853 p
  rw [sub501, sub486]
  rfl
theorem sub503 (p : Pattern) : d0 (change p 112 (some 138)) = d0 p := by
  rfl
theorem sub504 (p : Pattern) : d2 (change p 112 (some 138)) = d2 p := by
  rfl
theorem sub505 (p : Pattern) : d3 (change p 112 (some 138)) = d3 p := by
  change (if p 161 then d2 (change p 112 (some 138)) else d0 (change p 112 (some 138))) = d3 p
  rw [sub504, sub503]
  rfl
theorem sub506 (p : Pattern) : d4 (change p 112 (some 138)) = d4 p := by
  change (if p 160 then d3 (change p 112 (some 138)) else d0 (change p 112 (some 138))) = d4 p
  rw [sub505, sub503]
  rfl
theorem sub507 (p : Pattern) : d5 (change p 112 (some 138)) = d5 p := by
  change (if p 160 then d2 (change p 112 (some 138)) else d0 (change p 112 (some 138))) = d5 p
  rw [sub504, sub503]
  rfl
theorem sub508 (p : Pattern) : d6 (change p 112 (some 138)) = d6 p := by
  change (if p 159 then d5 (change p 112 (some 138)) else d4 (change p 112 (some 138))) = d6 p
  rw [sub507, sub506]
  rfl
theorem sub509 (p : Pattern) : d7 (change p 112 (some 138)) = d7 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d4 (change p 112 (some 138))) = d7 p
  rw [sub504, sub506]
  rfl
theorem sub510 (p : Pattern) : d8 (change p 112 (some 138)) = d8 p := by
  change (if p 158 then d7 (change p 112 (some 138)) else d6 (change p 112 (some 138))) = d8 p
  rw [sub509, sub508]
  rfl
theorem sub511 (p : Pattern) : d1 (change p 112 (some 138)) = d1 p := by
  rfl
theorem sub512 (p : Pattern) : d9 (change p 112 (some 138)) = d9 p := by
  change (if p 161 then d2 (change p 112 (some 138)) else d1 (change p 112 (some 138))) = d9 p
  rw [sub504, sub511]
  rfl
theorem sub513 (p : Pattern) : d10 (change p 112 (some 138)) = d10 p := by
  change (if p 160 then d9 (change p 112 (some 138)) else d1 (change p 112 (some 138))) = d10 p
  rw [sub512, sub511]
  rfl
theorem sub514 (p : Pattern) : d11 (change p 112 (some 138)) = d11 p := by
  change (if p 160 then d2 (change p 112 (some 138)) else d1 (change p 112 (some 138))) = d11 p
  rw [sub504, sub511]
  rfl
theorem sub515 (p : Pattern) : d12 (change p 112 (some 138)) = d12 p := by
  change (if p 159 then d11 (change p 112 (some 138)) else d10 (change p 112 (some 138))) = d12 p
  rw [sub514, sub513]
  rfl
theorem sub516 (p : Pattern) : d13 (change p 112 (some 138)) = d13 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d10 (change p 112 (some 138))) = d13 p
  rw [sub504, sub513]
  rfl
theorem sub517 (p : Pattern) : d14 (change p 112 (some 138)) = d14 p := by
  change (if p 158 then d13 (change p 112 (some 138)) else d12 (change p 112 (some 138))) = d14 p
  rw [sub516, sub515]
  rfl
theorem sub518 (p : Pattern) : d15 (change p 112 (some 138)) = d15 p := by
  change (if p 139 then d14 (change p 112 (some 138)) else d8 (change p 112 (some 138))) = d15 p
  rw [sub517, sub510]
  rfl
theorem sub519 (p : Pattern) : d16 (change p 112 (some 138)) = d15 p := by
  change d15 (change p 112 (some 138)) = d15 p
  exact sub518 p
theorem sub520 (p : Pattern) : d17 (change p 112 (some 138)) = d17 p := by
  change (if p 160 then d2 (change p 112 (some 138)) else d3 (change p 112 (some 138))) = d17 p
  rw [sub504, sub505]
  rfl
theorem sub521 (p : Pattern) : d18 (change p 112 (some 138)) = d18 p := by
  change (if p 159 then d17 (change p 112 (some 138)) else d4 (change p 112 (some 138))) = d18 p
  rw [sub520, sub506]
  rfl
theorem sub522 (p : Pattern) : d19 (change p 112 (some 138)) = d19 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d17 (change p 112 (some 138))) = d19 p
  rw [sub504, sub520]
  rfl
theorem sub523 (p : Pattern) : d20 (change p 112 (some 138)) = d20 p := by
  change (if p 158 then d19 (change p 112 (some 138)) else d18 (change p 112 (some 138))) = d20 p
  rw [sub522, sub521]
  rfl
theorem sub524 (p : Pattern) : d21 (change p 112 (some 138)) = d21 p := by
  change (if p 160 then d2 (change p 112 (some 138)) else d9 (change p 112 (some 138))) = d21 p
  rw [sub504, sub512]
  rfl
theorem sub525 (p : Pattern) : d22 (change p 112 (some 138)) = d22 p := by
  change (if p 159 then d21 (change p 112 (some 138)) else d10 (change p 112 (some 138))) = d22 p
  rw [sub524, sub513]
  rfl
theorem sub526 (p : Pattern) : d23 (change p 112 (some 138)) = d23 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d21 (change p 112 (some 138))) = d23 p
  rw [sub504, sub524]
  rfl
theorem sub527 (p : Pattern) : d24 (change p 112 (some 138)) = d24 p := by
  change (if p 158 then d23 (change p 112 (some 138)) else d22 (change p 112 (some 138))) = d24 p
  rw [sub526, sub525]
  rfl
theorem sub528 (p : Pattern) : d25 (change p 112 (some 138)) = d25 p := by
  change (if p 139 then d24 (change p 112 (some 138)) else d20 (change p 112 (some 138))) = d25 p
  rw [sub527, sub523]
  rfl
theorem sub529 (p : Pattern) : d26 (change p 112 (some 138)) = d25 p := by
  change d25 (change p 112 (some 138)) = d25 p
  exact sub528 p
theorem sub530 (p : Pattern) : d27 (change p 112 (some 138)) = d46 p := by
  change (if p 134 then d26 (change p 112 (some 138)) else d16 (change p 112 (some 138))) = d46 p
  rw [sub529, sub519]
  rfl
theorem sub531 (p : Pattern) : d28 (change p 112 (some 138)) = d47 p := by
  change (if p 133 then d27 (change p 112 (some 138)) else d16 (change p 112 (some 138))) = d47 p
  rw [sub530, sub519]
  rfl
theorem sub532 (p : Pattern) : d29 (change p 112 (some 138)) = d29 p := by
  change (if p 161 then d1 (change p 112 (some 138)) else d0 (change p 112 (some 138))) = d29 p
  rw [sub511, sub503]
  rfl
theorem sub533 (p : Pattern) : d30 (change p 112 (some 138)) = d30 p := by
  change (if p 160 then d2 (change p 112 (some 138)) else d29 (change p 112 (some 138))) = d30 p
  rw [sub504, sub532]
  rfl
theorem sub534 (p : Pattern) : d31 (change p 112 (some 138)) = d31 p := by
  change (if p 159 then d30 (change p 112 (some 138)) else d4 (change p 112 (some 138))) = d31 p
  rw [sub533, sub506]
  rfl
theorem sub535 (p : Pattern) : d32 (change p 112 (some 138)) = d32 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d30 (change p 112 (some 138))) = d32 p
  rw [sub504, sub533]
  rfl
theorem sub536 (p : Pattern) : d33 (change p 112 (some 138)) = d33 p := by
  change (if p 158 then d32 (change p 112 (some 138)) else d31 (change p 112 (some 138))) = d33 p
  rw [sub535, sub534]
  rfl
theorem sub537 (p : Pattern) : d34 (change p 112 (some 138)) = d34 p := by
  change (if p 139 then d24 (change p 112 (some 138)) else d33 (change p 112 (some 138))) = d34 p
  rw [sub527, sub536]
  rfl
theorem sub538 (p : Pattern) : d35 (change p 112 (some 138)) = d34 p := by
  change d34 (change p 112 (some 138)) = d34 p
  exact sub537 p
theorem sub539 (p : Pattern) : d36 (change p 112 (some 138)) = d48 p := by
  change (if p 134 then d35 (change p 112 (some 138)) else d16 (change p 112 (some 138))) = d48 p
  rw [sub538, sub519]
  rfl
theorem sub540 (p : Pattern) : d37 (change p 112 (some 138)) = d37 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d5 (change p 112 (some 138))) = d37 p
  rw [sub504, sub507]
  rfl
theorem sub541 (p : Pattern) : d38 (change p 112 (some 138)) = d38 p := by
  change (if p 158 then d37 (change p 112 (some 138)) else d6 (change p 112 (some 138))) = d38 p
  rw [sub540, sub508]
  rfl
theorem sub542 (p : Pattern) : d39 (change p 112 (some 138)) = d39 p := by
  change (if p 159 then d2 (change p 112 (some 138)) else d11 (change p 112 (some 138))) = d39 p
  rw [sub504, sub514]
  rfl
theorem sub543 (p : Pattern) : d40 (change p 112 (some 138)) = d40 p := by
  change (if p 158 then d39 (change p 112 (some 138)) else d12 (change p 112 (some 138))) = d40 p
  rw [sub542, sub515]
  rfl
theorem sub544 (p : Pattern) : d41 (change p 112 (some 138)) = d41 p := by
  change (if p 139 then d40 (change p 112 (some 138)) else d38 (change p 112 (some 138))) = d41 p
  rw [sub543, sub541]
  rfl
theorem sub545 (p : Pattern) : d42 (change p 112 (some 138)) = d41 p := by
  change d41 (change p 112 (some 138)) = d41 p
  exact sub544 p
theorem sub546 (p : Pattern) : d43 (change p 112 (some 138)) = d49 p := by
  change (if p 134 then d26 (change p 112 (some 138)) else d42 (change p 112 (some 138))) = d49 p
  rw [sub529, sub545]
  rfl
theorem sub547 (p : Pattern) : d44 (change p 112 (some 138)) = d50 p := by
  change (if p 133 then d43 (change p 112 (some 138)) else d36 (change p 112 (some 138))) = d50 p
  rw [sub546, sub539]
  rfl
theorem sub548 (p : Pattern) : d45 (change p 112 (some 138)) = d51 p := by
  change (if p 132 then d44 (change p 112 (some 138)) else d28 (change p 112 (some 138))) = d51 p
  rw [sub547, sub531]
  rfl
theorem sub549 (p : Pattern) : d184 (change p 112 (some 138)) = d51 p := by
  change d45 (change p 112 (some 138)) = d51 p
  exact sub548 p
theorem sub550 (p : Pattern) : d68 (change p 112 (some 138)) = d68 p := by
  change (if p 139 then d2 (change p 112 (some 138)) else d40 (change p 112 (some 138))) = d68 p
  rw [sub504, sub543]
  rfl
theorem sub551 (p : Pattern) : d69 (change p 112 (some 138)) = d68 p := by
  change d68 (change p 112 (some 138)) = d68 p
  exact sub550 p
theorem sub552 (p : Pattern) : d70 (change p 112 (some 138)) = d70 p := by
  change (if p 139 then d2 (change p 112 (some 138)) else d24 (change p 112 (some 138))) = d70 p
  rw [sub504, sub527]
  rfl
theorem sub553 (p : Pattern) : d71 (change p 112 (some 138)) = d70 p := by
  change d70 (change p 112 (some 138)) = d70 p
  exact sub552 p
theorem sub554 (p : Pattern) : d72 (change p 112 (some 138)) = d75 p := by
  change (if p 134 then d71 (change p 112 (some 138)) else d69 (change p 112 (some 138))) = d75 p
  rw [sub553, sub551]
  rfl
theorem sub555 (p : Pattern) : d73 (change p 112 (some 138)) = d79 p := by
  change (if p 133 then d72 (change p 112 (some 138)) else d27 (change p 112 (some 138))) = d79 p
  rw [sub554, sub530]
  rfl
theorem sub556 (p : Pattern) : d74 (change p 112 (some 138)) = d80 p := by
  change (if p 132 then d73 (change p 112 (some 138)) else d28 (change p 112 (some 138))) = d80 p
  rw [sub555, sub531]
  rfl
theorem sub557 (p : Pattern) : d75 (change p 112 (some 138)) = d75 p := by
  change (if p 134 then d70 (change p 112 (some 138)) else d68 (change p 112 (some 138))) = d75 p
  rw [sub552, sub550]
  rfl
theorem sub558 (p : Pattern) : d76 (change p 112 (some 138)) = d79 p := by
  change (if p 133 then d75 (change p 112 (some 138)) else d27 (change p 112 (some 138))) = d79 p
  rw [sub557, sub530]
  rfl
theorem sub559 (p : Pattern) : d77 (change p 112 (some 138)) = d80 p := by
  change (if p 132 then d76 (change p 112 (some 138)) else d28 (change p 112 (some 138))) = d80 p
  rw [sub558, sub531]
  rfl
theorem sub560 (p : Pattern) : d78 (change p 112 (some 138)) = d80 p := by
  change (if p 113 then d77 (change p 112 (some 138)) else d74 (change p 112 (some 138))) = d80 p
  rw [sub559, sub556]
  simp only [ite_self]
theorem sub561 (p : Pattern) : d185 (change p 112 (some 138)) = d80 p := by
  change d78 (change p 112 (some 138)) = d80 p
  exact sub560 p
theorem sub562 (p : Pattern) : d186 (change p 112 (some 138)) = d860 p := by
  change (if p 106 then d185 (change p 112 (some 138)) else d184 (change p 112 (some 138))) = d860 p
  rw [sub561, sub549]
  rfl
theorem sub563 (p : Pattern) : d97 (change p 112 (some 138)) = d97 p := by
  change (if p 139 then d2 (change p 112 (some 138)) else d14 (change p 112 (some 138))) = d97 p
  rw [sub504, sub517]
  rfl
theorem sub564 (p : Pattern) : d187 (change p 112 (some 138)) = d97 p := by
  change d97 (change p 112 (some 138)) = d97 p
  exact sub563 p
theorem sub565 (p : Pattern) : d188 (change p 112 (some 138)) = d70 p := by
  change d70 (change p 112 (some 138)) = d70 p
  exact sub552 p
theorem sub566 (p : Pattern) : d189 (change p 112 (some 138)) = d109 p := by
  change (if p 134 then d188 (change p 112 (some 138)) else d187 (change p 112 (some 138))) = d109 p
  rw [sub565, sub564]
  rfl
theorem sub567 (p : Pattern) : d190 (change p 112 (some 138)) = d110 p := by
  change (if p 133 then d189 (change p 112 (some 138)) else d187 (change p 112 (some 138))) = d110 p
  rw [sub566, sub564]
  rfl
theorem sub568 (p : Pattern) : d191 (change p 112 (some 138)) = d70 p := by
  change d70 (change p 112 (some 138)) = d70 p
  exact sub552 p
theorem sub569 (p : Pattern) : d192 (change p 112 (some 138)) = d109 p := by
  change (if p 134 then d191 (change p 112 (some 138)) else d187 (change p 112 (some 138))) = d109 p
  rw [sub568, sub564]
  rfl
theorem sub570 (p : Pattern) : d193 (change p 112 (some 138)) = d68 p := by
  change d68 (change p 112 (some 138)) = d68 p
  exact sub550 p
theorem sub571 (p : Pattern) : d194 (change p 112 (some 138)) = d75 p := by
  change (if p 134 then d188 (change p 112 (some 138)) else d193 (change p 112 (some 138))) = d75 p
  rw [sub565, sub570]
  rfl
theorem sub572 (p : Pattern) : d195 (change p 112 (some 138)) = d125 p := by
  change (if p 133 then d194 (change p 112 (some 138)) else d192 (change p 112 (some 138))) = d125 p
  rw [sub571, sub569]
  rfl
theorem sub573 (p : Pattern) : d196 (change p 112 (some 138)) = d126 p := by
  change (if p 132 then d195 (change p 112 (some 138)) else d190 (change p 112 (some 138))) = d126 p
  rw [sub572, sub567]
  rfl
theorem sub574 (p : Pattern) : d197 (change p 112 (some 138)) = d861 p := by
  change (if p 113 then d196 (change p 112 (some 138)) else d45 (change p 112 (some 138))) = d861 p
  rw [sub573, sub548]
  rfl
theorem sub575 (p : Pattern) : d198 (change p 112 (some 138)) = d861 p := by
  change d197 (change p 112 (some 138)) = d861 p
  exact sub574 p
theorem sub576 (p : Pattern) : d199 (change p 112 (some 138)) = d2 p := by
  change d2 (change p 112 (some 138)) = d2 p
  exact sub504 p
theorem sub577 (p : Pattern) : d200 (change p 112 (some 138)) = d2 p := by
  change d2 (change p 112 (some 138)) = d2 p
  exact sub504 p
theorem sub578 (p : Pattern) : d201 (change p 112 (some 138)) = d2 p := by
  change (if p 134 then d200 (change p 112 (some 138)) else d199 (change p 112 (some 138))) = d2 p
  rw [sub577, sub576]
  simp only [ite_self]
theorem sub579 (p : Pattern) : d202 (change p 112 (some 138)) = d111 p := by
  change (if p 133 then d201 (change p 112 (some 138)) else d189 (change p 112 (some 138))) = d111 p
  rw [sub578, sub566]
  rfl
theorem sub580 (p : Pattern) : d203 (change p 112 (some 138)) = d112 p := by
  change (if p 132 then d202 (change p 112 (some 138)) else d190 (change p 112 (some 138))) = d112 p
  rw [sub579, sub567]
  rfl
theorem sub581 (p : Pattern) : d204 (change p 112 (some 138)) = d862 p := by
  change (if p 113 then d203 (change p 112 (some 138)) else d77 (change p 112 (some 138))) = d862 p
  rw [sub580, sub559]
  rfl
theorem sub582 (p : Pattern) : d205 (change p 112 (some 138)) = d862 p := by
  change d204 (change p 112 (some 138)) = d862 p
  exact sub581 p
theorem sub583 (p : Pattern) : d206 (change p 112 (some 138)) = d863 p := by
  change (if p 106 then d205 (change p 112 (some 138)) else d198 (change p 112 (some 138))) = d863 p
  rw [sub582, sub575]
  rfl
theorem sub584 (p : Pattern) : d207 (change p 112 (some 138)) = d864 p := by
  change (if p 86 then d206 (change p 112 (some 138)) else d186 (change p 112 (some 138))) = d864 p
  rw [sub583, sub562]
  rfl
theorem sub585 (p : Pattern) : d208 (change p 112 (some 138)) = d51 p := by
  change d45 (change p 112 (some 138)) = d51 p
  exact sub548 p
theorem sub586 (p : Pattern) : d209 (change p 112 (some 138)) = d80 p := by
  change d77 (change p 112 (some 138)) = d80 p
  exact sub559 p
theorem sub587 (p : Pattern) : d210 (change p 112 (some 138)) = d860 p := by
  change (if p 106 then d209 (change p 112 (some 138)) else d208 (change p 112 (some 138))) = d860 p
  rw [sub586, sub585]
  rfl
theorem sub588 (p : Pattern) : d211 (change p 112 (some 138)) = d70 p := by
  change d70 (change p 112 (some 138)) = d70 p
  exact sub552 p
theorem sub589 (p : Pattern) : d212 (change p 112 (some 138)) = d109 p := by
  change (if p 134 then d211 (change p 112 (some 138)) else d187 (change p 112 (some 138))) = d109 p
  rw [sub588, sub564]
  rfl
theorem sub590 (p : Pattern) : d213 (change p 112 (some 138)) = d125 p := by
  change (if p 133 then d194 (change p 112 (some 138)) else d212 (change p 112 (some 138))) = d125 p
  rw [sub571, sub589]
  rfl
theorem sub591 (p : Pattern) : d214 (change p 112 (some 138)) = d126 p := by
  change (if p 132 then d213 (change p 112 (some 138)) else d190 (change p 112 (some 138))) = d126 p
  rw [sub590, sub567]
  rfl
theorem sub592 (p : Pattern) : d215 (change p 112 (some 138)) = d861 p := by
  change (if p 113 then d214 (change p 112 (some 138)) else d45 (change p 112 (some 138))) = d861 p
  rw [sub591, sub548]
  rfl
theorem sub593 (p : Pattern) : d216 (change p 112 (some 138)) = d861 p := by
  change d215 (change p 112 (some 138)) = d861 p
  exact sub592 p
theorem sub594 (p : Pattern) : d217 (change p 112 (some 138)) = d97 p := by
  change d97 (change p 112 (some 138)) = d97 p
  exact sub563 p
theorem sub595 (p : Pattern) : d218 (change p 112 (some 138)) = d70 p := by
  change d70 (change p 112 (some 138)) = d70 p
  exact sub552 p
theorem sub596 (p : Pattern) : d219 (change p 112 (some 138)) = d109 p := by
  change (if p 134 then d218 (change p 112 (some 138)) else d217 (change p 112 (some 138))) = d109 p
  rw [sub595, sub594]
  rfl
theorem sub597 (p : Pattern) : d220 (change p 112 (some 138)) = d110 p := by
  change (if p 133 then d219 (change p 112 (some 138)) else d217 (change p 112 (some 138))) = d110 p
  rw [sub596, sub594]
  rfl
theorem sub598 (p : Pattern) : d221 (change p 112 (some 138)) = d111 p := by
  change (if p 133 then d201 (change p 112 (some 138)) else d219 (change p 112 (some 138))) = d111 p
  rw [sub578, sub596]
  rfl
theorem sub599 (p : Pattern) : d222 (change p 112 (some 138)) = d112 p := by
  change (if p 132 then d221 (change p 112 (some 138)) else d220 (change p 112 (some 138))) = d112 p
  rw [sub598, sub597]
  rfl
end NetHack.Sokoban32Refined
