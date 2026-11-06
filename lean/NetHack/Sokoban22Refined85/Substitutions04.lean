/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub480 (p : Pattern) : d72 (change p 10000 (some 48)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d40 (change p 10000 (some 48))) = d72 p
  rw [sub414, sub447]
  rfl
theorem sub481 (p : Pattern) : d73 (change p 10000 (some 48)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d72 (change p 10000 (some 48))) = d73 p
  rw [sub414, sub480]
  rfl
theorem sub482 (p : Pattern) : d74 (change p 10000 (some 48)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 48)) else d71 (change p 10000 (some 48))) = d74 p
  rw [sub481, sub479]
  rfl
theorem sub483 (p : Pattern) : d75 (change p 10000 (some 48)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 48)) else d69 (change p 10000 (some 48))) = d75 p
  rw [sub482, sub477]
  rfl
theorem sub484 (p : Pattern) : d76 (change p 10000 (some 48)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 48)) else d65 (change p 10000 (some 48))) = d76 p
  rw [sub483, sub473]
  rfl
theorem sub485 (p : Pattern) : d77 (change p 10000 (some 48)) = d77 p := by
  change (if p 141 then d76 (change p 10000 (some 48)) else d52 (change p 10000 (some 48))) = d77 p
  rw [sub484, sub459]
  rfl
theorem sub486 (p : Pattern) : d78 (change p 10000 (some 48)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 48)) else d35 (change p 10000 (some 48))) = d78 p
  rw [sub442, sub441]
  rfl
theorem sub487 (p : Pattern) : d79 (change p 10000 (some 48)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 48)) else d53 (change p 10000 (some 48))) = d79 p
  rw [sub486, sub460]
  rfl
theorem sub488 (p : Pattern) : d80 (change p 10000 (some 48)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 48)) else d79 (change p 10000 (some 48))) = d80 p
  rw [sub471, sub487]
  rfl
theorem sub489 (p : Pattern) : d81 (change p 10000 (some 48)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d80 (change p 10000 (some 48))) = d81 p
  rw [sub414, sub488]
  rfl
theorem sub490 (p : Pattern) : d82 (change p 10000 (some 48)) = d82 p := by
  change (if p 160 then d81 (change p 10000 (some 48)) else d29 (change p 10000 (some 48))) = d82 p
  rw [sub489, sub433]
  rfl
theorem sub491 (p : Pattern) : d83 (change p 10000 (some 48)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d78 (change p 10000 (some 48))) = d83 p
  rw [sub414, sub486]
  rfl
theorem sub492 (p : Pattern) : d84 (change p 10000 (some 48)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d83 (change p 10000 (some 48))) = d84 p
  rw [sub414, sub491]
  rfl
theorem sub493 (p : Pattern) : d85 (change p 10000 (some 48)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d84 (change p 10000 (some 48))) = d85 p
  rw [sub414, sub492]
  rfl
theorem sub494 (p : Pattern) : d86 (change p 10000 (some 48)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 48)) else d65 (change p 10000 (some 48))) = d86 p
  rw [sub493, sub473]
  rfl
theorem sub495 (p : Pattern) : d87 (change p 10000 (some 48)) = d87 p := by
  change (if p 141 then d86 (change p 10000 (some 48)) else d82 (change p 10000 (some 48))) = d87 p
  rw [sub494, sub490]
  rfl
theorem sub496 (p : Pattern) : d88 (change p 10000 (some 48)) = d88 p := by
  change (if p 138 then d87 (change p 10000 (some 48)) else d77 (change p 10000 (some 48))) = d88 p
  rw [sub495, sub485]
  rfl
theorem sub497 (p : Pattern) : d89 (change p 10000 (some 48)) = d89 p := by
  change (if p 163 then d62 (change p 10000 (some 48)) else d26 (change p 10000 (some 48))) = d89 p
  rw [sub470, sub430]
  rfl
theorem sub498 (p : Pattern) : d90 (change p 10000 (some 48)) = d90 p := by
  change (if p 162 then d63 (change p 10000 (some 48)) else d89 (change p 10000 (some 48))) = d90 p
  rw [sub471, sub497]
  rfl
theorem sub499 (p : Pattern) : d91 (change p 10000 (some 48)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d63 (change p 10000 (some 48))) = d91 p
  rw [sub414, sub471]
  rfl
theorem sub500 (p : Pattern) : d92 (change p 10000 (some 48)) = d92 p := by
  change (if p 161 then d91 (change p 10000 (some 48)) else d90 (change p 10000 (some 48))) = d92 p
  rw [sub499, sub498]
  rfl
theorem sub501 (p : Pattern) : d93 (change p 10000 (some 48)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d91 (change p 10000 (some 48))) = d93 p
  rw [sub414, sub499]
  rfl
theorem sub502 (p : Pattern) : d94 (change p 10000 (some 48)) = d94 p := by
  change (if p 160 then d93 (change p 10000 (some 48)) else d92 (change p 10000 (some 48))) = d94 p
  rw [sub501, sub500]
  rfl
theorem sub503 (p : Pattern) : d95 (change p 10000 (some 48)) = d95 p := by
  change (if p 160 then d12 (change p 10000 (some 48)) else d93 (change p 10000 (some 48))) = d95 p
  rw [sub414, sub501]
  rfl
theorem sub504 (p : Pattern) : d96 (change p 10000 (some 48)) = d96 p := by
  change (if p 141 then d95 (change p 10000 (some 48)) else d94 (change p 10000 (some 48))) = d96 p
  rw [sub503, sub502]
  rfl
theorem sub505 (p : Pattern) : d97 (change p 10000 (some 48)) = d97 p := by
  change (if p 138 then d96 (change p 10000 (some 48)) else d87 (change p 10000 (some 48))) = d97 p
  rw [sub504, sub495]
  rfl
theorem sub506 (p : Pattern) : d98 (change p 10000 (some 48)) = d98 p := by
  change (if p 116 then d97 (change p 10000 (some 48)) else d88 (change p 10000 (some 48))) = d98 p
  rw [sub505, sub496]
  rfl
theorem sub507 (p : Pattern) : d99 (change p 10000 (some 48)) = d99 p := by
  change (if p 138 then d12 (change p 10000 (some 48)) else d87 (change p 10000 (some 48))) = d99 p
  rw [sub414, sub495]
  rfl
theorem sub508 (p : Pattern) : d100 (change p 10000 (some 48)) = d100 p := by
  change (if p 116 then d99 (change p 10000 (some 48)) else d88 (change p 10000 (some 48))) = d100 p
  rw [sub507, sub496]
  rfl
theorem sub509 (p : Pattern) : d101 (change p 10000 (some 48)) = d101 p := by
  change (if p 115 then d100 (change p 10000 (some 48)) else d98 (change p 10000 (some 48))) = d101 p
  rw [sub508, sub506]
  rfl
theorem sub510 (p : Pattern) : d170 (change p 10000 (some 48)) = d170 p := by
  change (if p 182 then d36 (change p 10000 (some 48)) else d31 (change p 10000 (some 48))) = d170 p
  rw [sub442, sub436]
  rfl
theorem sub511 (p : Pattern) : d171 (change p 10000 (some 48)) = d171 p := by
  change (if p 163 then d170 (change p 10000 (some 48)) else d53 (change p 10000 (some 48))) = d171 p
  rw [sub510, sub460]
  rfl
theorem sub512 (p : Pattern) : d172 (change p 10000 (some 48)) = d172 p := by
  change (if p 182 then d41 (change p 10000 (some 48)) else d31 (change p 10000 (some 48))) = d172 p
  rw [sub448, sub436]
  rfl
theorem sub513 (p : Pattern) : d173 (change p 10000 (some 48)) = d173 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d35 (change p 10000 (some 48))) = d173 p
  rw [sub414, sub441]
  rfl
theorem sub514 (p : Pattern) : d174 (change p 10000 (some 48)) = d174 p := by
  change (if p 163 then d173 (change p 10000 (some 48)) else d172 (change p 10000 (some 48))) = d174 p
  rw [sub513, sub512]
  rfl
theorem sub515 (p : Pattern) : d175 (change p 10000 (some 48)) = d175 p := by
  change (if p 162 then d174 (change p 10000 (some 48)) else d171 (change p 10000 (some 48))) = d175 p
  rw [sub514, sub511]
  rfl
theorem sub516 (p : Pattern) : d176 (change p 10000 (some 48)) = d176 p := by
  change (if p 163 then d173 (change p 10000 (some 48)) else d66 (change p 10000 (some 48))) = d176 p
  rw [sub513, sub474]
  rfl
theorem sub517 (p : Pattern) : d177 (change p 10000 (some 48)) = d177 p := by
  change (if p 162 then d73 (change p 10000 (some 48)) else d176 (change p 10000 (some 48))) = d177 p
  rw [sub481, sub516]
  rfl
theorem sub518 (p : Pattern) : d178 (change p 10000 (some 48)) = d178 p := by
  change (if p 161 then d177 (change p 10000 (some 48)) else d175 (change p 10000 (some 48))) = d178 p
  rw [sub517, sub515]
  rfl
theorem sub519 (p : Pattern) : d179 (change p 10000 (some 48)) = d179 p := by
  change (if p 160 then d178 (change p 10000 (some 48)) else d29 (change p 10000 (some 48))) = d179 p
  rw [sub518, sub433]
  rfl
theorem sub520 (p : Pattern) : d180 (change p 10000 (some 48)) = d180 p := by
  change (if p 163 then d43 (change p 10000 (some 48)) else d170 (change p 10000 (some 48))) = d180 p
  rw [sub450, sub510]
  rfl
theorem sub521 (p : Pattern) : d181 (change p 10000 (some 48)) = d181 p := by
  change (if p 163 then d72 (change p 10000 (some 48)) else d173 (change p 10000 (some 48))) = d181 p
  rw [sub480, sub513]
  rfl
theorem sub522 (p : Pattern) : d182 (change p 10000 (some 48)) = d182 p := by
  change (if p 162 then d181 (change p 10000 (some 48)) else d180 (change p 10000 (some 48))) = d182 p
  rw [sub521, sub520]
  rfl
theorem sub523 (p : Pattern) : d183 (change p 10000 (some 48)) = d183 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d173 (change p 10000 (some 48))) = d183 p
  rw [sub414, sub513]
  rfl
theorem sub524 (p : Pattern) : d184 (change p 10000 (some 48)) = d184 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d183 (change p 10000 (some 48))) = d184 p
  rw [sub414, sub523]
  rfl
theorem sub525 (p : Pattern) : d185 (change p 10000 (some 48)) = d185 p := by
  change (if p 161 then d184 (change p 10000 (some 48)) else d182 (change p 10000 (some 48))) = d185 p
  rw [sub524, sub522]
  rfl
theorem sub526 (p : Pattern) : d186 (change p 10000 (some 48)) = d186 p := by
  change (if p 160 then d185 (change p 10000 (some 48)) else d65 (change p 10000 (some 48))) = d186 p
  rw [sub525, sub473]
  rfl
theorem sub527 (p : Pattern) : d187 (change p 10000 (some 48)) = d187 p := by
  change (if p 141 then d186 (change p 10000 (some 48)) else d179 (change p 10000 (some 48))) = d187 p
  rw [sub526, sub519]
  rfl
theorem sub528 (p : Pattern) : d188 (change p 10000 (some 48)) = d188 p := by
  change (if p 162 then d79 (change p 10000 (some 48)) else d16 (change p 10000 (some 48))) = d188 p
  rw [sub487, sub418]
  rfl
theorem sub529 (p : Pattern) : d189 (change p 10000 (some 48)) = d189 p := by
  change (if p 161 then d80 (change p 10000 (some 48)) else d188 (change p 10000 (some 48))) = d189 p
  rw [sub488, sub528]
  rfl
theorem sub530 (p : Pattern) : d8 (change p 10000 (some 48)) = d8 p := by
  rfl
theorem sub531 (p : Pattern) : d190 (change p 10000 (some 48)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d8 (change p 10000 (some 48))) = d190 p
  rw [sub414, sub530]
  rfl
theorem sub532 (p : Pattern) : d191 (change p 10000 (some 48)) = d191 p := by
  change (if p 246 then d190 (change p 10000 (some 48)) else d8 (change p 10000 (some 48))) = d191 p
  rw [sub531, sub530]
  rfl
theorem sub533 (p : Pattern) : d192 (change p 10000 (some 48)) = d192 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d191 (change p 10000 (some 48))) = d192 p
  rw [sub414, sub532]
  rfl
theorem sub534 (p : Pattern) : d193 (change p 10000 (some 48)) = d193 p := by
  change (if p 182 then d192 (change p 10000 (some 48)) else d191 (change p 10000 (some 48))) = d193 p
  rw [sub533, sub532]
  rfl
theorem sub535 (p : Pattern) : d194 (change p 10000 (some 48)) = d194 p := by
  change (if p 163 then d193 (change p 10000 (some 48)) else d20 (change p 10000 (some 48))) = d194 p
  rw [sub534, sub423]
  rfl
theorem sub536 (p : Pattern) : d195 (change p 10000 (some 48)) = d195 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d194 (change p 10000 (some 48))) = d195 p
  rw [sub414, sub535]
  rfl
theorem sub537 (p : Pattern) : d196 (change p 10000 (some 48)) = d196 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d195 (change p 10000 (some 48))) = d196 p
  rw [sub414, sub536]
  rfl
theorem sub538 (p : Pattern) : d197 (change p 10000 (some 48)) = d197 p := by
  change (if p 160 then d196 (change p 10000 (some 48)) else d189 (change p 10000 (some 48))) = d197 p
  rw [sub537, sub529]
  rfl
theorem sub539 (p : Pattern) : d198 (change p 10000 (some 48)) = d198 p := by
  change (if p 163 then d62 (change p 10000 (some 48)) else d20 (change p 10000 (some 48))) = d198 p
  rw [sub470, sub423]
  rfl
theorem sub540 (p : Pattern) : d199 (change p 10000 (some 48)) = d199 p := by
  change (if p 162 then d198 (change p 10000 (some 48)) else d53 (change p 10000 (some 48))) = d199 p
  rw [sub539, sub460]
  rfl
theorem sub541 (p : Pattern) : d200 (change p 10000 (some 48)) = d200 p := by
  change (if p 161 then d84 (change p 10000 (some 48)) else d199 (change p 10000 (some 48))) = d200 p
  rw [sub492, sub540]
  rfl
theorem sub542 (p : Pattern) : d201 (change p 10000 (some 48)) = d201 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d193 (change p 10000 (some 48))) = d201 p
  rw [sub414, sub534]
  rfl
theorem sub543 (p : Pattern) : d202 (change p 10000 (some 48)) = d202 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d201 (change p 10000 (some 48))) = d202 p
  rw [sub414, sub542]
  rfl
theorem sub544 (p : Pattern) : d203 (change p 10000 (some 48)) = d203 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d202 (change p 10000 (some 48))) = d203 p
  rw [sub414, sub543]
  rfl
theorem sub545 (p : Pattern) : d204 (change p 10000 (some 48)) = d204 p := by
  change (if p 160 then d203 (change p 10000 (some 48)) else d200 (change p 10000 (some 48))) = d204 p
  rw [sub544, sub541]
  rfl
theorem sub546 (p : Pattern) : d205 (change p 10000 (some 48)) = d205 p := by
  change (if p 141 then d204 (change p 10000 (some 48)) else d197 (change p 10000 (some 48))) = d205 p
  rw [sub545, sub538]
  rfl
theorem sub547 (p : Pattern) : d206 (change p 10000 (some 48)) = d206 p := by
  change (if p 138 then d205 (change p 10000 (some 48)) else d187 (change p 10000 (some 48))) = d206 p
  rw [sub546, sub527]
  rfl
theorem sub548 (p : Pattern) : d207 (change p 10000 (some 48)) = d207 p := by
  change (if p 138 then d12 (change p 10000 (some 48)) else d205 (change p 10000 (some 48))) = d207 p
  rw [sub414, sub546]
  rfl
theorem sub549 (p : Pattern) : d208 (change p 10000 (some 48)) = d208 p := by
  change (if p 116 then d207 (change p 10000 (some 48)) else d206 (change p 10000 (some 48))) = d208 p
  rw [sub548, sub547]
  rfl
theorem sub550 (p : Pattern) : d209 (change p 10000 (some 48)) = d209 p := by
  change (if p 115 then d208 (change p 10000 (some 48)) else d98 (change p 10000 (some 48))) = d209 p
  rw [sub549, sub506]
  rfl
theorem sub551 (p : Pattern) : d210 (change p 10000 (some 48)) = d210 p := by
  change (if p 71 then d209 (change p 10000 (some 48)) else d101 (change p 10000 (some 48))) = d210 p
  rw [sub550, sub509]
  rfl
theorem sub552 (p : Pattern) : d1 (change p 10000 (some 48)) = d1 p := by
  rfl
theorem sub553 (p : Pattern) : d102 (change p 10000 (some 48)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d1 (change p 10000 (some 48))) = d102 p
  rw [sub414, sub552]
  rfl
theorem sub554 (p : Pattern) : d103 (change p 10000 (some 48)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 48)) else d1 (change p 10000 (some 48))) = d103 p
  rw [sub553, sub552]
  rfl
theorem sub555 (p : Pattern) : d104 (change p 10000 (some 48)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d103 (change p 10000 (some 48))) = d104 p
  rw [sub414, sub554]
  rfl
theorem sub556 (p : Pattern) : d105 (change p 10000 (some 48)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 48)) else d103 (change p 10000 (some 48))) = d105 p
  rw [sub555, sub554]
  rfl
theorem sub557 (p : Pattern) : d5 (change p 10000 (some 48)) = d5 p := by
  rfl
theorem sub558 (p : Pattern) : d106 (change p 10000 (some 48)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d5 (change p 10000 (some 48))) = d106 p
  rw [sub414, sub557]
  rfl
theorem sub559 (p : Pattern) : d107 (change p 10000 (some 48)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 48)) else d5 (change p 10000 (some 48))) = d107 p
  rw [sub558, sub557]
  rfl
theorem sub560 (p : Pattern) : d108 (change p 10000 (some 48)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d107 (change p 10000 (some 48))) = d108 p
  rw [sub414, sub559]
  rfl
theorem sub561 (p : Pattern) : d109 (change p 10000 (some 48)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 48)) else d107 (change p 10000 (some 48))) = d109 p
  rw [sub560, sub559]
  rfl
theorem sub562 (p : Pattern) : d110 (change p 10000 (some 48)) = d110 p := by
  change (if p 163 then d109 (change p 10000 (some 48)) else d105 (change p 10000 (some 48))) = d110 p
  rw [sub561, sub556]
  rfl
theorem sub563 (p : Pattern) : d111 (change p 10000 (some 48)) = d111 p := by
  change (if p 162 then d110 (change p 10000 (some 48)) else d105 (change p 10000 (some 48))) = d111 p
  rw [sub562, sub556]
  rfl
theorem sub564 (p : Pattern) : d112 (change p 10000 (some 48)) = d112 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d60 (change p 10000 (some 48))) = d112 p
  rw [sub414, sub468]
  rfl
theorem sub565 (p : Pattern) : d113 (change p 10000 (some 48)) = d113 p := by
  change (if p 162 then d112 (change p 10000 (some 48)) else d110 (change p 10000 (some 48))) = d113 p
  rw [sub564, sub562]
  rfl
theorem sub566 (p : Pattern) : d114 (change p 10000 (some 48)) = d114 p := by
  change (if p 161 then d113 (change p 10000 (some 48)) else d111 (change p 10000 (some 48))) = d114 p
  rw [sub565, sub563]
  rfl
theorem sub567 (p : Pattern) : d3 (change p 10000 (some 48)) = d3 p := by
  rfl
theorem sub568 (p : Pattern) : d115 (change p 10000 (some 48)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d3 (change p 10000 (some 48))) = d115 p
  rw [sub414, sub567]
  rfl
theorem sub569 (p : Pattern) : d116 (change p 10000 (some 48)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 48)) else d3 (change p 10000 (some 48))) = d116 p
  rw [sub568, sub567]
  rfl
theorem sub570 (p : Pattern) : d117 (change p 10000 (some 48)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d116 (change p 10000 (some 48))) = d117 p
  rw [sub414, sub569]
  rfl
theorem sub571 (p : Pattern) : d118 (change p 10000 (some 48)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 48)) else d103 (change p 10000 (some 48))) = d118 p
  rw [sub570, sub554]
  rfl
theorem sub572 (p : Pattern) : d7 (change p 10000 (some 48)) = d7 p := by
  rfl
theorem sub573 (p : Pattern) : d119 (change p 10000 (some 48)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 48)) else d7 (change p 10000 (some 48))) = d119 p
  rw [sub414, sub572]
  rfl
theorem sub574 (p : Pattern) : d120 (change p 10000 (some 48)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 48)) else d7 (change p 10000 (some 48))) = d120 p
  rw [sub573, sub572]
  rfl
theorem sub575 (p : Pattern) : d121 (change p 10000 (some 48)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 48)) else d120 (change p 10000 (some 48))) = d121 p
  rw [sub414, sub574]
  rfl
theorem sub576 (p : Pattern) : d122 (change p 10000 (some 48)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 48)) else d103 (change p 10000 (some 48))) = d122 p
  rw [sub575, sub554]
  rfl
theorem sub577 (p : Pattern) : d123 (change p 10000 (some 48)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 48)) else d118 (change p 10000 (some 48))) = d123 p
  rw [sub576, sub571]
  rfl
theorem sub578 (p : Pattern) : d124 (change p 10000 (some 48)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d103 (change p 10000 (some 48))) = d124 p
  rw [sub414, sub554]
  rfl
theorem sub579 (p : Pattern) : d125 (change p 10000 (some 48)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d107 (change p 10000 (some 48))) = d125 p
  rw [sub414, sub559]
  rfl
theorem sub580 (p : Pattern) : d126 (change p 10000 (some 48)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 48)) else d124 (change p 10000 (some 48))) = d126 p
  rw [sub579, sub578]
  rfl
theorem sub581 (p : Pattern) : d127 (change p 10000 (some 48)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 48)) else d123 (change p 10000 (some 48))) = d127 p
  rw [sub580, sub577]
  rfl
theorem sub582 (p : Pattern) : d128 (change p 10000 (some 48)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d70 (change p 10000 (some 48))) = d128 p
  rw [sub414, sub478]
  rfl
theorem sub583 (p : Pattern) : d129 (change p 10000 (some 48)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 48)) else d126 (change p 10000 (some 48))) = d129 p
  rw [sub582, sub580]
  rfl
theorem sub584 (p : Pattern) : d130 (change p 10000 (some 48)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 48)) else d127 (change p 10000 (some 48))) = d130 p
  rw [sub583, sub581]
  rfl
theorem sub585 (p : Pattern) : d131 (change p 10000 (some 48)) = d131 p := by
  change (if p 160 then d130 (change p 10000 (some 48)) else d114 (change p 10000 (some 48))) = d131 p
  rw [sub584, sub566]
  rfl
theorem sub586 (p : Pattern) : d132 (change p 10000 (some 48)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 48)) else d116 (change p 10000 (some 48))) = d132 p
  rw [sub570, sub569]
  rfl
theorem sub587 (p : Pattern) : d133 (change p 10000 (some 48)) = d133 p := by
  change (if p 163 then d132 (change p 10000 (some 48)) else d105 (change p 10000 (some 48))) = d133 p
  rw [sub586, sub556]
  rfl
theorem sub588 (p : Pattern) : d211 (change p 10000 (some 48)) = d211 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d109 (change p 10000 (some 48))) = d211 p
  rw [sub414, sub561]
  rfl
theorem sub589 (p : Pattern) : d212 (change p 10000 (some 48)) = d212 p := by
  change (if p 162 then d211 (change p 10000 (some 48)) else d133 (change p 10000 (some 48))) = d212 p
  rw [sub588, sub587]
  rfl
theorem sub590 (p : Pattern) : d213 (change p 10000 (some 48)) = d213 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d211 (change p 10000 (some 48))) = d213 p
  rw [sub414, sub588]
  rfl
theorem sub591 (p : Pattern) : d214 (change p 10000 (some 48)) = d214 p := by
  change (if p 161 then d213 (change p 10000 (some 48)) else d212 (change p 10000 (some 48))) = d214 p
  rw [sub590, sub589]
  rfl
theorem sub592 (p : Pattern) : d139 (change p 10000 (some 48)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d116 (change p 10000 (some 48))) = d139 p
  rw [sub414, sub569]
  rfl
theorem sub593 (p : Pattern) : d140 (change p 10000 (some 48)) = d140 p := by
  change (if p 163 then d139 (change p 10000 (some 48)) else d122 (change p 10000 (some 48))) = d140 p
  rw [sub592, sub576]
  rfl
theorem sub594 (p : Pattern) : d215 (change p 10000 (some 48)) = d215 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d125 (change p 10000 (some 48))) = d215 p
  rw [sub414, sub579]
  rfl
theorem sub595 (p : Pattern) : d216 (change p 10000 (some 48)) = d216 p := by
  change (if p 162 then d215 (change p 10000 (some 48)) else d140 (change p 10000 (some 48))) = d216 p
  rw [sub594, sub593]
  rfl
theorem sub596 (p : Pattern) : d217 (change p 10000 (some 48)) = d217 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d215 (change p 10000 (some 48))) = d217 p
  rw [sub414, sub594]
  rfl
theorem sub597 (p : Pattern) : d218 (change p 10000 (some 48)) = d218 p := by
  change (if p 161 then d217 (change p 10000 (some 48)) else d216 (change p 10000 (some 48))) = d218 p
  rw [sub596, sub595]
  rfl
theorem sub598 (p : Pattern) : d219 (change p 10000 (some 48)) = d219 p := by
  change (if p 160 then d218 (change p 10000 (some 48)) else d214 (change p 10000 (some 48))) = d219 p
  rw [sub597, sub591]
  rfl
theorem sub599 (p : Pattern) : d220 (change p 10000 (some 48)) = d220 p := by
  change (if p 141 then d219 (change p 10000 (some 48)) else d131 (change p 10000 (some 48))) = d220 p
  rw [sub598, sub585]
  rfl
end NetHack.Sokoban22Refined85
