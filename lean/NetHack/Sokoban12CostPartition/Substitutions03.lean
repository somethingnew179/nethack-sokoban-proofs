/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub360 (p : Pattern) : d125 (change p 132 (some 133)) = d125 p := by
  change (if p 187 then d60 (change p 132 (some 133)) else d11 (change p 132 (some 133))) = d125 p
  rw [sub344, sub339]
  rfl
theorem sub361 (p : Pattern) : d126 (change p 132 (some 133)) = d126 p := by
  change (if p 186 then d125 (change p 132 (some 133)) else d11 (change p 132 (some 133))) = d126 p
  rw [sub360, sub339]
  rfl
theorem sub362 (p : Pattern) : d127 (change p 132 (some 133)) = d127 p := by
  change (if p 168 then d126 (change p 132 (some 133)) else d120 (change p 132 (some 133))) = d127 p
  rw [sub361, sub354]
  rfl
theorem sub363 (p : Pattern) : d128 (change p 132 (some 133)) = d128 p := by
  change (if p 160 then d65 (change p 132 (some 133)) else d127 (change p 132 (some 133))) = d128 p
  rw [sub348, sub362]
  rfl
theorem sub364 (p : Pattern) : d129 (change p 132 (some 133)) = d129 p := by
  change (if p 159 then d128 (change p 132 (some 133)) else d109 (change p 132 (some 133))) = d129 p
  rw [sub363, sub359]
  rfl
theorem sub365 (p : Pattern) : d130 (change p 132 (some 133)) = d130 p := by
  change (if p 159 then d65 (change p 132 (some 133)) else d128 (change p 132 (some 133))) = d130 p
  rw [sub348, sub363]
  rfl
theorem sub366 (p : Pattern) : d131 (change p 132 (some 133)) = d131 p := by
  change (if p 158 then d130 (change p 132 (some 133)) else d129 (change p 132 (some 133))) = d131 p
  rw [sub365, sub364]
  rfl
theorem sub367 (p : Pattern) : d132 (change p 132 (some 133)) = d132 p := by
  change (if p 141 then d131 (change p 132 (some 133)) else d124 (change p 132 (some 133))) = d132 p
  rw [sub366, sub358]
  rfl
theorem sub368 (p : Pattern) : d133 (change p 132 (some 133)) = d133 p := by
  change (if p 134 then d132 (change p 132 (some 133)) else d118 (change p 132 (some 133))) = d133 p
  rw [sub367, sub351]
  rfl
theorem sub369 (p : Pattern) : d134 (change p 132 (some 133)) = d133 p := by
  change d133 (change p 132 (some 133)) = d133 p
  exact sub368 p
theorem sub370 (p : Pattern) : d199 (change p 132 (some 133)) = d133 p := by
  change d134 (change p 132 (some 133)) = d133 p
  exact sub369 p
theorem sub371 (p : Pattern) : d137 (change p 132 (some 133)) = d137 p := by
  change (if p 186 then d55 (change p 132 (some 133)) else d119 (change p 132 (some 133))) = d137 p
  rw [sub329, sub353]
  rfl
theorem sub372 (p : Pattern) : d138 (change p 132 (some 133)) = d138 p := by
  change (if p 160 then d137 (change p 132 (some 133)) else d7 (change p 132 (some 133))) = d138 p
  rw [sub371, sub326]
  rfl
theorem sub373 (p : Pattern) : d139 (change p 132 (some 133)) = d139 p := by
  change (if p 160 then d137 (change p 132 (some 133)) else d120 (change p 132 (some 133))) = d139 p
  rw [sub371, sub354]
  rfl
theorem sub374 (p : Pattern) : d140 (change p 132 (some 133)) = d140 p := by
  change (if p 159 then d139 (change p 132 (some 133)) else d138 (change p 132 (some 133))) = d140 p
  rw [sub373, sub372]
  rfl
theorem sub375 (p : Pattern) : d141 (change p 132 (some 133)) = d141 p := by
  change (if p 159 then d55 (change p 132 (some 133)) else d139 (change p 132 (some 133))) = d141 p
  rw [sub329, sub373]
  rfl
theorem sub376 (p : Pattern) : d142 (change p 132 (some 133)) = d142 p := by
  change (if p 158 then d141 (change p 132 (some 133)) else d140 (change p 132 (some 133))) = d142 p
  rw [sub375, sub374]
  rfl
theorem sub377 (p : Pattern) : d143 (change p 132 (some 133)) = d143 p := by
  change (if p 186 then d60 (change p 132 (some 133)) else d125 (change p 132 (some 133))) = d143 p
  rw [sub344, sub360]
  rfl
theorem sub378 (p : Pattern) : d144 (change p 132 (some 133)) = d144 p := by
  change (if p 168 then d143 (change p 132 (some 133)) else d137 (change p 132 (some 133))) = d144 p
  rw [sub377, sub371]
  rfl
theorem sub379 (p : Pattern) : d145 (change p 132 (some 133)) = d145 p := by
  change (if p 160 then d144 (change p 132 (some 133)) else d12 (change p 132 (some 133))) = d145 p
  rw [sub378, sub340]
  rfl
theorem sub380 (p : Pattern) : d146 (change p 132 (some 133)) = d146 p := by
  change (if p 160 then d144 (change p 132 (some 133)) else d127 (change p 132 (some 133))) = d146 p
  rw [sub378, sub362]
  rfl
theorem sub381 (p : Pattern) : d147 (change p 132 (some 133)) = d147 p := by
  change (if p 159 then d146 (change p 132 (some 133)) else d145 (change p 132 (some 133))) = d147 p
  rw [sub380, sub379]
  rfl
theorem sub382 (p : Pattern) : d148 (change p 132 (some 133)) = d148 p := by
  change (if p 159 then d65 (change p 132 (some 133)) else d146 (change p 132 (some 133))) = d148 p
  rw [sub348, sub380]
  rfl
theorem sub383 (p : Pattern) : d149 (change p 132 (some 133)) = d149 p := by
  change (if p 158 then d148 (change p 132 (some 133)) else d147 (change p 132 (some 133))) = d149 p
  rw [sub382, sub381]
  rfl
theorem sub384 (p : Pattern) : d150 (change p 132 (some 133)) = d150 p := by
  change (if p 141 then d149 (change p 132 (some 133)) else d142 (change p 132 (some 133))) = d150 p
  rw [sub383, sub376]
  rfl
theorem sub385 (p : Pattern) : d66 (change p 132 (some 133)) = d66 p := by
  change (if p 141 then d65 (change p 132 (some 133)) else d55 (change p 132 (some 133))) = d66 p
  rw [sub348, sub329]
  rfl
theorem sub386 (p : Pattern) : d151 (change p 132 (some 133)) = d151 p := by
  change (if p 134 then d66 (change p 132 (some 133)) else d150 (change p 132 (some 133))) = d151 p
  rw [sub385, sub384]
  rfl
theorem sub387 (p : Pattern) : d152 (change p 132 (some 133)) = d151 p := by
  change d151 (change p 132 (some 133)) = d151 p
  exact sub386 p
theorem sub388 (p : Pattern) : d200 (change p 132 (some 133)) = d151 p := by
  change d152 (change p 132 (some 133)) = d151 p
  exact sub387 p
theorem sub389 (p : Pattern) : d201 (change p 132 (some 133)) = d772 p := by
  change (if p 108 then d200 (change p 132 (some 133)) else d199 (change p 132 (some 133))) = d772 p
  rw [sub388, sub370]
  rfl
theorem sub390 (p : Pattern) : d0 (change p 158 none) = d0 p := by
  rfl
theorem sub391 (p : Pattern) : d2 (change p 158 none) = d2 p := by
  rfl
theorem sub392 (p : Pattern) : d6 (change p 158 none) = d6 p := by
  change (if p 193 then d2 (change p 158 none) else d0 (change p 158 none)) = d6 p
  rw [sub391, sub390]
  rfl
theorem sub393 (p : Pattern) : d7 (change p 158 none) = d7 p := by
  change (if p 192 then d6 (change p 158 none) else d0 (change p 158 none)) = d7 p
  rw [sub392, sub390]
  rfl
theorem sub394 (p : Pattern) : d4 (change p 158 none) = d4 p := by
  rfl
theorem sub395 (p : Pattern) : d54 (change p 158 none) = d54 p := by
  change (if p 193 then d4 (change p 158 none) else d2 (change p 158 none)) = d54 p
  rw [sub394, sub391]
  rfl
theorem sub396 (p : Pattern) : d55 (change p 158 none) = d55 p := by
  change (if p 192 then d54 (change p 158 none) else d2 (change p 158 none)) = d55 p
  rw [sub395, sub391]
  rfl
theorem sub397 (p : Pattern) : d56 (change p 158 none) = d56 p := by
  change (if p 186 then d55 (change p 158 none) else d7 (change p 158 none)) = d56 p
  rw [sub396, sub393]
  rfl
theorem sub398 (p : Pattern) : d57 (change p 158 none) = d57 p := by
  change (if p 160 then d56 (change p 158 none) else d7 (change p 158 none)) = d57 p
  rw [sub397, sub393]
  rfl
theorem sub399 (p : Pattern) : d68 (change p 158 none) = d57 p := by
  change d57 (change p 158 none) = d57 p
  exact sub398 p
theorem sub400 (p : Pattern) : d1 (change p 158 none) = d1 p := by
  rfl
theorem sub401 (p : Pattern) : d8 (change p 158 none) = d8 p := by
  change (if p 271 then d1 (change p 158 none) else d0 (change p 158 none)) = d8 p
  rw [sub400, sub390]
  rfl
theorem sub402 (p : Pattern) : d3 (change p 158 none) = d3 p := by
  rfl
theorem sub403 (p : Pattern) : d9 (change p 158 none) = d9 p := by
  change (if p 271 then d3 (change p 158 none) else d2 (change p 158 none)) = d9 p
  rw [sub402, sub391]
  rfl
theorem sub404 (p : Pattern) : d10 (change p 158 none) = d10 p := by
  change (if p 193 then d9 (change p 158 none) else d8 (change p 158 none)) = d10 p
  rw [sub403, sub401]
  rfl
theorem sub405 (p : Pattern) : d11 (change p 158 none) = d11 p := by
  change (if p 192 then d10 (change p 158 none) else d8 (change p 158 none)) = d11 p
  rw [sub404, sub401]
  rfl
theorem sub406 (p : Pattern) : d12 (change p 158 none) = d12 p := by
  change (if p 168 then d11 (change p 158 none) else d7 (change p 158 none)) = d12 p
  rw [sub405, sub393]
  rfl
theorem sub407 (p : Pattern) : d5 (change p 158 none) = d5 p := by
  rfl
theorem sub408 (p : Pattern) : d58 (change p 158 none) = d58 p := by
  change (if p 271 then d5 (change p 158 none) else d4 (change p 158 none)) = d58 p
  rw [sub407, sub394]
  rfl
theorem sub409 (p : Pattern) : d59 (change p 158 none) = d59 p := by
  change (if p 193 then d58 (change p 158 none) else d9 (change p 158 none)) = d59 p
  rw [sub408, sub403]
  rfl
theorem sub410 (p : Pattern) : d60 (change p 158 none) = d60 p := by
  change (if p 192 then d59 (change p 158 none) else d9 (change p 158 none)) = d60 p
  rw [sub409, sub403]
  rfl
theorem sub411 (p : Pattern) : d61 (change p 158 none) = d61 p := by
  change (if p 186 then d60 (change p 158 none) else d11 (change p 158 none)) = d61 p
  rw [sub410, sub405]
  rfl
theorem sub412 (p : Pattern) : d62 (change p 158 none) = d62 p := by
  change (if p 168 then d61 (change p 158 none) else d56 (change p 158 none)) = d62 p
  rw [sub411, sub397]
  rfl
theorem sub413 (p : Pattern) : d63 (change p 158 none) = d63 p := by
  change (if p 160 then d62 (change p 158 none) else d12 (change p 158 none)) = d63 p
  rw [sub412, sub406]
  rfl
theorem sub414 (p : Pattern) : d69 (change p 158 none) = d63 p := by
  change d63 (change p 158 none) = d63 p
  exact sub413 p
theorem sub415 (p : Pattern) : d70 (change p 158 none) = d64 p := by
  change (if p 141 then d69 (change p 158 none) else d68 (change p 158 none)) = d64 p
  rw [sub414, sub399]
  rfl
theorem sub416 (p : Pattern) : d106 (change p 158 none) = d106 p := by
  change (if p 160 then d55 (change p 158 none) else d7 (change p 158 none)) = d106 p
  rw [sub396, sub393]
  rfl
theorem sub417 (p : Pattern) : d229 (change p 158 none) = d106 p := by
  change d106 (change p 158 none) = d106 p
  exact sub416 p
theorem sub418 (p : Pattern) : d65 (change p 158 none) = d65 p := by
  change (if p 168 then d60 (change p 158 none) else d55 (change p 158 none)) = d65 p
  rw [sub410, sub396]
  rfl
theorem sub419 (p : Pattern) : d109 (change p 158 none) = d109 p := by
  change (if p 160 then d65 (change p 158 none) else d12 (change p 158 none)) = d109 p
  rw [sub418, sub406]
  rfl
theorem sub420 (p : Pattern) : d230 (change p 158 none) = d109 p := by
  change d109 (change p 158 none) = d109 p
  exact sub419 p
theorem sub421 (p : Pattern) : d231 (change p 158 none) = d227 p := by
  change (if p 141 then d230 (change p 158 none) else d229 (change p 158 none)) = d227 p
  rw [sub420, sub417]
  rfl
theorem sub422 (p : Pattern) : d232 (change p 158 none) = d228 p := by
  change (if p 134 then d231 (change p 158 none) else d70 (change p 158 none)) = d228 p
  rw [sub421, sub415]
  rfl
theorem sub423 (p : Pattern) : d119 (change p 158 none) = d119 p := by
  change (if p 187 then d55 (change p 158 none) else d7 (change p 158 none)) = d119 p
  rw [sub396, sub393]
  rfl
theorem sub424 (p : Pattern) : d120 (change p 158 none) = d120 p := by
  change (if p 186 then d119 (change p 158 none) else d7 (change p 158 none)) = d120 p
  rw [sub423, sub393]
  rfl
theorem sub425 (p : Pattern) : d121 (change p 158 none) = d121 p := by
  change (if p 160 then d55 (change p 158 none) else d120 (change p 158 none)) = d121 p
  rw [sub396, sub424]
  rfl
theorem sub426 (p : Pattern) : d122 (change p 158 none) = d122 p := by
  change (if p 159 then d121 (change p 158 none) else d106 (change p 158 none)) = d122 p
  rw [sub425, sub416]
  rfl
theorem sub427 (p : Pattern) : d181 (change p 158 none) = d122 p := by
  change d122 (change p 158 none) = d122 p
  exact sub426 p
theorem sub428 (p : Pattern) : d125 (change p 158 none) = d125 p := by
  change (if p 187 then d60 (change p 158 none) else d11 (change p 158 none)) = d125 p
  rw [sub410, sub405]
  rfl
theorem sub429 (p : Pattern) : d126 (change p 158 none) = d126 p := by
  change (if p 186 then d125 (change p 158 none) else d11 (change p 158 none)) = d126 p
  rw [sub428, sub405]
  rfl
theorem sub430 (p : Pattern) : d127 (change p 158 none) = d127 p := by
  change (if p 168 then d126 (change p 158 none) else d120 (change p 158 none)) = d127 p
  rw [sub429, sub424]
  rfl
theorem sub431 (p : Pattern) : d128 (change p 158 none) = d128 p := by
  change (if p 160 then d65 (change p 158 none) else d127 (change p 158 none)) = d128 p
  rw [sub418, sub430]
  rfl
theorem sub432 (p : Pattern) : d129 (change p 158 none) = d129 p := by
  change (if p 159 then d128 (change p 158 none) else d109 (change p 158 none)) = d129 p
  rw [sub431, sub419]
  rfl
theorem sub433 (p : Pattern) : d240 (change p 158 none) = d129 p := by
  change d129 (change p 158 none) = d129 p
  exact sub432 p
theorem sub434 (p : Pattern) : d241 (change p 158 none) = d775 p := by
  change (if p 141 then d240 (change p 158 none) else d181 (change p 158 none)) = d775 p
  rw [sub433, sub427]
  rfl
theorem sub435 (p : Pattern) : d242 (change p 158 none) = d776 p := by
  change (if p 134 then d241 (change p 158 none) else d70 (change p 158 none)) = d776 p
  rw [sub434, sub415]
  rfl
theorem sub436 (p : Pattern) : d315 (change p 158 none) = d777 p := by
  change (if p 133 then d242 (change p 158 none) else d232 (change p 158 none)) = d777 p
  rw [sub435, sub422]
  rfl
theorem sub437 (p : Pattern) : d66 (change p 158 none) = d66 p := by
  change (if p 141 then d65 (change p 158 none) else d55 (change p 158 none)) = d66 p
  rw [sub418, sub396]
  rfl
theorem sub438 (p : Pattern) : d244 (change p 158 none) = d778 p := by
  change (if p 133 then d66 (change p 158 none) else d242 (change p 158 none)) = d778 p
  rw [sub437, sub435]
  rfl
theorem sub439 (p : Pattern) : d316 (change p 158 none) = d779 p := by
  change (if p 132 then d244 (change p 158 none) else d315 (change p 158 none)) = d779 p
  rw [sub438, sub436]
  rfl
theorem sub440 (p : Pattern) : d71 (change p 158 none) = d67 p := by
  change (if p 134 then d66 (change p 158 none) else d70 (change p 158 none)) = d67 p
  rw [sub437, sub415]
  rfl
theorem sub441 (p : Pattern) : d137 (change p 158 none) = d137 p := by
  change (if p 186 then d55 (change p 158 none) else d119 (change p 158 none)) = d137 p
  rw [sub396, sub423]
  rfl
theorem sub442 (p : Pattern) : d138 (change p 158 none) = d138 p := by
  change (if p 160 then d137 (change p 158 none) else d7 (change p 158 none)) = d138 p
  rw [sub441, sub393]
  rfl
theorem sub443 (p : Pattern) : d139 (change p 158 none) = d139 p := by
  change (if p 160 then d137 (change p 158 none) else d120 (change p 158 none)) = d139 p
  rw [sub441, sub424]
  rfl
theorem sub444 (p : Pattern) : d140 (change p 158 none) = d140 p := by
  change (if p 159 then d139 (change p 158 none) else d138 (change p 158 none)) = d140 p
  rw [sub443, sub442]
  rfl
theorem sub445 (p : Pattern) : d188 (change p 158 none) = d140 p := by
  change d140 (change p 158 none) = d140 p
  exact sub444 p
theorem sub446 (p : Pattern) : d143 (change p 158 none) = d143 p := by
  change (if p 186 then d60 (change p 158 none) else d125 (change p 158 none)) = d143 p
  rw [sub410, sub428]
  rfl
theorem sub447 (p : Pattern) : d144 (change p 158 none) = d144 p := by
  change (if p 168 then d143 (change p 158 none) else d137 (change p 158 none)) = d144 p
  rw [sub446, sub441]
  rfl
theorem sub448 (p : Pattern) : d145 (change p 158 none) = d145 p := by
  change (if p 160 then d144 (change p 158 none) else d12 (change p 158 none)) = d145 p
  rw [sub447, sub406]
  rfl
theorem sub449 (p : Pattern) : d146 (change p 158 none) = d146 p := by
  change (if p 160 then d144 (change p 158 none) else d127 (change p 158 none)) = d146 p
  rw [sub447, sub430]
  rfl
theorem sub450 (p : Pattern) : d147 (change p 158 none) = d147 p := by
  change (if p 159 then d146 (change p 158 none) else d145 (change p 158 none)) = d147 p
  rw [sub449, sub448]
  rfl
theorem sub451 (p : Pattern) : d249 (change p 158 none) = d147 p := by
  change d147 (change p 158 none) = d147 p
  exact sub450 p
theorem sub452 (p : Pattern) : d250 (change p 158 none) = d780 p := by
  change (if p 141 then d249 (change p 158 none) else d188 (change p 158 none)) = d780 p
  rw [sub451, sub445]
  rfl
theorem sub453 (p : Pattern) : d251 (change p 158 none) = d781 p := by
  change (if p 134 then d66 (change p 158 none) else d250 (change p 158 none)) = d781 p
  rw [sub437, sub452]
  rfl
theorem sub454 (p : Pattern) : d317 (change p 158 none) = d782 p := by
  change (if p 133 then d251 (change p 158 none) else d71 (change p 158 none)) = d782 p
  rw [sub453, sub440]
  rfl
theorem sub455 (p : Pattern) : d153 (change p 158 none) = d153 p := by
  change (if p 159 then d139 (change p 158 none) else d57 (change p 158 none)) = d153 p
  rw [sub443, sub398]
  rfl
theorem sub456 (p : Pattern) : d191 (change p 158 none) = d153 p := by
  change d153 (change p 158 none) = d153 p
  exact sub455 p
theorem sub457 (p : Pattern) : d155 (change p 158 none) = d155 p := by
  change (if p 159 then d146 (change p 158 none) else d63 (change p 158 none)) = d155 p
  rw [sub449, sub413]
  rfl
theorem sub458 (p : Pattern) : d253 (change p 158 none) = d155 p := by
  change d155 (change p 158 none) = d155 p
  exact sub457 p
theorem sub459 (p : Pattern) : d254 (change p 158 none) = d783 p := by
  change (if p 141 then d253 (change p 158 none) else d191 (change p 158 none)) = d783 p
  rw [sub458, sub456]
  rfl
theorem sub460 (p : Pattern) : d255 (change p 158 none) = d784 p := by
  change (if p 134 then d66 (change p 158 none) else d254 (change p 158 none)) = d784 p
  rw [sub437, sub459]
  rfl
theorem sub461 (p : Pattern) : d256 (change p 158 none) = d785 p := by
  change (if p 133 then d66 (change p 158 none) else d255 (change p 158 none)) = d785 p
  rw [sub437, sub460]
  rfl
theorem sub462 (p : Pattern) : d318 (change p 158 none) = d786 p := by
  change (if p 132 then d256 (change p 158 none) else d317 (change p 158 none)) = d786 p
  rw [sub461, sub454]
  rfl
theorem sub463 (p : Pattern) : d319 (change p 158 none) = d787 p := by
  change (if p 108 then d318 (change p 158 none) else d316 (change p 158 none)) = d787 p
  rw [sub462, sub439]
  rfl
theorem sub464 (p : Pattern) : d0 (change p 133 (some 134)) = d0 p := by
  rfl
theorem sub465 (p : Pattern) : d2 (change p 133 (some 134)) = d2 p := by
  rfl
theorem sub466 (p : Pattern) : d6 (change p 133 (some 134)) = d6 p := by
  change (if p 193 then d2 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d6 p
  rw [sub465, sub464]
  rfl
theorem sub467 (p : Pattern) : d7 (change p 133 (some 134)) = d7 p := by
  change (if p 192 then d6 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d7 p
  rw [sub466, sub464]
  rfl
theorem sub468 (p : Pattern) : d4 (change p 133 (some 134)) = d4 p := by
  rfl
theorem sub469 (p : Pattern) : d54 (change p 133 (some 134)) = d54 p := by
  change (if p 193 then d4 (change p 133 (some 134)) else d2 (change p 133 (some 134))) = d54 p
  rw [sub468, sub465]
  rfl
theorem sub470 (p : Pattern) : d55 (change p 133 (some 134)) = d55 p := by
  change (if p 192 then d54 (change p 133 (some 134)) else d2 (change p 133 (some 134))) = d55 p
  rw [sub469, sub465]
  rfl
theorem sub471 (p : Pattern) : d106 (change p 133 (some 134)) = d106 p := by
  change (if p 160 then d55 (change p 133 (some 134)) else d7 (change p 133 (some 134))) = d106 p
  rw [sub470, sub467]
  rfl
theorem sub472 (p : Pattern) : d107 (change p 133 (some 134)) = d107 p := by
  change (if p 159 then d55 (change p 133 (some 134)) else d106 (change p 133 (some 134))) = d107 p
  rw [sub470, sub471]
  rfl
theorem sub473 (p : Pattern) : d108 (change p 133 (some 134)) = d108 p := by
  change (if p 158 then d107 (change p 133 (some 134)) else d106 (change p 133 (some 134))) = d108 p
  rw [sub472, sub471]
  rfl
theorem sub474 (p : Pattern) : d1 (change p 133 (some 134)) = d1 p := by
  rfl
theorem sub475 (p : Pattern) : d8 (change p 133 (some 134)) = d8 p := by
  change (if p 271 then d1 (change p 133 (some 134)) else d0 (change p 133 (some 134))) = d8 p
  rw [sub474, sub464]
  rfl
theorem sub476 (p : Pattern) : d3 (change p 133 (some 134)) = d3 p := by
  rfl
theorem sub477 (p : Pattern) : d9 (change p 133 (some 134)) = d9 p := by
  change (if p 271 then d3 (change p 133 (some 134)) else d2 (change p 133 (some 134))) = d9 p
  rw [sub476, sub465]
  rfl
theorem sub478 (p : Pattern) : d10 (change p 133 (some 134)) = d10 p := by
  change (if p 193 then d9 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d10 p
  rw [sub477, sub475]
  rfl
theorem sub479 (p : Pattern) : d11 (change p 133 (some 134)) = d11 p := by
  change (if p 192 then d10 (change p 133 (some 134)) else d8 (change p 133 (some 134))) = d11 p
  rw [sub478, sub475]
  rfl
end NetHack.Sokoban12CostPartition
