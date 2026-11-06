/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub360 (p : Pattern) : d33 (change p 86 (some 112)) = d33 p := by
  change (if p 158 then d32 (change p 86 (some 112)) else d31 (change p 86 (some 112))) = d33 p
  rw [sub359, sub358]
  rfl
theorem sub361 (p : Pattern) : d34 (change p 86 (some 112)) = d34 p := by
  change (if p 139 then d24 (change p 86 (some 112)) else d33 (change p 86 (some 112))) = d34 p
  rw [sub352, sub360]
  rfl
theorem sub362 (p : Pattern) : d48 (change p 86 (some 112)) = d48 p := by
  change (if p 134 then d34 (change p 86 (some 112)) else d15 (change p 86 (some 112))) = d48 p
  rw [sub361, sub344]
  rfl
theorem sub363 (p : Pattern) : d37 (change p 86 (some 112)) = d37 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d5 (change p 86 (some 112))) = d37 p
  rw [sub330, sub333]
  rfl
theorem sub364 (p : Pattern) : d38 (change p 86 (some 112)) = d38 p := by
  change (if p 158 then d37 (change p 86 (some 112)) else d6 (change p 86 (some 112))) = d38 p
  rw [sub363, sub334]
  rfl
theorem sub365 (p : Pattern) : d39 (change p 86 (some 112)) = d39 p := by
  change (if p 159 then d2 (change p 86 (some 112)) else d11 (change p 86 (some 112))) = d39 p
  rw [sub330, sub340]
  rfl
theorem sub366 (p : Pattern) : d40 (change p 86 (some 112)) = d40 p := by
  change (if p 158 then d39 (change p 86 (some 112)) else d12 (change p 86 (some 112))) = d40 p
  rw [sub365, sub341]
  rfl
theorem sub367 (p : Pattern) : d41 (change p 86 (some 112)) = d41 p := by
  change (if p 139 then d40 (change p 86 (some 112)) else d38 (change p 86 (some 112))) = d41 p
  rw [sub366, sub364]
  rfl
theorem sub368 (p : Pattern) : d49 (change p 86 (some 112)) = d49 p := by
  change (if p 134 then d25 (change p 86 (some 112)) else d41 (change p 86 (some 112))) = d49 p
  rw [sub353, sub367]
  rfl
theorem sub369 (p : Pattern) : d50 (change p 86 (some 112)) = d50 p := by
  change (if p 133 then d49 (change p 86 (some 112)) else d48 (change p 86 (some 112))) = d50 p
  rw [sub368, sub362]
  rfl
theorem sub370 (p : Pattern) : d51 (change p 86 (some 112)) = d51 p := by
  change (if p 132 then d50 (change p 86 (some 112)) else d47 (change p 86 (some 112))) = d51 p
  rw [sub369, sub355]
  rfl
theorem sub371 (p : Pattern) : d52 (change p 86 (some 112)) = d52 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d8 (change p 86 (some 112))) = d52 p
  rw [sub330, sub336]
  rfl
theorem sub372 (p : Pattern) : d53 (change p 86 (some 112)) = d53 p := by
  change (if p 138 then d52 (change p 86 (some 112)) else d15 (change p 86 (some 112))) = d53 p
  rw [sub371, sub344]
  rfl
theorem sub373 (p : Pattern) : d54 (change p 86 (some 112)) = d54 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d20 (change p 86 (some 112))) = d54 p
  rw [sub330, sub348]
  rfl
theorem sub374 (p : Pattern) : d55 (change p 86 (some 112)) = d55 p := by
  change (if p 138 then d54 (change p 86 (some 112)) else d25 (change p 86 (some 112))) = d55 p
  rw [sub373, sub353]
  rfl
theorem sub375 (p : Pattern) : d56 (change p 86 (some 112)) = d56 p := by
  change (if p 134 then d55 (change p 86 (some 112)) else d53 (change p 86 (some 112))) = d56 p
  rw [sub374, sub372]
  rfl
theorem sub376 (p : Pattern) : d57 (change p 86 (some 112)) = d57 p := by
  change (if p 133 then d56 (change p 86 (some 112)) else d53 (change p 86 (some 112))) = d57 p
  rw [sub375, sub372]
  rfl
theorem sub377 (p : Pattern) : d58 (change p 86 (some 112)) = d58 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d33 (change p 86 (some 112))) = d58 p
  rw [sub330, sub360]
  rfl
theorem sub378 (p : Pattern) : d59 (change p 86 (some 112)) = d59 p := by
  change (if p 138 then d58 (change p 86 (some 112)) else d34 (change p 86 (some 112))) = d59 p
  rw [sub377, sub361]
  rfl
theorem sub379 (p : Pattern) : d60 (change p 86 (some 112)) = d60 p := by
  change (if p 134 then d59 (change p 86 (some 112)) else d53 (change p 86 (some 112))) = d60 p
  rw [sub378, sub372]
  rfl
theorem sub380 (p : Pattern) : d61 (change p 86 (some 112)) = d61 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d38 (change p 86 (some 112))) = d61 p
  rw [sub330, sub364]
  rfl
theorem sub381 (p : Pattern) : d62 (change p 86 (some 112)) = d62 p := by
  change (if p 138 then d61 (change p 86 (some 112)) else d41 (change p 86 (some 112))) = d62 p
  rw [sub380, sub367]
  rfl
theorem sub382 (p : Pattern) : d63 (change p 86 (some 112)) = d63 p := by
  change (if p 134 then d55 (change p 86 (some 112)) else d62 (change p 86 (some 112))) = d63 p
  rw [sub374, sub381]
  rfl
theorem sub383 (p : Pattern) : d64 (change p 86 (some 112)) = d64 p := by
  change (if p 133 then d63 (change p 86 (some 112)) else d60 (change p 86 (some 112))) = d64 p
  rw [sub382, sub379]
  rfl
theorem sub384 (p : Pattern) : d65 (change p 86 (some 112)) = d65 p := by
  change (if p 132 then d64 (change p 86 (some 112)) else d57 (change p 86 (some 112))) = d65 p
  rw [sub383, sub376]
  rfl
theorem sub385 (p : Pattern) : d66 (change p 86 (some 112)) = d66 p := by
  change (if p 113 then d65 (change p 86 (some 112)) else d51 (change p 86 (some 112))) = d66 p
  rw [sub384, sub370]
  rfl
theorem sub386 (p : Pattern) : d67 (change p 86 (some 112)) = d66 p := by
  change d66 (change p 86 (some 112)) = d66 p
  exact sub385 p
theorem sub387 (p : Pattern) : d68 (change p 86 (some 112)) = d68 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d40 (change p 86 (some 112))) = d68 p
  rw [sub330, sub366]
  rfl
theorem sub388 (p : Pattern) : d70 (change p 86 (some 112)) = d70 p := by
  change (if p 139 then d2 (change p 86 (some 112)) else d24 (change p 86 (some 112))) = d70 p
  rw [sub330, sub352]
  rfl
theorem sub389 (p : Pattern) : d75 (change p 86 (some 112)) = d75 p := by
  change (if p 134 then d70 (change p 86 (some 112)) else d68 (change p 86 (some 112))) = d75 p
  rw [sub388, sub387]
  rfl
theorem sub390 (p : Pattern) : d79 (change p 86 (some 112)) = d79 p := by
  change (if p 133 then d75 (change p 86 (some 112)) else d46 (change p 86 (some 112))) = d79 p
  rw [sub389, sub354]
  rfl
theorem sub391 (p : Pattern) : d80 (change p 86 (some 112)) = d80 p := by
  change (if p 132 then d79 (change p 86 (some 112)) else d47 (change p 86 (some 112))) = d80 p
  rw [sub390, sub355]
  rfl
theorem sub392 (p : Pattern) : d81 (change p 86 (some 112)) = d81 p := by
  change (if p 133 then d75 (change p 86 (some 112)) else d56 (change p 86 (some 112))) = d81 p
  rw [sub389, sub375]
  rfl
theorem sub393 (p : Pattern) : d82 (change p 86 (some 112)) = d82 p := by
  change (if p 132 then d81 (change p 86 (some 112)) else d57 (change p 86 (some 112))) = d82 p
  rw [sub392, sub376]
  rfl
theorem sub394 (p : Pattern) : d83 (change p 86 (some 112)) = d83 p := by
  change (if p 113 then d82 (change p 86 (some 112)) else d80 (change p 86 (some 112))) = d83 p
  rw [sub393, sub391]
  rfl
theorem sub395 (p : Pattern) : d84 (change p 86 (some 112)) = d83 p := by
  change d83 (change p 86 (some 112)) = d83 p
  exact sub394 p
theorem sub396 (p : Pattern) : d85 (change p 86 (some 112)) = d837 p := by
  change (if p 106 then d84 (change p 86 (some 112)) else d67 (change p 86 (some 112))) = d837 p
  rw [sub395, sub386]
  rfl
theorem sub397 (p : Pattern) : d174 (change p 86 (some 112)) = d837 p := by
  change d85 (change p 86 (some 112)) = d837 p
  exact sub396 p
theorem sub398 (p : Pattern) : d117 (change p 86 (some 112)) = d83 p := by
  change d83 (change p 86 (some 112)) = d83 p
  exact sub394 p
theorem sub399 (p : Pattern) : d118 (change p 86 (some 112)) = d837 p := by
  change (if p 106 then d117 (change p 86 (some 112)) else d67 (change p 86 (some 112))) = d837 p
  rw [sub398, sub386]
  rfl
theorem sub400 (p : Pattern) : d175 (change p 86 (some 112)) = d837 p := by
  change d118 (change p 86 (some 112)) = d837 p
  exact sub399 p
theorem sub401 (p : Pattern) : d176 (change p 86 (some 112)) = d837 p := by
  change (if p 80 then d175 (change p 86 (some 112)) else d174 (change p 86 (some 112))) = d837 p
  rw [sub400, sub397]
  simp only [ite_self]
theorem sub402 (p : Pattern) : d0 (change p 106 (some 132)) = d0 p := by
  rfl
theorem sub403 (p : Pattern) : d2 (change p 106 (some 132)) = d2 p := by
  rfl
theorem sub404 (p : Pattern) : d3 (change p 106 (some 132)) = d3 p := by
  change (if p 161 then d2 (change p 106 (some 132)) else d0 (change p 106 (some 132))) = d3 p
  rw [sub403, sub402]
  rfl
theorem sub405 (p : Pattern) : d4 (change p 106 (some 132)) = d4 p := by
  change (if p 160 then d3 (change p 106 (some 132)) else d0 (change p 106 (some 132))) = d4 p
  rw [sub404, sub402]
  rfl
theorem sub406 (p : Pattern) : d5 (change p 106 (some 132)) = d5 p := by
  change (if p 160 then d2 (change p 106 (some 132)) else d0 (change p 106 (some 132))) = d5 p
  rw [sub403, sub402]
  rfl
theorem sub407 (p : Pattern) : d6 (change p 106 (some 132)) = d6 p := by
  change (if p 159 then d5 (change p 106 (some 132)) else d4 (change p 106 (some 132))) = d6 p
  rw [sub406, sub405]
  rfl
theorem sub408 (p : Pattern) : d7 (change p 106 (some 132)) = d7 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d4 (change p 106 (some 132))) = d7 p
  rw [sub403, sub405]
  rfl
theorem sub409 (p : Pattern) : d8 (change p 106 (some 132)) = d8 p := by
  change (if p 158 then d7 (change p 106 (some 132)) else d6 (change p 106 (some 132))) = d8 p
  rw [sub408, sub407]
  rfl
theorem sub410 (p : Pattern) : d1 (change p 106 (some 132)) = d1 p := by
  rfl
theorem sub411 (p : Pattern) : d9 (change p 106 (some 132)) = d9 p := by
  change (if p 161 then d2 (change p 106 (some 132)) else d1 (change p 106 (some 132))) = d9 p
  rw [sub403, sub410]
  rfl
theorem sub412 (p : Pattern) : d10 (change p 106 (some 132)) = d10 p := by
  change (if p 160 then d9 (change p 106 (some 132)) else d1 (change p 106 (some 132))) = d10 p
  rw [sub411, sub410]
  rfl
theorem sub413 (p : Pattern) : d11 (change p 106 (some 132)) = d11 p := by
  change (if p 160 then d2 (change p 106 (some 132)) else d1 (change p 106 (some 132))) = d11 p
  rw [sub403, sub410]
  rfl
theorem sub414 (p : Pattern) : d12 (change p 106 (some 132)) = d12 p := by
  change (if p 159 then d11 (change p 106 (some 132)) else d10 (change p 106 (some 132))) = d12 p
  rw [sub413, sub412]
  rfl
theorem sub415 (p : Pattern) : d13 (change p 106 (some 132)) = d13 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d10 (change p 106 (some 132))) = d13 p
  rw [sub403, sub412]
  rfl
theorem sub416 (p : Pattern) : d14 (change p 106 (some 132)) = d14 p := by
  change (if p 158 then d13 (change p 106 (some 132)) else d12 (change p 106 (some 132))) = d14 p
  rw [sub415, sub414]
  rfl
theorem sub417 (p : Pattern) : d15 (change p 106 (some 132)) = d15 p := by
  change (if p 139 then d14 (change p 106 (some 132)) else d8 (change p 106 (some 132))) = d15 p
  rw [sub416, sub409]
  rfl
theorem sub418 (p : Pattern) : d16 (change p 106 (some 132)) = d16 p := by
  change (if p 138 then d15 (change p 106 (some 132)) else d8 (change p 106 (some 132))) = d16 p
  rw [sub417, sub409]
  rfl
theorem sub419 (p : Pattern) : d29 (change p 106 (some 132)) = d29 p := by
  change (if p 161 then d1 (change p 106 (some 132)) else d0 (change p 106 (some 132))) = d29 p
  rw [sub410, sub402]
  rfl
theorem sub420 (p : Pattern) : d30 (change p 106 (some 132)) = d30 p := by
  change (if p 160 then d2 (change p 106 (some 132)) else d29 (change p 106 (some 132))) = d30 p
  rw [sub403, sub419]
  rfl
theorem sub421 (p : Pattern) : d31 (change p 106 (some 132)) = d31 p := by
  change (if p 159 then d30 (change p 106 (some 132)) else d4 (change p 106 (some 132))) = d31 p
  rw [sub420, sub405]
  rfl
theorem sub422 (p : Pattern) : d32 (change p 106 (some 132)) = d32 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d30 (change p 106 (some 132))) = d32 p
  rw [sub403, sub420]
  rfl
theorem sub423 (p : Pattern) : d33 (change p 106 (some 132)) = d33 p := by
  change (if p 158 then d32 (change p 106 (some 132)) else d31 (change p 106 (some 132))) = d33 p
  rw [sub422, sub421]
  rfl
theorem sub424 (p : Pattern) : d21 (change p 106 (some 132)) = d21 p := by
  change (if p 160 then d2 (change p 106 (some 132)) else d9 (change p 106 (some 132))) = d21 p
  rw [sub403, sub411]
  rfl
theorem sub425 (p : Pattern) : d22 (change p 106 (some 132)) = d22 p := by
  change (if p 159 then d21 (change p 106 (some 132)) else d10 (change p 106 (some 132))) = d22 p
  rw [sub424, sub412]
  rfl
theorem sub426 (p : Pattern) : d23 (change p 106 (some 132)) = d23 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d21 (change p 106 (some 132))) = d23 p
  rw [sub403, sub424]
  rfl
theorem sub427 (p : Pattern) : d24 (change p 106 (some 132)) = d24 p := by
  change (if p 158 then d23 (change p 106 (some 132)) else d22 (change p 106 (some 132))) = d24 p
  rw [sub426, sub425]
  rfl
theorem sub428 (p : Pattern) : d34 (change p 106 (some 132)) = d34 p := by
  change (if p 139 then d24 (change p 106 (some 132)) else d33 (change p 106 (some 132))) = d34 p
  rw [sub427, sub423]
  rfl
theorem sub429 (p : Pattern) : d35 (change p 106 (some 132)) = d35 p := by
  change (if p 138 then d34 (change p 106 (some 132)) else d33 (change p 106 (some 132))) = d35 p
  rw [sub428, sub423]
  rfl
theorem sub430 (p : Pattern) : d36 (change p 106 (some 132)) = d36 p := by
  change (if p 134 then d35 (change p 106 (some 132)) else d16 (change p 106 (some 132))) = d36 p
  rw [sub429, sub418]
  rfl
theorem sub431 (p : Pattern) : d37 (change p 106 (some 132)) = d37 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d5 (change p 106 (some 132))) = d37 p
  rw [sub403, sub406]
  rfl
theorem sub432 (p : Pattern) : d38 (change p 106 (some 132)) = d38 p := by
  change (if p 158 then d37 (change p 106 (some 132)) else d6 (change p 106 (some 132))) = d38 p
  rw [sub431, sub407]
  rfl
theorem sub433 (p : Pattern) : d39 (change p 106 (some 132)) = d39 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d11 (change p 106 (some 132))) = d39 p
  rw [sub403, sub413]
  rfl
theorem sub434 (p : Pattern) : d40 (change p 106 (some 132)) = d40 p := by
  change (if p 158 then d39 (change p 106 (some 132)) else d12 (change p 106 (some 132))) = d40 p
  rw [sub433, sub414]
  rfl
theorem sub435 (p : Pattern) : d41 (change p 106 (some 132)) = d41 p := by
  change (if p 139 then d40 (change p 106 (some 132)) else d38 (change p 106 (some 132))) = d41 p
  rw [sub434, sub432]
  rfl
theorem sub436 (p : Pattern) : d42 (change p 106 (some 132)) = d42 p := by
  change (if p 138 then d41 (change p 106 (some 132)) else d38 (change p 106 (some 132))) = d42 p
  rw [sub435, sub432]
  rfl
theorem sub437 (p : Pattern) : d17 (change p 106 (some 132)) = d17 p := by
  change (if p 160 then d2 (change p 106 (some 132)) else d3 (change p 106 (some 132))) = d17 p
  rw [sub403, sub404]
  rfl
theorem sub438 (p : Pattern) : d18 (change p 106 (some 132)) = d18 p := by
  change (if p 159 then d17 (change p 106 (some 132)) else d4 (change p 106 (some 132))) = d18 p
  rw [sub437, sub405]
  rfl
theorem sub439 (p : Pattern) : d19 (change p 106 (some 132)) = d19 p := by
  change (if p 159 then d2 (change p 106 (some 132)) else d17 (change p 106 (some 132))) = d19 p
  rw [sub403, sub437]
  rfl
theorem sub440 (p : Pattern) : d20 (change p 106 (some 132)) = d20 p := by
  change (if p 158 then d19 (change p 106 (some 132)) else d18 (change p 106 (some 132))) = d20 p
  rw [sub439, sub438]
  rfl
theorem sub441 (p : Pattern) : d25 (change p 106 (some 132)) = d25 p := by
  change (if p 139 then d24 (change p 106 (some 132)) else d20 (change p 106 (some 132))) = d25 p
  rw [sub427, sub440]
  rfl
theorem sub442 (p : Pattern) : d26 (change p 106 (some 132)) = d26 p := by
  change (if p 138 then d25 (change p 106 (some 132)) else d20 (change p 106 (some 132))) = d26 p
  rw [sub441, sub440]
  rfl
theorem sub443 (p : Pattern) : d43 (change p 106 (some 132)) = d43 p := by
  change (if p 134 then d26 (change p 106 (some 132)) else d42 (change p 106 (some 132))) = d43 p
  rw [sub442, sub436]
  rfl
theorem sub444 (p : Pattern) : d44 (change p 106 (some 132)) = d44 p := by
  change (if p 133 then d43 (change p 106 (some 132)) else d36 (change p 106 (some 132))) = d44 p
  rw [sub443, sub430]
  rfl
theorem sub445 (p : Pattern) : d45 (change p 106 (some 132)) = d44 p := by
  change d44 (change p 106 (some 132)) = d44 p
  exact sub444 p
theorem sub446 (p : Pattern) : d48 (change p 106 (some 132)) = d48 p := by
  change (if p 134 then d34 (change p 106 (some 132)) else d15 (change p 106 (some 132))) = d48 p
  rw [sub428, sub417]
  rfl
theorem sub447 (p : Pattern) : d49 (change p 106 (some 132)) = d49 p := by
  change (if p 134 then d25 (change p 106 (some 132)) else d41 (change p 106 (some 132))) = d49 p
  rw [sub441, sub435]
  rfl
theorem sub448 (p : Pattern) : d50 (change p 106 (some 132)) = d50 p := by
  change (if p 133 then d49 (change p 106 (some 132)) else d48 (change p 106 (some 132))) = d50 p
  rw [sub447, sub446]
  rfl
theorem sub449 (p : Pattern) : d51 (change p 106 (some 132)) = d50 p := by
  change d50 (change p 106 (some 132)) = d50 p
  exact sub448 p
theorem sub450 (p : Pattern) : d52 (change p 106 (some 132)) = d52 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d8 (change p 106 (some 132))) = d52 p
  rw [sub403, sub409]
  rfl
theorem sub451 (p : Pattern) : d53 (change p 106 (some 132)) = d53 p := by
  change (if p 138 then d52 (change p 106 (some 132)) else d15 (change p 106 (some 132))) = d53 p
  rw [sub450, sub417]
  rfl
theorem sub452 (p : Pattern) : d58 (change p 106 (some 132)) = d58 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d33 (change p 106 (some 132))) = d58 p
  rw [sub403, sub423]
  rfl
theorem sub453 (p : Pattern) : d59 (change p 106 (some 132)) = d59 p := by
  change (if p 138 then d58 (change p 106 (some 132)) else d34 (change p 106 (some 132))) = d59 p
  rw [sub452, sub428]
  rfl
theorem sub454 (p : Pattern) : d60 (change p 106 (some 132)) = d60 p := by
  change (if p 134 then d59 (change p 106 (some 132)) else d53 (change p 106 (some 132))) = d60 p
  rw [sub453, sub451]
  rfl
theorem sub455 (p : Pattern) : d61 (change p 106 (some 132)) = d61 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d38 (change p 106 (some 132))) = d61 p
  rw [sub403, sub432]
  rfl
theorem sub456 (p : Pattern) : d62 (change p 106 (some 132)) = d62 p := by
  change (if p 138 then d61 (change p 106 (some 132)) else d41 (change p 106 (some 132))) = d62 p
  rw [sub455, sub435]
  rfl
theorem sub457 (p : Pattern) : d54 (change p 106 (some 132)) = d54 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d20 (change p 106 (some 132))) = d54 p
  rw [sub403, sub440]
  rfl
theorem sub458 (p : Pattern) : d55 (change p 106 (some 132)) = d55 p := by
  change (if p 138 then d54 (change p 106 (some 132)) else d25 (change p 106 (some 132))) = d55 p
  rw [sub457, sub441]
  rfl
theorem sub459 (p : Pattern) : d63 (change p 106 (some 132)) = d63 p := by
  change (if p 134 then d55 (change p 106 (some 132)) else d62 (change p 106 (some 132))) = d63 p
  rw [sub458, sub456]
  rfl
theorem sub460 (p : Pattern) : d64 (change p 106 (some 132)) = d64 p := by
  change (if p 133 then d63 (change p 106 (some 132)) else d60 (change p 106 (some 132))) = d64 p
  rw [sub459, sub454]
  rfl
theorem sub461 (p : Pattern) : d65 (change p 106 (some 132)) = d64 p := by
  change d64 (change p 106 (some 132)) = d64 p
  exact sub460 p
theorem sub462 (p : Pattern) : d66 (change p 106 (some 132)) = d844 p := by
  change (if p 113 then d65 (change p 106 (some 132)) else d51 (change p 106 (some 132))) = d844 p
  rw [sub461, sub449]
  rfl
theorem sub463 (p : Pattern) : d67 (change p 106 (some 132)) = d845 p := by
  change (if p 112 then d66 (change p 106 (some 132)) else d45 (change p 106 (some 132))) = d845 p
  rw [sub462, sub445]
  rfl
theorem sub464 (p : Pattern) : d177 (change p 106 (some 132)) = d845 p := by
  change d67 (change p 106 (some 132)) = d845 p
  exact sub463 p
theorem sub465 (p : Pattern) : d86 (change p 106 (some 132)) = d86 p := by
  change (if p 138 then d52 (change p 106 (some 132)) else d8 (change p 106 (some 132))) = d86 p
  rw [sub450, sub409]
  rfl
theorem sub466 (p : Pattern) : d90 (change p 106 (some 132)) = d90 p := by
  change (if p 138 then d58 (change p 106 (some 132)) else d33 (change p 106 (some 132))) = d90 p
  rw [sub452, sub423]
  rfl
theorem sub467 (p : Pattern) : d91 (change p 106 (some 132)) = d91 p := by
  change (if p 134 then d90 (change p 106 (some 132)) else d86 (change p 106 (some 132))) = d91 p
  rw [sub466, sub465]
  rfl
theorem sub468 (p : Pattern) : d92 (change p 106 (some 132)) = d92 p := by
  change (if p 138 then d61 (change p 106 (some 132)) else d38 (change p 106 (some 132))) = d92 p
  rw [sub455, sub432]
  rfl
theorem sub469 (p : Pattern) : d87 (change p 106 (some 132)) = d87 p := by
  change (if p 138 then d54 (change p 106 (some 132)) else d20 (change p 106 (some 132))) = d87 p
  rw [sub457, sub440]
  rfl
theorem sub470 (p : Pattern) : d93 (change p 106 (some 132)) = d93 p := by
  change (if p 134 then d87 (change p 106 (some 132)) else d92 (change p 106 (some 132))) = d93 p
  rw [sub469, sub468]
  rfl
theorem sub471 (p : Pattern) : d94 (change p 106 (some 132)) = d94 p := by
  change (if p 133 then d93 (change p 106 (some 132)) else d91 (change p 106 (some 132))) = d94 p
  rw [sub470, sub467]
  rfl
theorem sub472 (p : Pattern) : d95 (change p 106 (some 132)) = d94 p := by
  change d94 (change p 106 (some 132)) = d94 p
  exact sub471 p
theorem sub473 (p : Pattern) : d96 (change p 106 (some 132)) = d846 p := by
  change (if p 113 then d95 (change p 106 (some 132)) else d45 (change p 106 (some 132))) = d846 p
  rw [sub472, sub445]
  rfl
theorem sub474 (p : Pattern) : d97 (change p 106 (some 132)) = d97 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d14 (change p 106 (some 132))) = d97 p
  rw [sub403, sub416]
  rfl
theorem sub475 (p : Pattern) : d98 (change p 106 (some 132)) = d98 p := by
  change (if p 138 then d97 (change p 106 (some 132)) else d14 (change p 106 (some 132))) = d98 p
  rw [sub474, sub416]
  rfl
theorem sub476 (p : Pattern) : d70 (change p 106 (some 132)) = d70 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d24 (change p 106 (some 132))) = d70 p
  rw [sub403, sub427]
  rfl
theorem sub477 (p : Pattern) : d71 (change p 106 (some 132)) = d71 p := by
  change (if p 138 then d70 (change p 106 (some 132)) else d24 (change p 106 (some 132))) = d71 p
  rw [sub476, sub427]
  rfl
theorem sub478 (p : Pattern) : d99 (change p 106 (some 132)) = d99 p := by
  change (if p 134 then d71 (change p 106 (some 132)) else d98 (change p 106 (some 132))) = d99 p
  rw [sub477, sub475]
  rfl
theorem sub479 (p : Pattern) : d68 (change p 106 (some 132)) = d68 p := by
  change (if p 139 then d2 (change p 106 (some 132)) else d40 (change p 106 (some 132))) = d68 p
  rw [sub403, sub434]
  rfl
end NetHack.Sokoban32Refined
