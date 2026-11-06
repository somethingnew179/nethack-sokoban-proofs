/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions44
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5400 (p : Pattern) : d1129 (change p 162 (some 163)) = d1127 p := by
  change d1128 (change p 162 (some 163)) = d1127 p
  exact sub5399 p
theorem sub5401 (p : Pattern) : d1130 (change p 162 (some 163)) = d4720 p := by
  change (if p 161 then d1129 (change p 162 (some 163)) else d1124 (change p 162 (some 163))) = d4720 p
  rw [sub5400, sub5392]
  rfl
theorem sub5402 (p : Pattern) : d1131 (change p 162 (some 163)) = d4721 p := by
  change (if p 160 then d1130 (change p 162 (some 163)) else d1125 (change p 162 (some 163))) = d4721 p
  rw [sub5401, sub5393]
  rfl
theorem sub5403 (p : Pattern) : d1132 (change p 162 (some 163)) = d4722 p := by
  change (if p 141 then d1131 (change p 162 (some 163)) else d1123 (change p 162 (some 163))) = d4722 p
  rw [sub5402, sub5388]
  rfl
theorem sub5404 (p : Pattern) : d1133 (change p 162 (some 163)) = d132 p := by
  change d132 (change p 162 (some 163)) = d132 p
  exact sub5293 p
theorem sub5405 (p : Pattern) : d1134 (change p 162 (some 163)) = d132 p := by
  change d1133 (change p 162 (some 163)) = d132 p
  exact sub5404 p
theorem sub5406 (p : Pattern) : d1135 (change p 162 (some 163)) = d4704 p := by
  change (if p 161 then d1134 (change p 162 (some 163)) else d1089 (change p 162 (some 163))) = d4704 p
  rw [sub5405, sub5348]
  rfl
theorem sub5407 (p : Pattern) : d1136 (change p 162 (some 163)) = d4706 p := by
  change (if p 160 then d1062 (change p 162 (some 163)) else d1135 (change p 162 (some 163))) = d4706 p
  rw [sub5314, sub5406]
  rfl
theorem sub5408 (p : Pattern) : d1137 (change p 162 (some 163)) = d109 p := by
  change d109 (change p 162 (some 163)) = d109 p
  exact sub5316 p
theorem sub5409 (p : Pattern) : d1138 (change p 162 (some 163)) = d109 p := by
  change d1137 (change p 162 (some 163)) = d109 p
  exact sub5408 p
theorem sub5410 (p : Pattern) : d1139 (change p 162 (some 163)) = d4707 p := by
  change (if p 161 then d1138 (change p 162 (some 163)) else d1061 (change p 162 (some 163))) = d4707 p
  rw [sub5409, sub5313]
  rfl
theorem sub5411 (p : Pattern) : d1140 (change p 162 (some 163)) = d109 p := by
  change d109 (change p 162 (some 163)) = d109 p
  exact sub5316 p
theorem sub5412 (p : Pattern) : d1141 (change p 162 (some 163)) = d4708 p := by
  change (if p 161 then d12 (change p 162 (some 163)) else d1140 (change p 162 (some 163))) = d4708 p
  rw [sub5140, sub5411]
  rfl
theorem sub5413 (p : Pattern) : d1142 (change p 162 (some 163)) = d4709 p := by
  change (if p 160 then d1141 (change p 162 (some 163)) else d1139 (change p 162 (some 163))) = d4709 p
  rw [sub5412, sub5410]
  rfl
theorem sub5414 (p : Pattern) : d1143 (change p 162 (some 163)) = d4710 p := by
  change (if p 141 then d1142 (change p 162 (some 163)) else d1136 (change p 162 (some 163))) = d4710 p
  rw [sub5413, sub5407]
  rfl
theorem sub5415 (p : Pattern) : d1144 (change p 162 (some 163)) = d4723 p := by
  change (if p 138 then d1143 (change p 162 (some 163)) else d1132 (change p 162 (some 163))) = d4723 p
  rw [sub5414, sub5403]
  rfl
theorem sub5416 (p : Pattern) : d1145 (change p 162 (some 163)) = d4712 p := by
  change (if p 138 then d12 (change p 162 (some 163)) else d1143 (change p 162 (some 163))) = d4712 p
  rw [sub5140, sub5414]
  rfl
theorem sub5417 (p : Pattern) : d1146 (change p 162 (some 163)) = d4724 p := by
  change (if p 116 then d1145 (change p 162 (some 163)) else d1144 (change p 162 (some 163))) = d4724 p
  rw [sub5416, sub5415]
  rfl
theorem sub5418 (p : Pattern) : d1147 (change p 162 (some 163)) = d4725 p := by
  change (if p 115 then d1146 (change p 162 (some 163)) else d1116 (change p 162 (some 163))) = d4725 p
  rw [sub5417, sub5375]
  rfl
theorem sub5419 (p : Pattern) : d1148 (change p 162 (some 163)) = d4726 p := by
  change (if p 71 then d1147 (change p 162 (some 163)) else d1014 (change p 162 (some 163))) = d4726 p
  rw [sub5418, sub5242]
  rfl
theorem sub5420 (p : Pattern) : d1149 (change p 162 (some 163)) = d4727 p := by
  change (if p 49 then d1148 (change p 162 (some 163)) else d1108 (change p 162 (some 163))) = d4727 p
  rw [sub5419, sub5367]
  rfl
theorem sub5421 (p : Pattern) : d1150 (change p 162 (some 163)) = d4728 p := by
  change (if p 48 then d1149 (change p 162 (some 163)) else d1098 (change p 162 (some 163))) = d4728 p
  rw [sub5420, sub5357]
  rfl
theorem sub5422 (p : Pattern) : d0 (change p 160 none) = d0 p := by
  rfl
theorem sub5423 (p : Pattern) : d12 (change p 160 none) = d12 p := by
  rfl
theorem sub5424 (p : Pattern) : d13 (change p 160 none) = d13 p := by
  change (if p 247 then d12 (change p 160 none) else d0 (change p 160 none)) = d13 p
  rw [sub5423, sub5422]
  rfl
theorem sub5425 (p : Pattern) : d14 (change p 160 none) = d14 p := by
  change (if p 246 then d13 (change p 160 none) else d0 (change p 160 none)) = d14 p
  rw [sub5424, sub5422]
  rfl
theorem sub5426 (p : Pattern) : d15 (change p 160 none) = d15 p := by
  change (if p 204 then d12 (change p 160 none) else d14 (change p 160 none)) = d15 p
  rw [sub5423, sub5425]
  rfl
theorem sub5427 (p : Pattern) : d16 (change p 160 none) = d16 p := by
  change (if p 182 then d15 (change p 160 none) else d14 (change p 160 none)) = d16 p
  rw [sub5426, sub5425]
  rfl
theorem sub5428 (p : Pattern) : d4 (change p 160 none) = d4 p := by
  rfl
theorem sub5429 (p : Pattern) : d17 (change p 160 none) = d17 p := by
  change (if p 247 then d12 (change p 160 none) else d4 (change p 160 none)) = d17 p
  rw [sub5423, sub5428]
  rfl
theorem sub5430 (p : Pattern) : d18 (change p 160 none) = d18 p := by
  change (if p 246 then d17 (change p 160 none) else d4 (change p 160 none)) = d18 p
  rw [sub5429, sub5428]
  rfl
theorem sub5431 (p : Pattern) : d19 (change p 160 none) = d19 p := by
  change (if p 204 then d12 (change p 160 none) else d18 (change p 160 none)) = d19 p
  rw [sub5423, sub5430]
  rfl
theorem sub5432 (p : Pattern) : d20 (change p 160 none) = d20 p := by
  change (if p 182 then d19 (change p 160 none) else d18 (change p 160 none)) = d20 p
  rw [sub5431, sub5430]
  rfl
theorem sub5433 (p : Pattern) : d21 (change p 160 none) = d21 p := by
  change (if p 163 then d20 (change p 160 none) else d16 (change p 160 none)) = d21 p
  rw [sub5432, sub5427]
  rfl
theorem sub5434 (p : Pattern) : d22 (change p 160 none) = d22 p := by
  change (if p 162 then d21 (change p 160 none) else d16 (change p 160 none)) = d22 p
  rw [sub5433, sub5427]
  rfl
theorem sub5435 (p : Pattern) : d9 (change p 160 none) = d9 p := by
  rfl
theorem sub5436 (p : Pattern) : d23 (change p 160 none) = d23 p := by
  change (if p 247 then d12 (change p 160 none) else d9 (change p 160 none)) = d23 p
  rw [sub5423, sub5435]
  rfl
theorem sub5437 (p : Pattern) : d24 (change p 160 none) = d24 p := by
  change (if p 246 then d23 (change p 160 none) else d9 (change p 160 none)) = d24 p
  rw [sub5436, sub5435]
  rfl
theorem sub5438 (p : Pattern) : d25 (change p 160 none) = d25 p := by
  change (if p 204 then d12 (change p 160 none) else d24 (change p 160 none)) = d25 p
  rw [sub5423, sub5437]
  rfl
theorem sub5439 (p : Pattern) : d26 (change p 160 none) = d26 p := by
  change (if p 182 then d25 (change p 160 none) else d24 (change p 160 none)) = d26 p
  rw [sub5438, sub5437]
  rfl
theorem sub5440 (p : Pattern) : d27 (change p 160 none) = d27 p := by
  change (if p 163 then d12 (change p 160 none) else d26 (change p 160 none)) = d27 p
  rw [sub5423, sub5439]
  rfl
theorem sub5441 (p : Pattern) : d28 (change p 160 none) = d28 p := by
  change (if p 162 then d27 (change p 160 none) else d21 (change p 160 none)) = d28 p
  rw [sub5440, sub5433]
  rfl
theorem sub5442 (p : Pattern) : d29 (change p 160 none) = d29 p := by
  change (if p 161 then d28 (change p 160 none) else d22 (change p 160 none)) = d29 p
  rw [sub5441, sub5434]
  rfl
theorem sub5443 (p : Pattern) : d710 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5444 (p : Pattern) : d2 (change p 160 none) = d2 p := by
  rfl
theorem sub5445 (p : Pattern) : d30 (change p 160 none) = d30 p := by
  change (if p 247 then d12 (change p 160 none) else d2 (change p 160 none)) = d30 p
  rw [sub5423, sub5444]
  rfl
theorem sub5446 (p : Pattern) : d31 (change p 160 none) = d31 p := by
  change (if p 246 then d30 (change p 160 none) else d2 (change p 160 none)) = d31 p
  rw [sub5445, sub5444]
  rfl
theorem sub5447 (p : Pattern) : d32 (change p 160 none) = d32 p := by
  change (if p 204 then d12 (change p 160 none) else d31 (change p 160 none)) = d32 p
  rw [sub5423, sub5446]
  rfl
theorem sub5448 (p : Pattern) : d53 (change p 160 none) = d53 p := by
  change (if p 182 then d32 (change p 160 none) else d31 (change p 160 none)) = d53 p
  rw [sub5447, sub5446]
  rfl
theorem sub5449 (p : Pattern) : d54 (change p 160 none) = d54 p := by
  change (if p 163 then d53 (change p 160 none) else d16 (change p 160 none)) = d54 p
  rw [sub5448, sub5427]
  rfl
theorem sub5450 (p : Pattern) : d55 (change p 160 none) = d55 p := by
  change (if p 163 then d26 (change p 160 none) else d20 (change p 160 none)) = d55 p
  rw [sub5439, sub5432]
  rfl
theorem sub5451 (p : Pattern) : d56 (change p 160 none) = d56 p := by
  change (if p 162 then d55 (change p 160 none) else d54 (change p 160 none)) = d56 p
  rw [sub5450, sub5449]
  rfl
theorem sub5452 (p : Pattern) : d10 (change p 160 none) = d10 p := by
  rfl
theorem sub5453 (p : Pattern) : d57 (change p 160 none) = d57 p := by
  change (if p 247 then d12 (change p 160 none) else d10 (change p 160 none)) = d57 p
  rw [sub5423, sub5452]
  rfl
theorem sub5454 (p : Pattern) : d58 (change p 160 none) = d58 p := by
  change (if p 246 then d57 (change p 160 none) else d10 (change p 160 none)) = d58 p
  rw [sub5453, sub5452]
  rfl
theorem sub5455 (p : Pattern) : d59 (change p 160 none) = d59 p := by
  change (if p 204 then d12 (change p 160 none) else d58 (change p 160 none)) = d59 p
  rw [sub5423, sub5454]
  rfl
theorem sub5456 (p : Pattern) : d60 (change p 160 none) = d60 p := by
  change (if p 182 then d59 (change p 160 none) else d58 (change p 160 none)) = d60 p
  rw [sub5455, sub5454]
  rfl
theorem sub5457 (p : Pattern) : d61 (change p 160 none) = d61 p := by
  change (if p 163 then d60 (change p 160 none) else d20 (change p 160 none)) = d61 p
  rw [sub5456, sub5432]
  rfl
theorem sub5458 (p : Pattern) : d11 (change p 160 none) = d11 p := by
  rfl
theorem sub5459 (p : Pattern) : d39 (change p 160 none) = d39 p := by
  change (if p 247 then d12 (change p 160 none) else d11 (change p 160 none)) = d39 p
  rw [sub5423, sub5458]
  rfl
theorem sub5460 (p : Pattern) : d40 (change p 160 none) = d40 p := by
  change (if p 246 then d39 (change p 160 none) else d11 (change p 160 none)) = d40 p
  rw [sub5459, sub5458]
  rfl
theorem sub5461 (p : Pattern) : d41 (change p 160 none) = d41 p := by
  change (if p 204 then d12 (change p 160 none) else d40 (change p 160 none)) = d41 p
  rw [sub5423, sub5460]
  rfl
theorem sub5462 (p : Pattern) : d62 (change p 160 none) = d62 p := by
  change (if p 182 then d41 (change p 160 none) else d40 (change p 160 none)) = d62 p
  rw [sub5461, sub5460]
  rfl
theorem sub5463 (p : Pattern) : d63 (change p 160 none) = d63 p := by
  change (if p 163 then d12 (change p 160 none) else d62 (change p 160 none)) = d63 p
  rw [sub5423, sub5462]
  rfl
theorem sub5464 (p : Pattern) : d64 (change p 160 none) = d64 p := by
  change (if p 162 then d63 (change p 160 none) else d61 (change p 160 none)) = d64 p
  rw [sub5463, sub5457]
  rfl
theorem sub5465 (p : Pattern) : d65 (change p 160 none) = d65 p := by
  change (if p 161 then d64 (change p 160 none) else d56 (change p 160 none)) = d65 p
  rw [sub5464, sub5451]
  rfl
theorem sub5466 (p : Pattern) : d711 (change p 160 none) = d65 p := by
  change d65 (change p 160 none) = d65 p
  exact sub5465 p
theorem sub5467 (p : Pattern) : d712 (change p 160 none) = d4729 p := by
  change (if p 141 then d711 (change p 160 none) else d710 (change p 160 none)) = d4729 p
  rw [sub5466, sub5443]
  rfl
theorem sub5468 (p : Pattern) : d713 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5469 (p : Pattern) : d714 (change p 160 none) = d65 p := by
  change d65 (change p 160 none) = d65 p
  exact sub5465 p
theorem sub5470 (p : Pattern) : d715 (change p 160 none) = d4729 p := by
  change (if p 141 then d714 (change p 160 none) else d713 (change p 160 none)) = d4729 p
  rw [sub5469, sub5468]
  rfl
theorem sub5471 (p : Pattern) : d716 (change p 160 none) = d4729 p := by
  change (if p 138 then d715 (change p 160 none) else d712 (change p 160 none)) = d4729 p
  rw [sub5470, sub5467]
  simp only [ite_self]
theorem sub5472 (p : Pattern) : d717 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5473 (p : Pattern) : d718 (change p 160 none) = d4729 p := by
  change (if p 141 then d714 (change p 160 none) else d717 (change p 160 none)) = d4729 p
  rw [sub5469, sub5472]
  rfl
theorem sub5474 (p : Pattern) : d89 (change p 160 none) = d89 p := by
  change (if p 163 then d62 (change p 160 none) else d26 (change p 160 none)) = d89 p
  rw [sub5462, sub5439]
  rfl
theorem sub5475 (p : Pattern) : d90 (change p 160 none) = d90 p := by
  change (if p 162 then d63 (change p 160 none) else d89 (change p 160 none)) = d90 p
  rw [sub5463, sub5474]
  rfl
theorem sub5476 (p : Pattern) : d91 (change p 160 none) = d91 p := by
  change (if p 162 then d12 (change p 160 none) else d63 (change p 160 none)) = d91 p
  rw [sub5423, sub5463]
  rfl
theorem sub5477 (p : Pattern) : d92 (change p 160 none) = d92 p := by
  change (if p 161 then d91 (change p 160 none) else d90 (change p 160 none)) = d92 p
  rw [sub5476, sub5475]
  rfl
theorem sub5478 (p : Pattern) : d719 (change p 160 none) = d92 p := by
  change d92 (change p 160 none) = d92 p
  exact sub5477 p
theorem sub5479 (p : Pattern) : d93 (change p 160 none) = d93 p := by
  change (if p 161 then d12 (change p 160 none) else d91 (change p 160 none)) = d93 p
  rw [sub5423, sub5476]
  rfl
theorem sub5480 (p : Pattern) : d95 (change p 160 none) = d93 p := by
  change d93 (change p 160 none) = d93 p
  exact sub5479 p
theorem sub5481 (p : Pattern) : d720 (change p 160 none) = d4730 p := by
  change (if p 141 then d95 (change p 160 none) else d719 (change p 160 none)) = d4730 p
  rw [sub5480, sub5478]
  rfl
theorem sub5482 (p : Pattern) : d721 (change p 160 none) = d4731 p := by
  change (if p 138 then d720 (change p 160 none) else d718 (change p 160 none)) = d4731 p
  rw [sub5481, sub5473]
  rfl
theorem sub5483 (p : Pattern) : d722 (change p 160 none) = d4732 p := by
  change (if p 116 then d721 (change p 160 none) else d716 (change p 160 none)) = d4732 p
  rw [sub5482, sub5471]
  rfl
theorem sub5484 (p : Pattern) : d723 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5485 (p : Pattern) : d724 (change p 160 none) = d65 p := by
  change d65 (change p 160 none) = d65 p
  exact sub5465 p
theorem sub5486 (p : Pattern) : d725 (change p 160 none) = d4729 p := by
  change (if p 141 then d724 (change p 160 none) else d723 (change p 160 none)) = d4729 p
  rw [sub5485, sub5484]
  rfl
theorem sub5487 (p : Pattern) : d726 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5488 (p : Pattern) : d727 (change p 160 none) = d4729 p := by
  change (if p 141 then d714 (change p 160 none) else d726 (change p 160 none)) = d4729 p
  rw [sub5469, sub5487]
  rfl
theorem sub5489 (p : Pattern) : d728 (change p 160 none) = d4729 p := by
  change (if p 138 then d727 (change p 160 none) else d725 (change p 160 none)) = d4729 p
  rw [sub5488, sub5486]
  simp only [ite_self]
theorem sub5490 (p : Pattern) : d729 (change p 160 none) = d4733 p := by
  change (if p 138 then d12 (change p 160 none) else d727 (change p 160 none)) = d4733 p
  rw [sub5423, sub5488]
  rfl
theorem sub5491 (p : Pattern) : d730 (change p 160 none) = d4734 p := by
  change (if p 116 then d729 (change p 160 none) else d728 (change p 160 none)) = d4734 p
  rw [sub5490, sub5489]
  rfl
theorem sub5492 (p : Pattern) : d731 (change p 160 none) = d4735 p := by
  change (if p 115 then d730 (change p 160 none) else d722 (change p 160 none)) = d4735 p
  rw [sub5491, sub5483]
  rfl
theorem sub5493 (p : Pattern) : d732 (change p 160 none) = d29 p := by
  change d29 (change p 160 none) = d29 p
  exact sub5442 p
theorem sub5494 (p : Pattern) : d733 (change p 160 none) = d65 p := by
  change d65 (change p 160 none) = d65 p
  exact sub5465 p
theorem sub5495 (p : Pattern) : d734 (change p 160 none) = d4729 p := by
  change (if p 141 then d733 (change p 160 none) else d732 (change p 160 none)) = d4729 p
  rw [sub5494, sub5493]
  rfl
theorem sub5496 (p : Pattern) : d735 (change p 160 none) = d4729 p := by
  change (if p 138 then d727 (change p 160 none) else d734 (change p 160 none)) = d4729 p
  rw [sub5488, sub5495]
  simp only [ite_self]
theorem sub5497 (p : Pattern) : d736 (change p 160 none) = d4731 p := by
  change (if p 138 then d720 (change p 160 none) else d715 (change p 160 none)) = d4731 p
  rw [sub5481, sub5470]
  rfl
theorem sub5498 (p : Pattern) : d737 (change p 160 none) = d4732 p := by
  change (if p 116 then d736 (change p 160 none) else d735 (change p 160 none)) = d4732 p
  rw [sub5497, sub5496]
  rfl
theorem sub5499 (p : Pattern) : d738 (change p 160 none) = d4729 p := by
  change (if p 138 then d727 (change p 160 none) else d718 (change p 160 none)) = d4729 p
  rw [sub5488, sub5473]
  simp only [ite_self]
theorem sub5500 (p : Pattern) : d739 (change p 160 none) = d4734 p := by
  change (if p 116 then d729 (change p 160 none) else d738 (change p 160 none)) = d4734 p
  rw [sub5490, sub5499]
  rfl
theorem sub5501 (p : Pattern) : d740 (change p 160 none) = d4735 p := by
  change (if p 115 then d739 (change p 160 none) else d737 (change p 160 none)) = d4735 p
  rw [sub5500, sub5498]
  rfl
theorem sub5502 (p : Pattern) : d741 (change p 160 none) = d4735 p := by
  change (if p 71 then d740 (change p 160 none) else d731 (change p 160 none)) = d4735 p
  rw [sub5501, sub5492]
  simp only [ite_self]
theorem sub5503 (p : Pattern) : d1 (change p 160 none) = d1 p := by
  rfl
theorem sub5504 (p : Pattern) : d102 (change p 160 none) = d102 p := by
  change (if p 247 then d12 (change p 160 none) else d1 (change p 160 none)) = d102 p
  rw [sub5423, sub5503]
  rfl
theorem sub5505 (p : Pattern) : d103 (change p 160 none) = d103 p := by
  change (if p 246 then d102 (change p 160 none) else d1 (change p 160 none)) = d103 p
  rw [sub5504, sub5503]
  rfl
theorem sub5506 (p : Pattern) : d104 (change p 160 none) = d104 p := by
  change (if p 204 then d12 (change p 160 none) else d103 (change p 160 none)) = d104 p
  rw [sub5423, sub5505]
  rfl
theorem sub5507 (p : Pattern) : d105 (change p 160 none) = d105 p := by
  change (if p 182 then d104 (change p 160 none) else d103 (change p 160 none)) = d105 p
  rw [sub5506, sub5505]
  rfl
theorem sub5508 (p : Pattern) : d5 (change p 160 none) = d5 p := by
  rfl
theorem sub5509 (p : Pattern) : d106 (change p 160 none) = d106 p := by
  change (if p 247 then d12 (change p 160 none) else d5 (change p 160 none)) = d106 p
  rw [sub5423, sub5508]
  rfl
theorem sub5510 (p : Pattern) : d107 (change p 160 none) = d107 p := by
  change (if p 246 then d106 (change p 160 none) else d5 (change p 160 none)) = d107 p
  rw [sub5509, sub5508]
  rfl
theorem sub5511 (p : Pattern) : d108 (change p 160 none) = d108 p := by
  change (if p 204 then d12 (change p 160 none) else d107 (change p 160 none)) = d108 p
  rw [sub5423, sub5510]
  rfl
theorem sub5512 (p : Pattern) : d109 (change p 160 none) = d109 p := by
  change (if p 182 then d108 (change p 160 none) else d107 (change p 160 none)) = d109 p
  rw [sub5511, sub5510]
  rfl
theorem sub5513 (p : Pattern) : d110 (change p 160 none) = d110 p := by
  change (if p 163 then d109 (change p 160 none) else d105 (change p 160 none)) = d110 p
  rw [sub5512, sub5507]
  rfl
theorem sub5514 (p : Pattern) : d111 (change p 160 none) = d111 p := by
  change (if p 162 then d110 (change p 160 none) else d105 (change p 160 none)) = d111 p
  rw [sub5513, sub5507]
  rfl
theorem sub5515 (p : Pattern) : d112 (change p 160 none) = d112 p := by
  change (if p 163 then d12 (change p 160 none) else d60 (change p 160 none)) = d112 p
  rw [sub5423, sub5456]
  rfl
theorem sub5516 (p : Pattern) : d113 (change p 160 none) = d113 p := by
  change (if p 162 then d112 (change p 160 none) else d110 (change p 160 none)) = d113 p
  rw [sub5515, sub5513]
  rfl
theorem sub5517 (p : Pattern) : d114 (change p 160 none) = d114 p := by
  change (if p 161 then d113 (change p 160 none) else d111 (change p 160 none)) = d114 p
  rw [sub5516, sub5514]
  rfl
theorem sub5518 (p : Pattern) : d742 (change p 160 none) = d114 p := by
  change d114 (change p 160 none) = d114 p
  exact sub5517 p
theorem sub5519 (p : Pattern) : d3 (change p 160 none) = d3 p := by
  rfl
end NetHack.Sokoban22Refined85
