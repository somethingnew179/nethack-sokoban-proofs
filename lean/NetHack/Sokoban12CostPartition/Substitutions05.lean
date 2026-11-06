/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub600 (p : Pattern) : d73 (change p 134 none) = d812 p := by
  change (if p 133 then d66 (change p 134 none) else d71 (change p 134 none)) = d812 p
  rw [sub599, sub597]
  rfl
theorem sub601 (p : Pattern) : d74 (change p 134 none) = d813 p := by
  change (if p 132 then d73 (change p 134 none) else d72 (change p 134 none)) = d813 p
  rw [sub600, sub598]
  rfl
theorem sub602 (p : Pattern) : d0 (change p 132 none) = d0 p := by
  rfl
theorem sub603 (p : Pattern) : d2 (change p 132 none) = d2 p := by
  rfl
theorem sub604 (p : Pattern) : d6 (change p 132 none) = d6 p := by
  change (if p 193 then d2 (change p 132 none) else d0 (change p 132 none)) = d6 p
  rw [sub603, sub602]
  rfl
theorem sub605 (p : Pattern) : d7 (change p 132 none) = d7 p := by
  change (if p 192 then d6 (change p 132 none) else d0 (change p 132 none)) = d7 p
  rw [sub604, sub602]
  rfl
theorem sub606 (p : Pattern) : d4 (change p 132 none) = d4 p := by
  rfl
theorem sub607 (p : Pattern) : d54 (change p 132 none) = d54 p := by
  change (if p 193 then d4 (change p 132 none) else d2 (change p 132 none)) = d54 p
  rw [sub606, sub603]
  rfl
theorem sub608 (p : Pattern) : d55 (change p 132 none) = d55 p := by
  change (if p 192 then d54 (change p 132 none) else d2 (change p 132 none)) = d55 p
  rw [sub607, sub603]
  rfl
theorem sub609 (p : Pattern) : d56 (change p 132 none) = d56 p := by
  change (if p 186 then d55 (change p 132 none) else d7 (change p 132 none)) = d56 p
  rw [sub608, sub605]
  rfl
theorem sub610 (p : Pattern) : d57 (change p 132 none) = d57 p := by
  change (if p 160 then d56 (change p 132 none) else d7 (change p 132 none)) = d57 p
  rw [sub609, sub605]
  rfl
theorem sub611 (p : Pattern) : d1 (change p 132 none) = d1 p := by
  rfl
theorem sub612 (p : Pattern) : d8 (change p 132 none) = d8 p := by
  change (if p 271 then d1 (change p 132 none) else d0 (change p 132 none)) = d8 p
  rw [sub611, sub602]
  rfl
theorem sub613 (p : Pattern) : d3 (change p 132 none) = d3 p := by
  rfl
theorem sub614 (p : Pattern) : d9 (change p 132 none) = d9 p := by
  change (if p 271 then d3 (change p 132 none) else d2 (change p 132 none)) = d9 p
  rw [sub613, sub603]
  rfl
theorem sub615 (p : Pattern) : d10 (change p 132 none) = d10 p := by
  change (if p 193 then d9 (change p 132 none) else d8 (change p 132 none)) = d10 p
  rw [sub614, sub612]
  rfl
theorem sub616 (p : Pattern) : d11 (change p 132 none) = d11 p := by
  change (if p 192 then d10 (change p 132 none) else d8 (change p 132 none)) = d11 p
  rw [sub615, sub612]
  rfl
theorem sub617 (p : Pattern) : d12 (change p 132 none) = d12 p := by
  change (if p 168 then d11 (change p 132 none) else d7 (change p 132 none)) = d12 p
  rw [sub616, sub605]
  rfl
theorem sub618 (p : Pattern) : d5 (change p 132 none) = d5 p := by
  rfl
theorem sub619 (p : Pattern) : d58 (change p 132 none) = d58 p := by
  change (if p 271 then d5 (change p 132 none) else d4 (change p 132 none)) = d58 p
  rw [sub618, sub606]
  rfl
theorem sub620 (p : Pattern) : d59 (change p 132 none) = d59 p := by
  change (if p 193 then d58 (change p 132 none) else d9 (change p 132 none)) = d59 p
  rw [sub619, sub614]
  rfl
theorem sub621 (p : Pattern) : d60 (change p 132 none) = d60 p := by
  change (if p 192 then d59 (change p 132 none) else d9 (change p 132 none)) = d60 p
  rw [sub620, sub614]
  rfl
theorem sub622 (p : Pattern) : d61 (change p 132 none) = d61 p := by
  change (if p 186 then d60 (change p 132 none) else d11 (change p 132 none)) = d61 p
  rw [sub621, sub616]
  rfl
theorem sub623 (p : Pattern) : d62 (change p 132 none) = d62 p := by
  change (if p 168 then d61 (change p 132 none) else d56 (change p 132 none)) = d62 p
  rw [sub622, sub609]
  rfl
theorem sub624 (p : Pattern) : d63 (change p 132 none) = d63 p := by
  change (if p 160 then d62 (change p 132 none) else d12 (change p 132 none)) = d63 p
  rw [sub623, sub617]
  rfl
theorem sub625 (p : Pattern) : d64 (change p 132 none) = d64 p := by
  change (if p 141 then d63 (change p 132 none) else d57 (change p 132 none)) = d64 p
  rw [sub624, sub610]
  rfl
theorem sub626 (p : Pattern) : d106 (change p 132 none) = d106 p := by
  change (if p 160 then d55 (change p 132 none) else d7 (change p 132 none)) = d106 p
  rw [sub608, sub605]
  rfl
theorem sub627 (p : Pattern) : d107 (change p 132 none) = d107 p := by
  change (if p 159 then d55 (change p 132 none) else d106 (change p 132 none)) = d107 p
  rw [sub608, sub626]
  rfl
theorem sub628 (p : Pattern) : d108 (change p 132 none) = d108 p := by
  change (if p 158 then d107 (change p 132 none) else d106 (change p 132 none)) = d108 p
  rw [sub627, sub626]
  rfl
theorem sub629 (p : Pattern) : d65 (change p 132 none) = d65 p := by
  change (if p 168 then d60 (change p 132 none) else d55 (change p 132 none)) = d65 p
  rw [sub621, sub608]
  rfl
theorem sub630 (p : Pattern) : d109 (change p 132 none) = d109 p := by
  change (if p 160 then d65 (change p 132 none) else d12 (change p 132 none)) = d109 p
  rw [sub629, sub617]
  rfl
theorem sub631 (p : Pattern) : d110 (change p 132 none) = d110 p := by
  change (if p 159 then d65 (change p 132 none) else d109 (change p 132 none)) = d110 p
  rw [sub629, sub630]
  rfl
theorem sub632 (p : Pattern) : d111 (change p 132 none) = d111 p := by
  change (if p 158 then d110 (change p 132 none) else d109 (change p 132 none)) = d111 p
  rw [sub631, sub630]
  rfl
theorem sub633 (p : Pattern) : d112 (change p 132 none) = d112 p := by
  change (if p 141 then d111 (change p 132 none) else d108 (change p 132 none)) = d112 p
  rw [sub632, sub628]
  rfl
theorem sub634 (p : Pattern) : d113 (change p 132 none) = d113 p := by
  change (if p 134 then d112 (change p 132 none) else d64 (change p 132 none)) = d113 p
  rw [sub633, sub625]
  rfl
theorem sub635 (p : Pattern) : d114 (change p 132 none) = d114 p := by
  change (if p 159 then d55 (change p 132 none) else d57 (change p 132 none)) = d114 p
  rw [sub608, sub610]
  rfl
theorem sub636 (p : Pattern) : d115 (change p 132 none) = d115 p := by
  change (if p 158 then d114 (change p 132 none) else d57 (change p 132 none)) = d115 p
  rw [sub635, sub610]
  rfl
theorem sub637 (p : Pattern) : d116 (change p 132 none) = d116 p := by
  change (if p 159 then d65 (change p 132 none) else d63 (change p 132 none)) = d116 p
  rw [sub629, sub624]
  rfl
theorem sub638 (p : Pattern) : d117 (change p 132 none) = d117 p := by
  change (if p 158 then d116 (change p 132 none) else d63 (change p 132 none)) = d117 p
  rw [sub637, sub624]
  rfl
theorem sub639 (p : Pattern) : d118 (change p 132 none) = d118 p := by
  change (if p 141 then d117 (change p 132 none) else d115 (change p 132 none)) = d118 p
  rw [sub638, sub636]
  rfl
theorem sub640 (p : Pattern) : d119 (change p 132 none) = d119 p := by
  change (if p 187 then d55 (change p 132 none) else d7 (change p 132 none)) = d119 p
  rw [sub608, sub605]
  rfl
theorem sub641 (p : Pattern) : d120 (change p 132 none) = d120 p := by
  change (if p 186 then d119 (change p 132 none) else d7 (change p 132 none)) = d120 p
  rw [sub640, sub605]
  rfl
theorem sub642 (p : Pattern) : d121 (change p 132 none) = d121 p := by
  change (if p 160 then d55 (change p 132 none) else d120 (change p 132 none)) = d121 p
  rw [sub608, sub641]
  rfl
theorem sub643 (p : Pattern) : d122 (change p 132 none) = d122 p := by
  change (if p 159 then d121 (change p 132 none) else d106 (change p 132 none)) = d122 p
  rw [sub642, sub626]
  rfl
theorem sub644 (p : Pattern) : d123 (change p 132 none) = d123 p := by
  change (if p 159 then d55 (change p 132 none) else d121 (change p 132 none)) = d123 p
  rw [sub608, sub642]
  rfl
theorem sub645 (p : Pattern) : d124 (change p 132 none) = d124 p := by
  change (if p 158 then d123 (change p 132 none) else d122 (change p 132 none)) = d124 p
  rw [sub644, sub643]
  rfl
theorem sub646 (p : Pattern) : d125 (change p 132 none) = d125 p := by
  change (if p 187 then d60 (change p 132 none) else d11 (change p 132 none)) = d125 p
  rw [sub621, sub616]
  rfl
theorem sub647 (p : Pattern) : d126 (change p 132 none) = d126 p := by
  change (if p 186 then d125 (change p 132 none) else d11 (change p 132 none)) = d126 p
  rw [sub646, sub616]
  rfl
theorem sub648 (p : Pattern) : d127 (change p 132 none) = d127 p := by
  change (if p 168 then d126 (change p 132 none) else d120 (change p 132 none)) = d127 p
  rw [sub647, sub641]
  rfl
theorem sub649 (p : Pattern) : d128 (change p 132 none) = d128 p := by
  change (if p 160 then d65 (change p 132 none) else d127 (change p 132 none)) = d128 p
  rw [sub629, sub648]
  rfl
theorem sub650 (p : Pattern) : d129 (change p 132 none) = d129 p := by
  change (if p 159 then d128 (change p 132 none) else d109 (change p 132 none)) = d129 p
  rw [sub649, sub630]
  rfl
theorem sub651 (p : Pattern) : d130 (change p 132 none) = d130 p := by
  change (if p 159 then d65 (change p 132 none) else d128 (change p 132 none)) = d130 p
  rw [sub629, sub649]
  rfl
theorem sub652 (p : Pattern) : d131 (change p 132 none) = d131 p := by
  change (if p 158 then d130 (change p 132 none) else d129 (change p 132 none)) = d131 p
  rw [sub651, sub650]
  rfl
theorem sub653 (p : Pattern) : d132 (change p 132 none) = d132 p := by
  change (if p 141 then d131 (change p 132 none) else d124 (change p 132 none)) = d132 p
  rw [sub652, sub645]
  rfl
theorem sub654 (p : Pattern) : d133 (change p 132 none) = d133 p := by
  change (if p 134 then d132 (change p 132 none) else d118 (change p 132 none)) = d133 p
  rw [sub653, sub639]
  rfl
theorem sub655 (p : Pattern) : d134 (change p 132 none) = d134 p := by
  change (if p 133 then d133 (change p 132 none) else d113 (change p 132 none)) = d134 p
  rw [sub654, sub634]
  rfl
theorem sub656 (p : Pattern) : d199 (change p 132 none) = d134 p := by
  change d134 (change p 132 none) = d134 p
  exact sub655 p
theorem sub657 (p : Pattern) : d66 (change p 132 none) = d66 p := by
  change (if p 141 then d65 (change p 132 none) else d55 (change p 132 none)) = d66 p
  rw [sub629, sub608]
  rfl
theorem sub658 (p : Pattern) : d67 (change p 132 none) = d67 p := by
  change (if p 134 then d66 (change p 132 none) else d64 (change p 132 none)) = d67 p
  rw [sub657, sub625]
  rfl
theorem sub659 (p : Pattern) : d137 (change p 132 none) = d137 p := by
  change (if p 186 then d55 (change p 132 none) else d119 (change p 132 none)) = d137 p
  rw [sub608, sub640]
  rfl
theorem sub660 (p : Pattern) : d138 (change p 132 none) = d138 p := by
  change (if p 160 then d137 (change p 132 none) else d7 (change p 132 none)) = d138 p
  rw [sub659, sub605]
  rfl
theorem sub661 (p : Pattern) : d139 (change p 132 none) = d139 p := by
  change (if p 160 then d137 (change p 132 none) else d120 (change p 132 none)) = d139 p
  rw [sub659, sub641]
  rfl
theorem sub662 (p : Pattern) : d140 (change p 132 none) = d140 p := by
  change (if p 159 then d139 (change p 132 none) else d138 (change p 132 none)) = d140 p
  rw [sub661, sub660]
  rfl
theorem sub663 (p : Pattern) : d141 (change p 132 none) = d141 p := by
  change (if p 159 then d55 (change p 132 none) else d139 (change p 132 none)) = d141 p
  rw [sub608, sub661]
  rfl
theorem sub664 (p : Pattern) : d142 (change p 132 none) = d142 p := by
  change (if p 158 then d141 (change p 132 none) else d140 (change p 132 none)) = d142 p
  rw [sub663, sub662]
  rfl
theorem sub665 (p : Pattern) : d143 (change p 132 none) = d143 p := by
  change (if p 186 then d60 (change p 132 none) else d125 (change p 132 none)) = d143 p
  rw [sub621, sub646]
  rfl
theorem sub666 (p : Pattern) : d144 (change p 132 none) = d144 p := by
  change (if p 168 then d143 (change p 132 none) else d137 (change p 132 none)) = d144 p
  rw [sub665, sub659]
  rfl
theorem sub667 (p : Pattern) : d145 (change p 132 none) = d145 p := by
  change (if p 160 then d144 (change p 132 none) else d12 (change p 132 none)) = d145 p
  rw [sub666, sub617]
  rfl
theorem sub668 (p : Pattern) : d146 (change p 132 none) = d146 p := by
  change (if p 160 then d144 (change p 132 none) else d127 (change p 132 none)) = d146 p
  rw [sub666, sub648]
  rfl
theorem sub669 (p : Pattern) : d147 (change p 132 none) = d147 p := by
  change (if p 159 then d146 (change p 132 none) else d145 (change p 132 none)) = d147 p
  rw [sub668, sub667]
  rfl
theorem sub670 (p : Pattern) : d148 (change p 132 none) = d148 p := by
  change (if p 159 then d65 (change p 132 none) else d146 (change p 132 none)) = d148 p
  rw [sub629, sub668]
  rfl
theorem sub671 (p : Pattern) : d149 (change p 132 none) = d149 p := by
  change (if p 158 then d148 (change p 132 none) else d147 (change p 132 none)) = d149 p
  rw [sub670, sub669]
  rfl
theorem sub672 (p : Pattern) : d150 (change p 132 none) = d150 p := by
  change (if p 141 then d149 (change p 132 none) else d142 (change p 132 none)) = d150 p
  rw [sub671, sub664]
  rfl
theorem sub673 (p : Pattern) : d151 (change p 132 none) = d151 p := by
  change (if p 134 then d66 (change p 132 none) else d150 (change p 132 none)) = d151 p
  rw [sub657, sub672]
  rfl
theorem sub674 (p : Pattern) : d152 (change p 132 none) = d152 p := by
  change (if p 133 then d151 (change p 132 none) else d67 (change p 132 none)) = d152 p
  rw [sub673, sub658]
  rfl
theorem sub675 (p : Pattern) : d200 (change p 132 none) = d152 p := by
  change d152 (change p 132 none) = d152 p
  exact sub674 p
theorem sub676 (p : Pattern) : d201 (change p 132 none) = d814 p := by
  change (if p 108 then d200 (change p 132 none) else d199 (change p 132 none)) = d814 p
  rw [sub675, sub656]
  rfl
theorem sub677 (p : Pattern) : d0 (change p 108 none) = d0 p := by
  rfl
theorem sub678 (p : Pattern) : d2 (change p 108 none) = d2 p := by
  rfl
theorem sub679 (p : Pattern) : d6 (change p 108 none) = d6 p := by
  change (if p 193 then d2 (change p 108 none) else d0 (change p 108 none)) = d6 p
  rw [sub678, sub677]
  rfl
theorem sub680 (p : Pattern) : d7 (change p 108 none) = d7 p := by
  change (if p 192 then d6 (change p 108 none) else d0 (change p 108 none)) = d7 p
  rw [sub679, sub677]
  rfl
theorem sub681 (p : Pattern) : d4 (change p 108 none) = d4 p := by
  rfl
theorem sub682 (p : Pattern) : d54 (change p 108 none) = d54 p := by
  change (if p 193 then d4 (change p 108 none) else d2 (change p 108 none)) = d54 p
  rw [sub681, sub678]
  rfl
theorem sub683 (p : Pattern) : d55 (change p 108 none) = d55 p := by
  change (if p 192 then d54 (change p 108 none) else d2 (change p 108 none)) = d55 p
  rw [sub682, sub678]
  rfl
theorem sub684 (p : Pattern) : d56 (change p 108 none) = d56 p := by
  change (if p 186 then d55 (change p 108 none) else d7 (change p 108 none)) = d56 p
  rw [sub683, sub680]
  rfl
theorem sub685 (p : Pattern) : d57 (change p 108 none) = d57 p := by
  change (if p 160 then d56 (change p 108 none) else d7 (change p 108 none)) = d57 p
  rw [sub684, sub680]
  rfl
theorem sub686 (p : Pattern) : d1 (change p 108 none) = d1 p := by
  rfl
theorem sub687 (p : Pattern) : d8 (change p 108 none) = d8 p := by
  change (if p 271 then d1 (change p 108 none) else d0 (change p 108 none)) = d8 p
  rw [sub686, sub677]
  rfl
theorem sub688 (p : Pattern) : d3 (change p 108 none) = d3 p := by
  rfl
theorem sub689 (p : Pattern) : d9 (change p 108 none) = d9 p := by
  change (if p 271 then d3 (change p 108 none) else d2 (change p 108 none)) = d9 p
  rw [sub688, sub678]
  rfl
theorem sub690 (p : Pattern) : d10 (change p 108 none) = d10 p := by
  change (if p 193 then d9 (change p 108 none) else d8 (change p 108 none)) = d10 p
  rw [sub689, sub687]
  rfl
theorem sub691 (p : Pattern) : d11 (change p 108 none) = d11 p := by
  change (if p 192 then d10 (change p 108 none) else d8 (change p 108 none)) = d11 p
  rw [sub690, sub687]
  rfl
theorem sub692 (p : Pattern) : d12 (change p 108 none) = d12 p := by
  change (if p 168 then d11 (change p 108 none) else d7 (change p 108 none)) = d12 p
  rw [sub691, sub680]
  rfl
theorem sub693 (p : Pattern) : d5 (change p 108 none) = d5 p := by
  rfl
theorem sub694 (p : Pattern) : d58 (change p 108 none) = d58 p := by
  change (if p 271 then d5 (change p 108 none) else d4 (change p 108 none)) = d58 p
  rw [sub693, sub681]
  rfl
theorem sub695 (p : Pattern) : d59 (change p 108 none) = d59 p := by
  change (if p 193 then d58 (change p 108 none) else d9 (change p 108 none)) = d59 p
  rw [sub694, sub689]
  rfl
theorem sub696 (p : Pattern) : d60 (change p 108 none) = d60 p := by
  change (if p 192 then d59 (change p 108 none) else d9 (change p 108 none)) = d60 p
  rw [sub695, sub689]
  rfl
theorem sub697 (p : Pattern) : d61 (change p 108 none) = d61 p := by
  change (if p 186 then d60 (change p 108 none) else d11 (change p 108 none)) = d61 p
  rw [sub696, sub691]
  rfl
theorem sub698 (p : Pattern) : d62 (change p 108 none) = d62 p := by
  change (if p 168 then d61 (change p 108 none) else d56 (change p 108 none)) = d62 p
  rw [sub697, sub684]
  rfl
theorem sub699 (p : Pattern) : d63 (change p 108 none) = d63 p := by
  change (if p 160 then d62 (change p 108 none) else d12 (change p 108 none)) = d63 p
  rw [sub698, sub692]
  rfl
theorem sub700 (p : Pattern) : d64 (change p 108 none) = d64 p := by
  change (if p 141 then d63 (change p 108 none) else d57 (change p 108 none)) = d64 p
  rw [sub699, sub685]
  rfl
theorem sub701 (p : Pattern) : d65 (change p 108 none) = d65 p := by
  change (if p 168 then d60 (change p 108 none) else d55 (change p 108 none)) = d65 p
  rw [sub696, sub683]
  rfl
theorem sub702 (p : Pattern) : d66 (change p 108 none) = d66 p := by
  change (if p 141 then d65 (change p 108 none) else d55 (change p 108 none)) = d66 p
  rw [sub701, sub683]
  rfl
theorem sub703 (p : Pattern) : d67 (change p 108 none) = d67 p := by
  change (if p 134 then d66 (change p 108 none) else d64 (change p 108 none)) = d67 p
  rw [sub702, sub700]
  rfl
theorem sub704 (p : Pattern) : d68 (change p 108 none) = d68 p := by
  change (if p 158 then d55 (change p 108 none) else d57 (change p 108 none)) = d68 p
  rw [sub683, sub685]
  rfl
theorem sub705 (p : Pattern) : d69 (change p 108 none) = d69 p := by
  change (if p 158 then d65 (change p 108 none) else d63 (change p 108 none)) = d69 p
  rw [sub701, sub699]
  rfl
theorem sub706 (p : Pattern) : d70 (change p 108 none) = d70 p := by
  change (if p 141 then d69 (change p 108 none) else d68 (change p 108 none)) = d70 p
  rw [sub705, sub704]
  rfl
theorem sub707 (p : Pattern) : d71 (change p 108 none) = d71 p := by
  change (if p 134 then d66 (change p 108 none) else d70 (change p 108 none)) = d71 p
  rw [sub702, sub706]
  rfl
theorem sub708 (p : Pattern) : d72 (change p 108 none) = d72 p := by
  change (if p 133 then d71 (change p 108 none) else d67 (change p 108 none)) = d72 p
  rw [sub707, sub703]
  rfl
theorem sub709 (p : Pattern) : d73 (change p 108 none) = d73 p := by
  change (if p 133 then d66 (change p 108 none) else d71 (change p 108 none)) = d73 p
  rw [sub702, sub707]
  rfl
theorem sub710 (p : Pattern) : d74 (change p 108 none) = d74 p := by
  change (if p 132 then d73 (change p 108 none) else d72 (change p 108 none)) = d74 p
  rw [sub709, sub708]
  rfl
theorem sub711 (p : Pattern) : d75 (change p 108 none) = d74 p := by
  change d74 (change p 108 none) = d74 p
  exact sub710 p
theorem sub712 (p : Pattern) : d0 (change p 160 (some 186)) = d0 p := by
  rfl
theorem sub713 (p : Pattern) : d2 (change p 160 (some 186)) = d2 p := by
  rfl
theorem sub714 (p : Pattern) : d6 (change p 160 (some 186)) = d6 p := by
  change (if p 193 then d2 (change p 160 (some 186)) else d0 (change p 160 (some 186))) = d6 p
  rw [sub713, sub712]
  rfl
theorem sub715 (p : Pattern) : d7 (change p 160 (some 186)) = d7 p := by
  change (if p 192 then d6 (change p 160 (some 186)) else d0 (change p 160 (some 186))) = d7 p
  rw [sub714, sub712]
  rfl
theorem sub716 (p : Pattern) : d106 (change p 160 (some 186)) = d7 p := by
  change d7 (change p 160 (some 186)) = d7 p
  exact sub715 p
theorem sub717 (p : Pattern) : d1 (change p 160 (some 186)) = d1 p := by
  rfl
theorem sub718 (p : Pattern) : d8 (change p 160 (some 186)) = d8 p := by
  change (if p 271 then d1 (change p 160 (some 186)) else d0 (change p 160 (some 186))) = d8 p
  rw [sub717, sub712]
  rfl
theorem sub719 (p : Pattern) : d3 (change p 160 (some 186)) = d3 p := by
  rfl
end NetHack.Sokoban12CostPartition
