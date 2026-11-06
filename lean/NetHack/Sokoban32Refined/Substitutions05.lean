/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub600 (p : Pattern) : d223 (change p 112 (some 138)) = d862 p := by
  change (if p 113 then d222 (change p 112 (some 138)) else d77 (change p 112 (some 138))) = d862 p
  rw [sub599, sub559]
  rfl
theorem sub601 (p : Pattern) : d224 (change p 112 (some 138)) = d862 p := by
  change d223 (change p 112 (some 138)) = d862 p
  exact sub600 p
theorem sub602 (p : Pattern) : d225 (change p 112 (some 138)) = d863 p := by
  change (if p 106 then d224 (change p 112 (some 138)) else d216 (change p 112 (some 138))) = d863 p
  rw [sub601, sub593]
  rfl
theorem sub603 (p : Pattern) : d226 (change p 112 (some 138)) = d864 p := by
  change (if p 86 then d225 (change p 112 (some 138)) else d210 (change p 112 (some 138))) = d864 p
  rw [sub602, sub587]
  rfl
theorem sub604 (p : Pattern) : d227 (change p 112 (some 138)) = d864 p := by
  change (if p 80 then d226 (change p 112 (some 138)) else d207 (change p 112 (some 138))) = d864 p
  rw [sub603, sub584]
  simp only [ite_self]
theorem sub605 (p : Pattern) : d0 (change p 80 none) = d0 p := by
  rfl
theorem sub606 (p : Pattern) : d2 (change p 80 none) = d2 p := by
  rfl
theorem sub607 (p : Pattern) : d3 (change p 80 none) = d3 p := by
  change (if p 161 then d2 (change p 80 none) else d0 (change p 80 none)) = d3 p
  rw [sub606, sub605]
  rfl
theorem sub608 (p : Pattern) : d4 (change p 80 none) = d4 p := by
  change (if p 160 then d3 (change p 80 none) else d0 (change p 80 none)) = d4 p
  rw [sub607, sub605]
  rfl
theorem sub609 (p : Pattern) : d5 (change p 80 none) = d5 p := by
  change (if p 160 then d2 (change p 80 none) else d0 (change p 80 none)) = d5 p
  rw [sub606, sub605]
  rfl
theorem sub610 (p : Pattern) : d6 (change p 80 none) = d6 p := by
  change (if p 159 then d5 (change p 80 none) else d4 (change p 80 none)) = d6 p
  rw [sub609, sub608]
  rfl
theorem sub611 (p : Pattern) : d7 (change p 80 none) = d7 p := by
  change (if p 159 then d2 (change p 80 none) else d4 (change p 80 none)) = d7 p
  rw [sub606, sub608]
  rfl
theorem sub612 (p : Pattern) : d8 (change p 80 none) = d8 p := by
  change (if p 158 then d7 (change p 80 none) else d6 (change p 80 none)) = d8 p
  rw [sub611, sub610]
  rfl
theorem sub613 (p : Pattern) : d1 (change p 80 none) = d1 p := by
  rfl
theorem sub614 (p : Pattern) : d9 (change p 80 none) = d9 p := by
  change (if p 161 then d2 (change p 80 none) else d1 (change p 80 none)) = d9 p
  rw [sub606, sub613]
  rfl
theorem sub615 (p : Pattern) : d10 (change p 80 none) = d10 p := by
  change (if p 160 then d9 (change p 80 none) else d1 (change p 80 none)) = d10 p
  rw [sub614, sub613]
  rfl
theorem sub616 (p : Pattern) : d11 (change p 80 none) = d11 p := by
  change (if p 160 then d2 (change p 80 none) else d1 (change p 80 none)) = d11 p
  rw [sub606, sub613]
  rfl
theorem sub617 (p : Pattern) : d12 (change p 80 none) = d12 p := by
  change (if p 159 then d11 (change p 80 none) else d10 (change p 80 none)) = d12 p
  rw [sub616, sub615]
  rfl
theorem sub618 (p : Pattern) : d13 (change p 80 none) = d13 p := by
  change (if p 159 then d2 (change p 80 none) else d10 (change p 80 none)) = d13 p
  rw [sub606, sub615]
  rfl
theorem sub619 (p : Pattern) : d14 (change p 80 none) = d14 p := by
  change (if p 158 then d13 (change p 80 none) else d12 (change p 80 none)) = d14 p
  rw [sub618, sub617]
  rfl
theorem sub620 (p : Pattern) : d15 (change p 80 none) = d15 p := by
  change (if p 139 then d14 (change p 80 none) else d8 (change p 80 none)) = d15 p
  rw [sub619, sub612]
  rfl
theorem sub621 (p : Pattern) : d16 (change p 80 none) = d16 p := by
  change (if p 138 then d15 (change p 80 none) else d8 (change p 80 none)) = d16 p
  rw [sub620, sub612]
  rfl
theorem sub622 (p : Pattern) : d17 (change p 80 none) = d17 p := by
  change (if p 160 then d2 (change p 80 none) else d3 (change p 80 none)) = d17 p
  rw [sub606, sub607]
  rfl
theorem sub623 (p : Pattern) : d18 (change p 80 none) = d18 p := by
  change (if p 159 then d17 (change p 80 none) else d4 (change p 80 none)) = d18 p
  rw [sub622, sub608]
  rfl
theorem sub624 (p : Pattern) : d19 (change p 80 none) = d19 p := by
  change (if p 159 then d2 (change p 80 none) else d17 (change p 80 none)) = d19 p
  rw [sub606, sub622]
  rfl
theorem sub625 (p : Pattern) : d20 (change p 80 none) = d20 p := by
  change (if p 158 then d19 (change p 80 none) else d18 (change p 80 none)) = d20 p
  rw [sub624, sub623]
  rfl
theorem sub626 (p : Pattern) : d21 (change p 80 none) = d21 p := by
  change (if p 160 then d2 (change p 80 none) else d9 (change p 80 none)) = d21 p
  rw [sub606, sub614]
  rfl
theorem sub627 (p : Pattern) : d22 (change p 80 none) = d22 p := by
  change (if p 159 then d21 (change p 80 none) else d10 (change p 80 none)) = d22 p
  rw [sub626, sub615]
  rfl
theorem sub628 (p : Pattern) : d23 (change p 80 none) = d23 p := by
  change (if p 159 then d2 (change p 80 none) else d21 (change p 80 none)) = d23 p
  rw [sub606, sub626]
  rfl
theorem sub629 (p : Pattern) : d24 (change p 80 none) = d24 p := by
  change (if p 158 then d23 (change p 80 none) else d22 (change p 80 none)) = d24 p
  rw [sub628, sub627]
  rfl
theorem sub630 (p : Pattern) : d25 (change p 80 none) = d25 p := by
  change (if p 139 then d24 (change p 80 none) else d20 (change p 80 none)) = d25 p
  rw [sub629, sub625]
  rfl
theorem sub631 (p : Pattern) : d26 (change p 80 none) = d26 p := by
  change (if p 138 then d25 (change p 80 none) else d20 (change p 80 none)) = d26 p
  rw [sub630, sub625]
  rfl
theorem sub632 (p : Pattern) : d27 (change p 80 none) = d27 p := by
  change (if p 134 then d26 (change p 80 none) else d16 (change p 80 none)) = d27 p
  rw [sub631, sub621]
  rfl
theorem sub633 (p : Pattern) : d28 (change p 80 none) = d28 p := by
  change (if p 133 then d27 (change p 80 none) else d16 (change p 80 none)) = d28 p
  rw [sub632, sub621]
  rfl
theorem sub634 (p : Pattern) : d29 (change p 80 none) = d29 p := by
  change (if p 161 then d1 (change p 80 none) else d0 (change p 80 none)) = d29 p
  rw [sub613, sub605]
  rfl
theorem sub635 (p : Pattern) : d30 (change p 80 none) = d30 p := by
  change (if p 160 then d2 (change p 80 none) else d29 (change p 80 none)) = d30 p
  rw [sub606, sub634]
  rfl
theorem sub636 (p : Pattern) : d31 (change p 80 none) = d31 p := by
  change (if p 159 then d30 (change p 80 none) else d4 (change p 80 none)) = d31 p
  rw [sub635, sub608]
  rfl
theorem sub637 (p : Pattern) : d32 (change p 80 none) = d32 p := by
  change (if p 159 then d2 (change p 80 none) else d30 (change p 80 none)) = d32 p
  rw [sub606, sub635]
  rfl
theorem sub638 (p : Pattern) : d33 (change p 80 none) = d33 p := by
  change (if p 158 then d32 (change p 80 none) else d31 (change p 80 none)) = d33 p
  rw [sub637, sub636]
  rfl
theorem sub639 (p : Pattern) : d34 (change p 80 none) = d34 p := by
  change (if p 139 then d24 (change p 80 none) else d33 (change p 80 none)) = d34 p
  rw [sub629, sub638]
  rfl
theorem sub640 (p : Pattern) : d35 (change p 80 none) = d35 p := by
  change (if p 138 then d34 (change p 80 none) else d33 (change p 80 none)) = d35 p
  rw [sub639, sub638]
  rfl
theorem sub641 (p : Pattern) : d36 (change p 80 none) = d36 p := by
  change (if p 134 then d35 (change p 80 none) else d16 (change p 80 none)) = d36 p
  rw [sub640, sub621]
  rfl
theorem sub642 (p : Pattern) : d37 (change p 80 none) = d37 p := by
  change (if p 159 then d2 (change p 80 none) else d5 (change p 80 none)) = d37 p
  rw [sub606, sub609]
  rfl
theorem sub643 (p : Pattern) : d38 (change p 80 none) = d38 p := by
  change (if p 158 then d37 (change p 80 none) else d6 (change p 80 none)) = d38 p
  rw [sub642, sub610]
  rfl
theorem sub644 (p : Pattern) : d39 (change p 80 none) = d39 p := by
  change (if p 159 then d2 (change p 80 none) else d11 (change p 80 none)) = d39 p
  rw [sub606, sub616]
  rfl
theorem sub645 (p : Pattern) : d40 (change p 80 none) = d40 p := by
  change (if p 158 then d39 (change p 80 none) else d12 (change p 80 none)) = d40 p
  rw [sub644, sub617]
  rfl
theorem sub646 (p : Pattern) : d41 (change p 80 none) = d41 p := by
  change (if p 139 then d40 (change p 80 none) else d38 (change p 80 none)) = d41 p
  rw [sub645, sub643]
  rfl
theorem sub647 (p : Pattern) : d42 (change p 80 none) = d42 p := by
  change (if p 138 then d41 (change p 80 none) else d38 (change p 80 none)) = d42 p
  rw [sub646, sub643]
  rfl
theorem sub648 (p : Pattern) : d43 (change p 80 none) = d43 p := by
  change (if p 134 then d26 (change p 80 none) else d42 (change p 80 none)) = d43 p
  rw [sub631, sub647]
  rfl
theorem sub649 (p : Pattern) : d44 (change p 80 none) = d44 p := by
  change (if p 133 then d43 (change p 80 none) else d36 (change p 80 none)) = d44 p
  rw [sub648, sub641]
  rfl
theorem sub650 (p : Pattern) : d45 (change p 80 none) = d45 p := by
  change (if p 132 then d44 (change p 80 none) else d28 (change p 80 none)) = d45 p
  rw [sub649, sub633]
  rfl
theorem sub651 (p : Pattern) : d46 (change p 80 none) = d46 p := by
  change (if p 134 then d25 (change p 80 none) else d15 (change p 80 none)) = d46 p
  rw [sub630, sub620]
  rfl
theorem sub652 (p : Pattern) : d47 (change p 80 none) = d47 p := by
  change (if p 133 then d46 (change p 80 none) else d15 (change p 80 none)) = d47 p
  rw [sub651, sub620]
  rfl
theorem sub653 (p : Pattern) : d48 (change p 80 none) = d48 p := by
  change (if p 134 then d34 (change p 80 none) else d15 (change p 80 none)) = d48 p
  rw [sub639, sub620]
  rfl
theorem sub654 (p : Pattern) : d49 (change p 80 none) = d49 p := by
  change (if p 134 then d25 (change p 80 none) else d41 (change p 80 none)) = d49 p
  rw [sub630, sub646]
  rfl
theorem sub655 (p : Pattern) : d50 (change p 80 none) = d50 p := by
  change (if p 133 then d49 (change p 80 none) else d48 (change p 80 none)) = d50 p
  rw [sub654, sub653]
  rfl
theorem sub656 (p : Pattern) : d51 (change p 80 none) = d51 p := by
  change (if p 132 then d50 (change p 80 none) else d47 (change p 80 none)) = d51 p
  rw [sub655, sub652]
  rfl
theorem sub657 (p : Pattern) : d52 (change p 80 none) = d52 p := by
  change (if p 139 then d2 (change p 80 none) else d8 (change p 80 none)) = d52 p
  rw [sub606, sub612]
  rfl
theorem sub658 (p : Pattern) : d53 (change p 80 none) = d53 p := by
  change (if p 138 then d52 (change p 80 none) else d15 (change p 80 none)) = d53 p
  rw [sub657, sub620]
  rfl
theorem sub659 (p : Pattern) : d54 (change p 80 none) = d54 p := by
  change (if p 139 then d2 (change p 80 none) else d20 (change p 80 none)) = d54 p
  rw [sub606, sub625]
  rfl
theorem sub660 (p : Pattern) : d55 (change p 80 none) = d55 p := by
  change (if p 138 then d54 (change p 80 none) else d25 (change p 80 none)) = d55 p
  rw [sub659, sub630]
  rfl
theorem sub661 (p : Pattern) : d56 (change p 80 none) = d56 p := by
  change (if p 134 then d55 (change p 80 none) else d53 (change p 80 none)) = d56 p
  rw [sub660, sub658]
  rfl
theorem sub662 (p : Pattern) : d57 (change p 80 none) = d57 p := by
  change (if p 133 then d56 (change p 80 none) else d53 (change p 80 none)) = d57 p
  rw [sub661, sub658]
  rfl
theorem sub663 (p : Pattern) : d58 (change p 80 none) = d58 p := by
  change (if p 139 then d2 (change p 80 none) else d33 (change p 80 none)) = d58 p
  rw [sub606, sub638]
  rfl
theorem sub664 (p : Pattern) : d59 (change p 80 none) = d59 p := by
  change (if p 138 then d58 (change p 80 none) else d34 (change p 80 none)) = d59 p
  rw [sub663, sub639]
  rfl
theorem sub665 (p : Pattern) : d60 (change p 80 none) = d60 p := by
  change (if p 134 then d59 (change p 80 none) else d53 (change p 80 none)) = d60 p
  rw [sub664, sub658]
  rfl
theorem sub666 (p : Pattern) : d61 (change p 80 none) = d61 p := by
  change (if p 139 then d2 (change p 80 none) else d38 (change p 80 none)) = d61 p
  rw [sub606, sub643]
  rfl
theorem sub667 (p : Pattern) : d62 (change p 80 none) = d62 p := by
  change (if p 138 then d61 (change p 80 none) else d41 (change p 80 none)) = d62 p
  rw [sub666, sub646]
  rfl
theorem sub668 (p : Pattern) : d63 (change p 80 none) = d63 p := by
  change (if p 134 then d55 (change p 80 none) else d62 (change p 80 none)) = d63 p
  rw [sub660, sub667]
  rfl
theorem sub669 (p : Pattern) : d64 (change p 80 none) = d64 p := by
  change (if p 133 then d63 (change p 80 none) else d60 (change p 80 none)) = d64 p
  rw [sub668, sub665]
  rfl
theorem sub670 (p : Pattern) : d65 (change p 80 none) = d65 p := by
  change (if p 132 then d64 (change p 80 none) else d57 (change p 80 none)) = d65 p
  rw [sub669, sub662]
  rfl
theorem sub671 (p : Pattern) : d66 (change p 80 none) = d66 p := by
  change (if p 113 then d65 (change p 80 none) else d51 (change p 80 none)) = d66 p
  rw [sub670, sub656]
  rfl
theorem sub672 (p : Pattern) : d67 (change p 80 none) = d67 p := by
  change (if p 112 then d66 (change p 80 none) else d45 (change p 80 none)) = d67 p
  rw [sub671, sub650]
  rfl
theorem sub673 (p : Pattern) : d68 (change p 80 none) = d68 p := by
  change (if p 139 then d2 (change p 80 none) else d40 (change p 80 none)) = d68 p
  rw [sub606, sub645]
  rfl
theorem sub674 (p : Pattern) : d69 (change p 80 none) = d69 p := by
  change (if p 138 then d68 (change p 80 none) else d40 (change p 80 none)) = d69 p
  rw [sub673, sub645]
  rfl
theorem sub675 (p : Pattern) : d70 (change p 80 none) = d70 p := by
  change (if p 139 then d2 (change p 80 none) else d24 (change p 80 none)) = d70 p
  rw [sub606, sub629]
  rfl
theorem sub676 (p : Pattern) : d71 (change p 80 none) = d71 p := by
  change (if p 138 then d70 (change p 80 none) else d24 (change p 80 none)) = d71 p
  rw [sub675, sub629]
  rfl
theorem sub677 (p : Pattern) : d72 (change p 80 none) = d72 p := by
  change (if p 134 then d71 (change p 80 none) else d69 (change p 80 none)) = d72 p
  rw [sub676, sub674]
  rfl
theorem sub678 (p : Pattern) : d73 (change p 80 none) = d73 p := by
  change (if p 133 then d72 (change p 80 none) else d27 (change p 80 none)) = d73 p
  rw [sub677, sub632]
  rfl
theorem sub679 (p : Pattern) : d74 (change p 80 none) = d74 p := by
  change (if p 132 then d73 (change p 80 none) else d28 (change p 80 none)) = d74 p
  rw [sub678, sub633]
  rfl
theorem sub680 (p : Pattern) : d75 (change p 80 none) = d75 p := by
  change (if p 134 then d70 (change p 80 none) else d68 (change p 80 none)) = d75 p
  rw [sub675, sub673]
  rfl
theorem sub681 (p : Pattern) : d76 (change p 80 none) = d76 p := by
  change (if p 133 then d75 (change p 80 none) else d27 (change p 80 none)) = d76 p
  rw [sub680, sub632]
  rfl
theorem sub682 (p : Pattern) : d77 (change p 80 none) = d77 p := by
  change (if p 132 then d76 (change p 80 none) else d28 (change p 80 none)) = d77 p
  rw [sub681, sub633]
  rfl
theorem sub683 (p : Pattern) : d78 (change p 80 none) = d78 p := by
  change (if p 113 then d77 (change p 80 none) else d74 (change p 80 none)) = d78 p
  rw [sub682, sub679]
  rfl
theorem sub684 (p : Pattern) : d79 (change p 80 none) = d79 p := by
  change (if p 133 then d75 (change p 80 none) else d46 (change p 80 none)) = d79 p
  rw [sub680, sub651]
  rfl
theorem sub685 (p : Pattern) : d80 (change p 80 none) = d80 p := by
  change (if p 132 then d79 (change p 80 none) else d47 (change p 80 none)) = d80 p
  rw [sub684, sub652]
  rfl
theorem sub686 (p : Pattern) : d81 (change p 80 none) = d81 p := by
  change (if p 133 then d75 (change p 80 none) else d56 (change p 80 none)) = d81 p
  rw [sub680, sub661]
  rfl
theorem sub687 (p : Pattern) : d82 (change p 80 none) = d82 p := by
  change (if p 132 then d81 (change p 80 none) else d57 (change p 80 none)) = d82 p
  rw [sub686, sub662]
  rfl
theorem sub688 (p : Pattern) : d83 (change p 80 none) = d83 p := by
  change (if p 113 then d82 (change p 80 none) else d80 (change p 80 none)) = d83 p
  rw [sub687, sub685]
  rfl
theorem sub689 (p : Pattern) : d84 (change p 80 none) = d84 p := by
  change (if p 112 then d83 (change p 80 none) else d78 (change p 80 none)) = d84 p
  rw [sub688, sub683]
  rfl
theorem sub690 (p : Pattern) : d85 (change p 80 none) = d85 p := by
  change (if p 106 then d84 (change p 80 none) else d67 (change p 80 none)) = d85 p
  rw [sub689, sub672]
  rfl
theorem sub691 (p : Pattern) : d86 (change p 80 none) = d86 p := by
  change (if p 138 then d52 (change p 80 none) else d8 (change p 80 none)) = d86 p
  rw [sub657, sub612]
  rfl
theorem sub692 (p : Pattern) : d87 (change p 80 none) = d87 p := by
  change (if p 138 then d54 (change p 80 none) else d20 (change p 80 none)) = d87 p
  rw [sub659, sub625]
  rfl
theorem sub693 (p : Pattern) : d88 (change p 80 none) = d88 p := by
  change (if p 134 then d87 (change p 80 none) else d86 (change p 80 none)) = d88 p
  rw [sub692, sub691]
  rfl
theorem sub694 (p : Pattern) : d89 (change p 80 none) = d89 p := by
  change (if p 133 then d88 (change p 80 none) else d86 (change p 80 none)) = d89 p
  rw [sub693, sub691]
  rfl
theorem sub695 (p : Pattern) : d90 (change p 80 none) = d90 p := by
  change (if p 138 then d58 (change p 80 none) else d33 (change p 80 none)) = d90 p
  rw [sub663, sub638]
  rfl
theorem sub696 (p : Pattern) : d91 (change p 80 none) = d91 p := by
  change (if p 134 then d90 (change p 80 none) else d86 (change p 80 none)) = d91 p
  rw [sub695, sub691]
  rfl
theorem sub697 (p : Pattern) : d92 (change p 80 none) = d92 p := by
  change (if p 138 then d61 (change p 80 none) else d38 (change p 80 none)) = d92 p
  rw [sub666, sub643]
  rfl
theorem sub698 (p : Pattern) : d93 (change p 80 none) = d93 p := by
  change (if p 134 then d87 (change p 80 none) else d92 (change p 80 none)) = d93 p
  rw [sub692, sub697]
  rfl
theorem sub699 (p : Pattern) : d94 (change p 80 none) = d94 p := by
  change (if p 133 then d93 (change p 80 none) else d91 (change p 80 none)) = d94 p
  rw [sub698, sub696]
  rfl
theorem sub700 (p : Pattern) : d95 (change p 80 none) = d95 p := by
  change (if p 132 then d94 (change p 80 none) else d89 (change p 80 none)) = d95 p
  rw [sub699, sub694]
  rfl
theorem sub701 (p : Pattern) : d96 (change p 80 none) = d96 p := by
  change (if p 113 then d95 (change p 80 none) else d45 (change p 80 none)) = d96 p
  rw [sub700, sub650]
  rfl
theorem sub702 (p : Pattern) : d97 (change p 80 none) = d97 p := by
  change (if p 139 then d2 (change p 80 none) else d14 (change p 80 none)) = d97 p
  rw [sub606, sub619]
  rfl
theorem sub703 (p : Pattern) : d98 (change p 80 none) = d98 p := by
  change (if p 138 then d97 (change p 80 none) else d14 (change p 80 none)) = d98 p
  rw [sub702, sub619]
  rfl
theorem sub704 (p : Pattern) : d99 (change p 80 none) = d99 p := by
  change (if p 134 then d71 (change p 80 none) else d98 (change p 80 none)) = d99 p
  rw [sub676, sub703]
  rfl
theorem sub705 (p : Pattern) : d100 (change p 80 none) = d100 p := by
  change (if p 133 then d99 (change p 80 none) else d98 (change p 80 none)) = d100 p
  rw [sub704, sub703]
  rfl
theorem sub706 (p : Pattern) : d101 (change p 80 none) = d101 p := by
  change (if p 133 then d72 (change p 80 none) else d99 (change p 80 none)) = d101 p
  rw [sub677, sub704]
  rfl
theorem sub707 (p : Pattern) : d102 (change p 80 none) = d102 p := by
  change (if p 132 then d101 (change p 80 none) else d100 (change p 80 none)) = d102 p
  rw [sub706, sub705]
  rfl
theorem sub708 (p : Pattern) : d103 (change p 80 none) = d103 p := by
  change (if p 112 then d102 (change p 80 none) else d96 (change p 80 none)) = d103 p
  rw [sub707, sub701]
  rfl
theorem sub709 (p : Pattern) : d104 (change p 80 none) = d104 p := by
  change (if p 133 then d75 (change p 80 none) else d88 (change p 80 none)) = d104 p
  rw [sub680, sub693]
  rfl
theorem sub710 (p : Pattern) : d105 (change p 80 none) = d105 p := by
  change (if p 132 then d104 (change p 80 none) else d89 (change p 80 none)) = d105 p
  rw [sub709, sub694]
  rfl
theorem sub711 (p : Pattern) : d106 (change p 80 none) = d106 p := by
  change (if p 113 then d105 (change p 80 none) else d77 (change p 80 none)) = d106 p
  rw [sub710, sub682]
  rfl
theorem sub712 (p : Pattern) : d107 (change p 80 none) = d107 p := by
  change (if p 133 then d2 (change p 80 none) else d99 (change p 80 none)) = d107 p
  rw [sub606, sub704]
  rfl
theorem sub713 (p : Pattern) : d108 (change p 80 none) = d108 p := by
  change (if p 132 then d107 (change p 80 none) else d100 (change p 80 none)) = d108 p
  rw [sub712, sub705]
  rfl
theorem sub714 (p : Pattern) : d109 (change p 80 none) = d109 p := by
  change (if p 134 then d70 (change p 80 none) else d97 (change p 80 none)) = d109 p
  rw [sub675, sub702]
  rfl
theorem sub715 (p : Pattern) : d110 (change p 80 none) = d110 p := by
  change (if p 133 then d109 (change p 80 none) else d97 (change p 80 none)) = d110 p
  rw [sub714, sub702]
  rfl
theorem sub716 (p : Pattern) : d111 (change p 80 none) = d111 p := by
  change (if p 133 then d2 (change p 80 none) else d109 (change p 80 none)) = d111 p
  rw [sub606, sub714]
  rfl
theorem sub717 (p : Pattern) : d112 (change p 80 none) = d112 p := by
  change (if p 132 then d111 (change p 80 none) else d110 (change p 80 none)) = d112 p
  rw [sub716, sub715]
  rfl
theorem sub718 (p : Pattern) : d113 (change p 80 none) = d113 p := by
  change (if p 113 then d112 (change p 80 none) else d108 (change p 80 none)) = d113 p
  rw [sub717, sub713]
  rfl
theorem sub719 (p : Pattern) : d114 (change p 80 none) = d114 p := by
  change (if p 112 then d113 (change p 80 none) else d106 (change p 80 none)) = d114 p
  rw [sub718, sub711]
  rfl
end NetHack.Sokoban32Refined
