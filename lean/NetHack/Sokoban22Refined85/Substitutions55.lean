/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions54
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub6600 (p : Pattern) : d48 (change p 10000 (some 224)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d24 (change p 10000 (some 224))) = d48 p
  rw [sub6559, sub6573]
  rfl
theorem sub6601 (p : Pattern) : d49 (change p 10000 (some 224)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d48 (change p 10000 (some 224))) = d49 p
  rw [sub6559, sub6600]
  rfl
theorem sub6602 (p : Pattern) : d50 (change p 10000 (some 224)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 224)) else d47 (change p 10000 (some 224))) = d50 p
  rw [sub6601, sub6599]
  rfl
theorem sub6603 (p : Pattern) : d51 (change p 10000 (some 224)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 224)) else d45 (change p 10000 (some 224))) = d51 p
  rw [sub6602, sub6597]
  rfl
theorem sub6604 (p : Pattern) : d52 (change p 10000 (some 224)) = d52 p := by
  change (if p 160 then d51 (change p 10000 (some 224)) else d29 (change p 10000 (some 224))) = d52 p
  rw [sub6603, sub6578]
  rfl
theorem sub6605 (p : Pattern) : d53 (change p 10000 (some 224)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 224)) else d31 (change p 10000 (some 224))) = d53 p
  rw [sub6582, sub6581]
  rfl
theorem sub6606 (p : Pattern) : d54 (change p 10000 (some 224)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 224)) else d16 (change p 10000 (some 224))) = d54 p
  rw [sub6605, sub6563]
  rfl
theorem sub6607 (p : Pattern) : d55 (change p 10000 (some 224)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 224)) else d20 (change p 10000 (some 224))) = d55 p
  rw [sub6575, sub6568]
  rfl
theorem sub6608 (p : Pattern) : d56 (change p 10000 (some 224)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 224)) else d54 (change p 10000 (some 224))) = d56 p
  rw [sub6607, sub6606]
  rfl
theorem sub6609 (p : Pattern) : d10 (change p 10000 (some 224)) = d10 p := by
  rfl
theorem sub6610 (p : Pattern) : d57 (change p 10000 (some 224)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d10 (change p 10000 (some 224))) = d57 p
  rw [sub6559, sub6609]
  rfl
theorem sub6611 (p : Pattern) : d58 (change p 10000 (some 224)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 224)) else d10 (change p 10000 (some 224))) = d58 p
  rw [sub6610, sub6609]
  rfl
theorem sub6612 (p : Pattern) : d59 (change p 10000 (some 224)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d58 (change p 10000 (some 224))) = d59 p
  rw [sub6559, sub6611]
  rfl
theorem sub6613 (p : Pattern) : d60 (change p 10000 (some 224)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 224)) else d58 (change p 10000 (some 224))) = d60 p
  rw [sub6612, sub6611]
  rfl
theorem sub6614 (p : Pattern) : d61 (change p 10000 (some 224)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 224)) else d20 (change p 10000 (some 224))) = d61 p
  rw [sub6613, sub6568]
  rfl
theorem sub6615 (p : Pattern) : d62 (change p 10000 (some 224)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 224)) else d40 (change p 10000 (some 224))) = d62 p
  rw [sub6593, sub6592]
  rfl
theorem sub6616 (p : Pattern) : d63 (change p 10000 (some 224)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d62 (change p 10000 (some 224))) = d63 p
  rw [sub6559, sub6615]
  rfl
theorem sub6617 (p : Pattern) : d64 (change p 10000 (some 224)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 224)) else d61 (change p 10000 (some 224))) = d64 p
  rw [sub6616, sub6614]
  rfl
theorem sub6618 (p : Pattern) : d65 (change p 10000 (some 224)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 224)) else d56 (change p 10000 (some 224))) = d65 p
  rw [sub6617, sub6608]
  rfl
theorem sub6619 (p : Pattern) : d66 (change p 10000 (some 224)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d31 (change p 10000 (some 224))) = d66 p
  rw [sub6559, sub6581]
  rfl
theorem sub6620 (p : Pattern) : d67 (change p 10000 (some 224)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 224)) else d37 (change p 10000 (some 224))) = d67 p
  rw [sub6619, sub6588]
  rfl
theorem sub6621 (p : Pattern) : d68 (change p 10000 (some 224)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 224)) else d43 (change p 10000 (some 224))) = d68 p
  rw [sub6600, sub6595]
  rfl
theorem sub6622 (p : Pattern) : d69 (change p 10000 (some 224)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 224)) else d67 (change p 10000 (some 224))) = d69 p
  rw [sub6621, sub6620]
  rfl
theorem sub6623 (p : Pattern) : d70 (change p 10000 (some 224)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d58 (change p 10000 (some 224))) = d70 p
  rw [sub6559, sub6611]
  rfl
theorem sub6624 (p : Pattern) : d71 (change p 10000 (some 224)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 224)) else d43 (change p 10000 (some 224))) = d71 p
  rw [sub6623, sub6595]
  rfl
theorem sub6625 (p : Pattern) : d72 (change p 10000 (some 224)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d40 (change p 10000 (some 224))) = d72 p
  rw [sub6559, sub6592]
  rfl
theorem sub6626 (p : Pattern) : d73 (change p 10000 (some 224)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d72 (change p 10000 (some 224))) = d73 p
  rw [sub6559, sub6625]
  rfl
theorem sub6627 (p : Pattern) : d74 (change p 10000 (some 224)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 224)) else d71 (change p 10000 (some 224))) = d74 p
  rw [sub6626, sub6624]
  rfl
theorem sub6628 (p : Pattern) : d75 (change p 10000 (some 224)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 224)) else d69 (change p 10000 (some 224))) = d75 p
  rw [sub6627, sub6622]
  rfl
theorem sub6629 (p : Pattern) : d76 (change p 10000 (some 224)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 224)) else d65 (change p 10000 (some 224))) = d76 p
  rw [sub6628, sub6618]
  rfl
theorem sub6630 (p : Pattern) : d77 (change p 10000 (some 224)) = d77 p := by
  change (if p 141 then d76 (change p 10000 (some 224)) else d52 (change p 10000 (some 224))) = d77 p
  rw [sub6629, sub6604]
  rfl
theorem sub6631 (p : Pattern) : d78 (change p 10000 (some 224)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 224)) else d35 (change p 10000 (some 224))) = d78 p
  rw [sub6587, sub6586]
  rfl
theorem sub6632 (p : Pattern) : d79 (change p 10000 (some 224)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 224)) else d53 (change p 10000 (some 224))) = d79 p
  rw [sub6631, sub6605]
  rfl
theorem sub6633 (p : Pattern) : d80 (change p 10000 (some 224)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 224)) else d79 (change p 10000 (some 224))) = d80 p
  rw [sub6616, sub6632]
  rfl
theorem sub6634 (p : Pattern) : d81 (change p 10000 (some 224)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d80 (change p 10000 (some 224))) = d81 p
  rw [sub6559, sub6633]
  rfl
theorem sub6635 (p : Pattern) : d82 (change p 10000 (some 224)) = d82 p := by
  change (if p 160 then d81 (change p 10000 (some 224)) else d29 (change p 10000 (some 224))) = d82 p
  rw [sub6634, sub6578]
  rfl
theorem sub6636 (p : Pattern) : d83 (change p 10000 (some 224)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d78 (change p 10000 (some 224))) = d83 p
  rw [sub6559, sub6631]
  rfl
theorem sub6637 (p : Pattern) : d84 (change p 10000 (some 224)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d83 (change p 10000 (some 224))) = d84 p
  rw [sub6559, sub6636]
  rfl
theorem sub6638 (p : Pattern) : d85 (change p 10000 (some 224)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d84 (change p 10000 (some 224))) = d85 p
  rw [sub6559, sub6637]
  rfl
theorem sub6639 (p : Pattern) : d86 (change p 10000 (some 224)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 224)) else d65 (change p 10000 (some 224))) = d86 p
  rw [sub6638, sub6618]
  rfl
theorem sub6640 (p : Pattern) : d87 (change p 10000 (some 224)) = d87 p := by
  change (if p 141 then d86 (change p 10000 (some 224)) else d82 (change p 10000 (some 224))) = d87 p
  rw [sub6639, sub6635]
  rfl
theorem sub6641 (p : Pattern) : d88 (change p 10000 (some 224)) = d88 p := by
  change (if p 138 then d87 (change p 10000 (some 224)) else d77 (change p 10000 (some 224))) = d88 p
  rw [sub6640, sub6630]
  rfl
theorem sub6642 (p : Pattern) : d89 (change p 10000 (some 224)) = d89 p := by
  change (if p 163 then d62 (change p 10000 (some 224)) else d26 (change p 10000 (some 224))) = d89 p
  rw [sub6615, sub6575]
  rfl
theorem sub6643 (p : Pattern) : d90 (change p 10000 (some 224)) = d90 p := by
  change (if p 162 then d63 (change p 10000 (some 224)) else d89 (change p 10000 (some 224))) = d90 p
  rw [sub6616, sub6642]
  rfl
theorem sub6644 (p : Pattern) : d91 (change p 10000 (some 224)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d63 (change p 10000 (some 224))) = d91 p
  rw [sub6559, sub6616]
  rfl
theorem sub6645 (p : Pattern) : d92 (change p 10000 (some 224)) = d92 p := by
  change (if p 161 then d91 (change p 10000 (some 224)) else d90 (change p 10000 (some 224))) = d92 p
  rw [sub6644, sub6643]
  rfl
theorem sub6646 (p : Pattern) : d93 (change p 10000 (some 224)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d91 (change p 10000 (some 224))) = d93 p
  rw [sub6559, sub6644]
  rfl
theorem sub6647 (p : Pattern) : d94 (change p 10000 (some 224)) = d94 p := by
  change (if p 160 then d93 (change p 10000 (some 224)) else d92 (change p 10000 (some 224))) = d94 p
  rw [sub6646, sub6645]
  rfl
theorem sub6648 (p : Pattern) : d95 (change p 10000 (some 224)) = d95 p := by
  change (if p 160 then d12 (change p 10000 (some 224)) else d93 (change p 10000 (some 224))) = d95 p
  rw [sub6559, sub6646]
  rfl
theorem sub6649 (p : Pattern) : d96 (change p 10000 (some 224)) = d96 p := by
  change (if p 141 then d95 (change p 10000 (some 224)) else d94 (change p 10000 (some 224))) = d96 p
  rw [sub6648, sub6647]
  rfl
theorem sub6650 (p : Pattern) : d97 (change p 10000 (some 224)) = d97 p := by
  change (if p 138 then d96 (change p 10000 (some 224)) else d87 (change p 10000 (some 224))) = d97 p
  rw [sub6649, sub6640]
  rfl
theorem sub6651 (p : Pattern) : d98 (change p 10000 (some 224)) = d98 p := by
  change (if p 116 then d97 (change p 10000 (some 224)) else d88 (change p 10000 (some 224))) = d98 p
  rw [sub6650, sub6641]
  rfl
theorem sub6652 (p : Pattern) : d99 (change p 10000 (some 224)) = d99 p := by
  change (if p 138 then d12 (change p 10000 (some 224)) else d87 (change p 10000 (some 224))) = d99 p
  rw [sub6559, sub6640]
  rfl
theorem sub6653 (p : Pattern) : d100 (change p 10000 (some 224)) = d100 p := by
  change (if p 116 then d99 (change p 10000 (some 224)) else d88 (change p 10000 (some 224))) = d100 p
  rw [sub6652, sub6641]
  rfl
theorem sub6654 (p : Pattern) : d101 (change p 10000 (some 224)) = d101 p := by
  change (if p 115 then d100 (change p 10000 (some 224)) else d98 (change p 10000 (some 224))) = d101 p
  rw [sub6653, sub6651]
  rfl
theorem sub6655 (p : Pattern) : d1 (change p 10000 (some 224)) = d1 p := by
  rfl
theorem sub6656 (p : Pattern) : d102 (change p 10000 (some 224)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d1 (change p 10000 (some 224))) = d102 p
  rw [sub6559, sub6655]
  rfl
theorem sub6657 (p : Pattern) : d103 (change p 10000 (some 224)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 224)) else d1 (change p 10000 (some 224))) = d103 p
  rw [sub6656, sub6655]
  rfl
theorem sub6658 (p : Pattern) : d104 (change p 10000 (some 224)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d103 (change p 10000 (some 224))) = d104 p
  rw [sub6559, sub6657]
  rfl
theorem sub6659 (p : Pattern) : d105 (change p 10000 (some 224)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 224)) else d103 (change p 10000 (some 224))) = d105 p
  rw [sub6658, sub6657]
  rfl
theorem sub6660 (p : Pattern) : d5 (change p 10000 (some 224)) = d5 p := by
  rfl
theorem sub6661 (p : Pattern) : d106 (change p 10000 (some 224)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d5 (change p 10000 (some 224))) = d106 p
  rw [sub6559, sub6660]
  rfl
theorem sub6662 (p : Pattern) : d107 (change p 10000 (some 224)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 224)) else d5 (change p 10000 (some 224))) = d107 p
  rw [sub6661, sub6660]
  rfl
theorem sub6663 (p : Pattern) : d108 (change p 10000 (some 224)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d107 (change p 10000 (some 224))) = d108 p
  rw [sub6559, sub6662]
  rfl
theorem sub6664 (p : Pattern) : d109 (change p 10000 (some 224)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 224)) else d107 (change p 10000 (some 224))) = d109 p
  rw [sub6663, sub6662]
  rfl
theorem sub6665 (p : Pattern) : d110 (change p 10000 (some 224)) = d110 p := by
  change (if p 163 then d109 (change p 10000 (some 224)) else d105 (change p 10000 (some 224))) = d110 p
  rw [sub6664, sub6659]
  rfl
theorem sub6666 (p : Pattern) : d111 (change p 10000 (some 224)) = d111 p := by
  change (if p 162 then d110 (change p 10000 (some 224)) else d105 (change p 10000 (some 224))) = d111 p
  rw [sub6665, sub6659]
  rfl
theorem sub6667 (p : Pattern) : d112 (change p 10000 (some 224)) = d112 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d60 (change p 10000 (some 224))) = d112 p
  rw [sub6559, sub6613]
  rfl
theorem sub6668 (p : Pattern) : d113 (change p 10000 (some 224)) = d113 p := by
  change (if p 162 then d112 (change p 10000 (some 224)) else d110 (change p 10000 (some 224))) = d113 p
  rw [sub6667, sub6665]
  rfl
theorem sub6669 (p : Pattern) : d114 (change p 10000 (some 224)) = d114 p := by
  change (if p 161 then d113 (change p 10000 (some 224)) else d111 (change p 10000 (some 224))) = d114 p
  rw [sub6668, sub6666]
  rfl
theorem sub6670 (p : Pattern) : d3 (change p 10000 (some 224)) = d3 p := by
  rfl
theorem sub6671 (p : Pattern) : d115 (change p 10000 (some 224)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d3 (change p 10000 (some 224))) = d115 p
  rw [sub6559, sub6670]
  rfl
theorem sub6672 (p : Pattern) : d116 (change p 10000 (some 224)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 224)) else d3 (change p 10000 (some 224))) = d116 p
  rw [sub6671, sub6670]
  rfl
theorem sub6673 (p : Pattern) : d117 (change p 10000 (some 224)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d116 (change p 10000 (some 224))) = d117 p
  rw [sub6559, sub6672]
  rfl
theorem sub6674 (p : Pattern) : d118 (change p 10000 (some 224)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 224)) else d103 (change p 10000 (some 224))) = d118 p
  rw [sub6673, sub6657]
  rfl
theorem sub6675 (p : Pattern) : d7 (change p 10000 (some 224)) = d7 p := by
  rfl
theorem sub6676 (p : Pattern) : d119 (change p 10000 (some 224)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 224)) else d7 (change p 10000 (some 224))) = d119 p
  rw [sub6559, sub6675]
  rfl
theorem sub6677 (p : Pattern) : d120 (change p 10000 (some 224)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 224)) else d7 (change p 10000 (some 224))) = d120 p
  rw [sub6676, sub6675]
  rfl
theorem sub6678 (p : Pattern) : d121 (change p 10000 (some 224)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 224)) else d120 (change p 10000 (some 224))) = d121 p
  rw [sub6559, sub6677]
  rfl
theorem sub6679 (p : Pattern) : d122 (change p 10000 (some 224)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 224)) else d103 (change p 10000 (some 224))) = d122 p
  rw [sub6678, sub6657]
  rfl
theorem sub6680 (p : Pattern) : d123 (change p 10000 (some 224)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 224)) else d118 (change p 10000 (some 224))) = d123 p
  rw [sub6679, sub6674]
  rfl
theorem sub6681 (p : Pattern) : d124 (change p 10000 (some 224)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d103 (change p 10000 (some 224))) = d124 p
  rw [sub6559, sub6657]
  rfl
theorem sub6682 (p : Pattern) : d125 (change p 10000 (some 224)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d107 (change p 10000 (some 224))) = d125 p
  rw [sub6559, sub6662]
  rfl
theorem sub6683 (p : Pattern) : d126 (change p 10000 (some 224)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 224)) else d124 (change p 10000 (some 224))) = d126 p
  rw [sub6682, sub6681]
  rfl
theorem sub6684 (p : Pattern) : d127 (change p 10000 (some 224)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 224)) else d123 (change p 10000 (some 224))) = d127 p
  rw [sub6683, sub6680]
  rfl
theorem sub6685 (p : Pattern) : d128 (change p 10000 (some 224)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d70 (change p 10000 (some 224))) = d128 p
  rw [sub6559, sub6623]
  rfl
theorem sub6686 (p : Pattern) : d129 (change p 10000 (some 224)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 224)) else d126 (change p 10000 (some 224))) = d129 p
  rw [sub6685, sub6683]
  rfl
theorem sub6687 (p : Pattern) : d130 (change p 10000 (some 224)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 224)) else d127 (change p 10000 (some 224))) = d130 p
  rw [sub6686, sub6684]
  rfl
theorem sub6688 (p : Pattern) : d131 (change p 10000 (some 224)) = d131 p := by
  change (if p 160 then d130 (change p 10000 (some 224)) else d114 (change p 10000 (some 224))) = d131 p
  rw [sub6687, sub6669]
  rfl
theorem sub6689 (p : Pattern) : d132 (change p 10000 (some 224)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 224)) else d116 (change p 10000 (some 224))) = d132 p
  rw [sub6673, sub6672]
  rfl
theorem sub6690 (p : Pattern) : d133 (change p 10000 (some 224)) = d133 p := by
  change (if p 163 then d132 (change p 10000 (some 224)) else d105 (change p 10000 (some 224))) = d133 p
  rw [sub6689, sub6659]
  rfl
theorem sub6691 (p : Pattern) : d134 (change p 10000 (some 224)) = d134 p := by
  change (if p 163 then d60 (change p 10000 (some 224)) else d109 (change p 10000 (some 224))) = d134 p
  rw [sub6613, sub6664]
  rfl
theorem sub6692 (p : Pattern) : d135 (change p 10000 (some 224)) = d135 p := by
  change (if p 162 then d134 (change p 10000 (some 224)) else d133 (change p 10000 (some 224))) = d135 p
  rw [sub6691, sub6690]
  rfl
theorem sub6693 (p : Pattern) : d136 (change p 10000 (some 224)) = d136 p := by
  change (if p 163 then d62 (change p 10000 (some 224)) else d109 (change p 10000 (some 224))) = d136 p
  rw [sub6615, sub6664]
  rfl
theorem sub6694 (p : Pattern) : d137 (change p 10000 (some 224)) = d137 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d136 (change p 10000 (some 224))) = d137 p
  rw [sub6559, sub6693]
  rfl
theorem sub6695 (p : Pattern) : d138 (change p 10000 (some 224)) = d138 p := by
  change (if p 161 then d137 (change p 10000 (some 224)) else d135 (change p 10000 (some 224))) = d138 p
  rw [sub6694, sub6692]
  rfl
theorem sub6696 (p : Pattern) : d139 (change p 10000 (some 224)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 224)) else d116 (change p 10000 (some 224))) = d139 p
  rw [sub6559, sub6672]
  rfl
theorem sub6697 (p : Pattern) : d140 (change p 10000 (some 224)) = d140 p := by
  change (if p 163 then d139 (change p 10000 (some 224)) else d122 (change p 10000 (some 224))) = d140 p
  rw [sub6696, sub6679]
  rfl
theorem sub6698 (p : Pattern) : d141 (change p 10000 (some 224)) = d141 p := by
  change (if p 163 then d70 (change p 10000 (some 224)) else d125 (change p 10000 (some 224))) = d141 p
  rw [sub6623, sub6682]
  rfl
theorem sub6699 (p : Pattern) : d142 (change p 10000 (some 224)) = d142 p := by
  change (if p 162 then d141 (change p 10000 (some 224)) else d140 (change p 10000 (some 224))) = d142 p
  rw [sub6698, sub6697]
  rfl
theorem sub6700 (p : Pattern) : d143 (change p 10000 (some 224)) = d143 p := by
  change (if p 163 then d72 (change p 10000 (some 224)) else d125 (change p 10000 (some 224))) = d143 p
  rw [sub6625, sub6682]
  rfl
theorem sub6701 (p : Pattern) : d144 (change p 10000 (some 224)) = d144 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d143 (change p 10000 (some 224))) = d144 p
  rw [sub6559, sub6700]
  rfl
theorem sub6702 (p : Pattern) : d145 (change p 10000 (some 224)) = d145 p := by
  change (if p 161 then d144 (change p 10000 (some 224)) else d142 (change p 10000 (some 224))) = d145 p
  rw [sub6701, sub6699]
  rfl
theorem sub6703 (p : Pattern) : d146 (change p 10000 (some 224)) = d146 p := by
  change (if p 160 then d145 (change p 10000 (some 224)) else d138 (change p 10000 (some 224))) = d146 p
  rw [sub6702, sub6695]
  rfl
theorem sub6704 (p : Pattern) : d147 (change p 10000 (some 224)) = d147 p := by
  change (if p 141 then d146 (change p 10000 (some 224)) else d131 (change p 10000 (some 224))) = d147 p
  rw [sub6703, sub6688]
  rfl
theorem sub6705 (p : Pattern) : d148 (change p 10000 (some 224)) = d148 p := by
  change (if p 182 then d121 (change p 10000 (some 224)) else d120 (change p 10000 (some 224))) = d148 p
  rw [sub6678, sub6677]
  rfl
theorem sub6706 (p : Pattern) : d149 (change p 10000 (some 224)) = d149 p := by
  change (if p 163 then d148 (change p 10000 (some 224)) else d132 (change p 10000 (some 224))) = d149 p
  rw [sub6705, sub6689]
  rfl
theorem sub6707 (p : Pattern) : d150 (change p 10000 (some 224)) = d150 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d149 (change p 10000 (some 224))) = d150 p
  rw [sub6559, sub6706]
  rfl
theorem sub6708 (p : Pattern) : d151 (change p 10000 (some 224)) = d151 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d150 (change p 10000 (some 224))) = d151 p
  rw [sub6559, sub6707]
  rfl
theorem sub6709 (p : Pattern) : d152 (change p 10000 (some 224)) = d152 p := by
  change (if p 160 then d151 (change p 10000 (some 224)) else d114 (change p 10000 (some 224))) = d152 p
  rw [sub6708, sub6669]
  rfl
theorem sub6710 (p : Pattern) : d153 (change p 10000 (some 224)) = d153 p := by
  change (if p 163 then d12 (change p 10000 (some 224)) else d148 (change p 10000 (some 224))) = d153 p
  rw [sub6559, sub6705]
  rfl
theorem sub6711 (p : Pattern) : d154 (change p 10000 (some 224)) = d154 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d153 (change p 10000 (some 224))) = d154 p
  rw [sub6559, sub6710]
  rfl
theorem sub6712 (p : Pattern) : d155 (change p 10000 (some 224)) = d155 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d154 (change p 10000 (some 224))) = d155 p
  rw [sub6559, sub6711]
  rfl
theorem sub6713 (p : Pattern) : d156 (change p 10000 (some 224)) = d156 p := by
  change (if p 160 then d155 (change p 10000 (some 224)) else d138 (change p 10000 (some 224))) = d156 p
  rw [sub6712, sub6695]
  rfl
theorem sub6714 (p : Pattern) : d157 (change p 10000 (some 224)) = d157 p := by
  change (if p 141 then d156 (change p 10000 (some 224)) else d152 (change p 10000 (some 224))) = d157 p
  rw [sub6713, sub6709]
  rfl
theorem sub6715 (p : Pattern) : d158 (change p 10000 (some 224)) = d158 p := by
  change (if p 138 then d157 (change p 10000 (some 224)) else d147 (change p 10000 (some 224))) = d158 p
  rw [sub6714, sub6704]
  rfl
theorem sub6716 (p : Pattern) : d159 (change p 10000 (some 224)) = d159 p := by
  change (if p 162 then d12 (change p 10000 (some 224)) else d112 (change p 10000 (some 224))) = d159 p
  rw [sub6559, sub6667]
  rfl
theorem sub6717 (p : Pattern) : d160 (change p 10000 (some 224)) = d160 p := by
  change (if p 161 then d12 (change p 10000 (some 224)) else d159 (change p 10000 (some 224))) = d160 p
  rw [sub6559, sub6716]
  rfl
theorem sub6718 (p : Pattern) : d161 (change p 10000 (some 224)) = d161 p := by
  change (if p 160 then d12 (change p 10000 (some 224)) else d160 (change p 10000 (some 224))) = d161 p
  rw [sub6559, sub6717]
  rfl
theorem sub6719 (p : Pattern) : d162 (change p 10000 (some 224)) = d162 p := by
  change (if p 141 then d12 (change p 10000 (some 224)) else d161 (change p 10000 (some 224))) = d162 p
  rw [sub6559, sub6718]
  rfl
end NetHack.Sokoban22Refined85
