/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions43
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6600 (pattern : Twelve) : d106 (change pattern 12 1) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 12 1) else d97 (change pattern 12 1)) = d106 pattern
  rw [s6599, s6591]
  rfl
theorem s6601 (pattern : Twelve) : d45 (change pattern 12 1) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d1 (change pattern 12 1)) = d45 pattern
  rw [s6529, s6513]
  rfl
theorem s6602 (pattern : Twelve) : d65 (change pattern 12 1) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 12 1) else d30 (change pattern 12 1)) = d65 pattern
  rw [s6601, s6534]
  rfl
theorem s6603 (pattern : Twelve) : d85 (change pattern 12 1) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 12 1) else d56 (change pattern 12 1)) = d85 pattern
  rw [s6602, s6559]
  rfl
theorem s6604 (pattern : Twelve) : d66 (change pattern 12 1) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 12 1) else d30 (change pattern 12 1)) = d66 pattern
  rw [s6573, s6534]
  rfl
theorem s6605 (pattern : Twelve) : d86 (change pattern 12 1) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 12 1) else d66 (change pattern 12 1)) = d86 pattern
  rw [s6597, s6604]
  rfl
theorem s6606 (pattern : Twelve) : d99 (change pattern 12 1) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 12 1) else d85 (change pattern 12 1)) = d99 pattern
  rw [s6605, s6603]
  rfl
theorem s6607 (pattern : Twelve) : d107 (change pattern 12 1) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 12 1) else d97 (change pattern 12 1)) = d107 pattern
  rw [s6606, s6591]
  rfl
theorem s6608 (pattern : Twelve) : d112 (change pattern 12 1) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 12 1) else d106 (change pattern 12 1)) = d112 pattern
  rw [s6607, s6600]
  rfl
theorem s6609 (pattern : Twelve) : d46 (change pattern 12 1) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d1 (change pattern 12 1)) = d46 pattern
  rw [s6522, s6513]
  rfl
theorem s6610 (pattern : Twelve) : d67 (change pattern 12 1) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 12 1) else d30 (change pattern 12 1)) = d67 pattern
  rw [s6609, s6534]
  rfl
theorem s6611 (pattern : Twelve) : d87 (change pattern 12 1) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 12 1) else d30 (change pattern 12 1)) = d87 pattern
  rw [s6610, s6534]
  rfl
theorem s6612 (pattern : Twelve) : d68 (change pattern 12 1) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 12 1) else d30 (change pattern 12 1)) = d68 pattern
  rw [s6572, s6534]
  rfl
theorem s6613 (pattern : Twelve) : d88 (change pattern 12 1) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 12 1) else d68 (change pattern 12 1)) = d88 pattern
  rw [s6597, s6612]
  rfl
theorem s6614 (pattern : Twelve) : d100 (change pattern 12 1) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 12 1) else d87 (change pattern 12 1)) = d100 pattern
  rw [s6613, s6611]
  rfl
theorem s6615 (pattern : Twelve) : d47 (change pattern 12 1) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d3 (change pattern 12 1)) = d47 pattern
  rw [s6529, s6522]
  rfl
theorem s6616 (pattern : Twelve) : d69 (change pattern 12 1) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 12 1) else d38 (change pattern 12 1)) = d69 pattern
  rw [s6615, s6572]
  rfl
theorem s6617 (pattern : Twelve) : d89 (change pattern 12 1) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 12 1) else d59 (change pattern 12 1)) = d89 pattern
  rw [s6616, s6574]
  rfl
theorem s6618 (pattern : Twelve) : d48 (change pattern 12 1) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d4 (change pattern 12 1)) = d48 pattern
  rw [s6529, s6537]
  rfl
theorem s6619 (pattern : Twelve) : d70 (change pattern 12 1) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 12 1) else d38 (change pattern 12 1)) = d70 pattern
  rw [s6618, s6572]
  rfl
theorem s6620 (pattern : Twelve) : d49 (change pattern 12 1) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d24 (change pattern 12 1)) = d49 pattern
  rw [s6529, s6579]
  rfl
theorem s6621 (pattern : Twelve) : d71 (change pattern 12 1) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 12 1) else d41 (change pattern 12 1)) = d71 pattern
  rw [s6620, s6580]
  rfl
theorem s6622 (pattern : Twelve) : d90 (change pattern 12 1) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 12 1) else d70 (change pattern 12 1)) = d90 pattern
  rw [s6621, s6619]
  rfl
theorem s6623 (pattern : Twelve) : d101 (change pattern 12 1) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 12 1) else d89 (change pattern 12 1)) = d101 pattern
  rw [s6622, s6617]
  rfl
theorem s6624 (pattern : Twelve) : d108 (change pattern 12 1) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 12 1) else d100 (change pattern 12 1)) = d108 pattern
  rw [s6623, s6614]
  rfl
theorem s6625 (pattern : Twelve) : d109 (change pattern 12 1) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d99 (change pattern 12 1)) = d109 pattern
  rw [s6529, s6606]
  rfl
theorem s6626 (pattern : Twelve) : d113 (change pattern 12 1) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 12 1) else d108 (change pattern 12 1)) = d113 pattern
  rw [s6625, s6624]
  rfl
theorem s6627 (pattern : Twelve) : d115 (change pattern 12 1) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 12 1) else d112 (change pattern 12 1)) = d115 pattern
  rw [s6626, s6608]
  rfl
theorem s6628 (pattern : Twelve) : d116 (change pattern 12 1) = d116 pattern := by
  change (if pattern.g then d115 (change pattern 12 1) else d114 (change pattern 12 1)) = d116 pattern
  rw [s6627, s6590]
  rfl
theorem s6629 (pattern : Twelve) : d120 (change pattern 12 1) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 12 1) else d17 (change pattern 12 1)) = d120 pattern
  rw [s6582, s6516]
  rfl
theorem s6630 (pattern : Twelve) : d129 (change pattern 12 1) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 12 1) else d120 (change pattern 12 1)) = d129 pattern
  rw [s6530, s6629]
  rfl
theorem s6631 (pattern : Twelve) : d136 (change pattern 12 1) = d136 pattern := by
  change (if pattern.f then d129 (change pattern 12 1) else d0 (change pattern 12 1)) = d136 pattern
  rw [s6630, s6512]
  rfl
theorem s6632 (pattern : Twelve) : d144 (change pattern 12 1) = d144 pattern := by
  change (if pattern.e then d136 (change pattern 12 1) else d72 (change pattern 12 1)) = d144 pattern
  rw [s6631, s6519]
  rfl
theorem s6633 (pattern : Twelve) : d121 (change pattern 12 1) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 12 1) else d0 (change pattern 12 1)) = d121 pattern
  rw [s6550, s6512]
  rfl
theorem s6634 (pattern : Twelve) : d130 (change pattern 12 1) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 12 1) else d121 (change pattern 12 1)) = d130 pattern
  rw [s6560, s6633]
  rfl
theorem s6635 (pattern : Twelve) : d137 (change pattern 12 1) = d137 pattern := by
  change (if pattern.f then d130 (change pattern 12 1) else d52 (change pattern 12 1)) = d137 pattern
  rw [s6634, s6541]
  rfl
theorem s6636 (pattern : Twelve) : d138 (change pattern 12 1) = d138 pattern := by
  change (if pattern.f then d129 (change pattern 12 1) else d56 (change pattern 12 1)) = d138 pattern
  rw [s6630, s6559]
  rfl
theorem s6637 (pattern : Twelve) : d145 (change pattern 12 1) = d145 pattern := by
  change (if pattern.e then d138 (change pattern 12 1) else d137 (change pattern 12 1)) = d145 pattern
  rw [s6636, s6635]
  rfl
theorem s6638 (pattern : Twelve) : d149 (change pattern 12 1) = d149 pattern := by
  change (if pattern.j then d145 (change pattern 12 1) else d144 (change pattern 12 1)) = d149 pattern
  rw [s6637, s6632]
  rfl
theorem s6639 (pattern : Twelve) : d139 (change pattern 12 1) = d139 pattern := by
  change (if pattern.f then d130 (change pattern 12 1) else d56 (change pattern 12 1)) = d139 pattern
  rw [s6634, s6559]
  rfl
theorem s6640 (pattern : Twelve) : d146 (change pattern 12 1) = d146 pattern := by
  change (if pattern.e then d138 (change pattern 12 1) else d139 (change pattern 12 1)) = d146 pattern
  rw [s6636, s6639]
  rfl
theorem s6641 (pattern : Twelve) : d150 (change pattern 12 1) = d150 pattern := by
  change (if pattern.j then d146 (change pattern 12 1) else d144 (change pattern 12 1)) = d150 pattern
  rw [s6640, s6632]
  rfl
theorem s6642 (pattern : Twelve) : d153 (change pattern 12 1) = d153 pattern := by
  change (if pattern.d then d150 (change pattern 12 1) else d149 (change pattern 12 1)) = d153 pattern
  rw [s6641, s6638]
  rfl
theorem s6643 (pattern : Twelve) : d122 (change pattern 12 1) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 12 1) else d17 (change pattern 12 1)) = d122 pattern
  rw [s6537, s6516]
  rfl
theorem s6644 (pattern : Twelve) : d131 (change pattern 12 1) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 12 1) else d121 (change pattern 12 1)) = d131 pattern
  rw [s6643, s6633]
  rfl
theorem s6645 (pattern : Twelve) : d140 (change pattern 12 1) = d140 pattern := by
  change (if pattern.f then d131 (change pattern 12 1) else d30 (change pattern 12 1)) = d140 pattern
  rw [s6644, s6534]
  rfl
theorem s6646 (pattern : Twelve) : d123 (change pattern 12 1) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d0 (change pattern 12 1)) = d123 pattern
  rw [s6522, s6512]
  rfl
theorem s6647 (pattern : Twelve) : d132 (change pattern 12 1) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 12 1) else d30 (change pattern 12 1)) = d132 pattern
  rw [s6646, s6534]
  rfl
theorem s6648 (pattern : Twelve) : d141 (change pattern 12 1) = d141 pattern := by
  change (if pattern.f then d129 (change pattern 12 1) else d132 (change pattern 12 1)) = d141 pattern
  rw [s6630, s6647]
  rfl
theorem s6649 (pattern : Twelve) : d147 (change pattern 12 1) = d147 pattern := by
  change (if pattern.e then d141 (change pattern 12 1) else d140 (change pattern 12 1)) = d147 pattern
  rw [s6648, s6645]
  rfl
theorem s6650 (pattern : Twelve) : d118 (change pattern 12 1) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 1) else d5 (change pattern 12 1)) = d118 pattern
  rw [s6542, s6535]
  rfl
theorem s6651 (pattern : Twelve) : d124 (change pattern 12 1) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 12 1) else d2 (change pattern 12 1)) = d124 pattern
  rw [s6650, s6520]
  rfl
theorem s6652 (pattern : Twelve) : d117 (change pattern 12 1) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 1) else d3 (change pattern 12 1)) = d117 pattern
  rw [s6537, s6522]
  rfl
theorem s6653 (pattern : Twelve) : d119 (change pattern 12 1) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 1) else d3 (change pattern 12 1)) = d119 pattern
  rw [s6652, s6522]
  rfl
theorem s6654 (pattern : Twelve) : d125 (change pattern 12 1) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d119 (change pattern 12 1)) = d125 pattern
  rw [s6529, s6653]
  rfl
theorem s6655 (pattern : Twelve) : d133 (change pattern 12 1) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 12 1) else d124 (change pattern 12 1)) = d133 pattern
  rw [s6654, s6651]
  rfl
theorem s6656 (pattern : Twelve) : d142 (change pattern 12 1) = d142 pattern := by
  change (if pattern.f then d133 (change pattern 12 1) else d59 (change pattern 12 1)) = d142 pattern
  rw [s6655, s6574]
  rfl
theorem s6657 (pattern : Twelve) : d126 (change pattern 12 1) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 12 1) else d2 (change pattern 12 1)) = d126 pattern
  rw [s6535, s6520]
  rfl
theorem s6658 (pattern : Twelve) : d134 (change pattern 12 1) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 12 1) else d126 (change pattern 12 1)) = d134 pattern
  rw [s6615, s6657]
  rfl
theorem s6659 (pattern : Twelve) : d127 (change pattern 12 1) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 12 1) else d23 (change pattern 12 1)) = d127 pattern
  rw [s6547, s6550]
  rfl
theorem s6660 (pattern : Twelve) : d128 (change pattern 12 1) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d20 (change pattern 12 1)) = d128 pattern
  rw [s6529, s6539]
  rfl
theorem s6661 (pattern : Twelve) : d135 (change pattern 12 1) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 12 1) else d127 (change pattern 12 1)) = d135 pattern
  rw [s6660, s6659]
  rfl
theorem s6662 (pattern : Twelve) : d143 (change pattern 12 1) = d143 pattern := by
  change (if pattern.f then d135 (change pattern 12 1) else d134 (change pattern 12 1)) = d143 pattern
  rw [s6661, s6658]
  rfl
theorem s6663 (pattern : Twelve) : d148 (change pattern 12 1) = d148 pattern := by
  change (if pattern.e then d143 (change pattern 12 1) else d142 (change pattern 12 1)) = d148 pattern
  rw [s6662, s6656]
  rfl
theorem s6664 (pattern : Twelve) : d151 (change pattern 12 1) = d151 pattern := by
  change (if pattern.j then d148 (change pattern 12 1) else d147 (change pattern 12 1)) = d151 pattern
  rw [s6663, s6649]
  rfl
theorem s6665 (pattern : Twelve) : d152 (change pattern 12 1) = d152 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d146 (change pattern 12 1)) = d152 pattern
  rw [s6529, s6640]
  rfl
theorem s6666 (pattern : Twelve) : d154 (change pattern 12 1) = d154 pattern := by
  change (if pattern.d then d152 (change pattern 12 1) else d151 (change pattern 12 1)) = d154 pattern
  rw [s6665, s6664]
  rfl
theorem s6667 (pattern : Twelve) : d155 (change pattern 12 1) = d155 pattern := by
  change (if pattern.c then d154 (change pattern 12 1) else d153 (change pattern 12 1)) = d155 pattern
  rw [s6666, s6642]
  rfl
theorem s6668 (pattern : Twelve) : d778 (change pattern 12 1) = d778 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d2 (change pattern 12 1)) = d778 pattern
  rw [s6522, s6520]
  rfl
theorem s6669 (pattern : Twelve) : d779 (change pattern 12 1) = d779 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d23 (change pattern 12 1)) = d779 pattern
  rw [s6522, s6550]
  rfl
theorem s6670 (pattern : Twelve) : d782 (change pattern 12 1) = d782 pattern := by
  change (if pattern.h then d779 (change pattern 12 1) else d778 (change pattern 12 1)) = d782 pattern
  rw [s6669, s6668]
  rfl
theorem s6671 (pattern : Twelve) : d788 (change pattern 12 1) = d788 pattern := by
  change (if pattern.f then d782 (change pattern 12 1) else d2 (change pattern 12 1)) = d788 pattern
  rw [s6670, s6520]
  rfl
theorem s6672 (pattern : Twelve) : d789 (change pattern 12 1) = d789 pattern := by
  change (if pattern.f then d61 (change pattern 12 1) else d38 (change pattern 12 1)) = d789 pattern
  rw [s6584, s6572]
  rfl
theorem s6673 (pattern : Twelve) : d794 (change pattern 12 1) = d794 pattern := by
  change (if pattern.e then d789 (change pattern 12 1) else d788 (change pattern 12 1)) = d794 pattern
  rw [s6672, s6671]
  rfl
theorem s6674 (pattern : Twelve) : d783 (change pattern 12 1) = d783 pattern := by
  change (if pattern.h then d44 (change pattern 12 1) else d38 (change pattern 12 1)) = d783 pattern
  rw [s6595, s6572]
  rfl
theorem s6675 (pattern : Twelve) : d790 (change pattern 12 1) = d790 pattern := by
  change (if pattern.f then d69 (change pattern 12 1) else d783 (change pattern 12 1)) = d790 pattern
  rw [s6616, s6674]
  rfl
theorem s6676 (pattern : Twelve) : d795 (change pattern 12 1) = d795 pattern := by
  change (if pattern.e then d90 (change pattern 12 1) else d790 (change pattern 12 1)) = d795 pattern
  rw [s6622, s6675]
  rfl
theorem s6677 (pattern : Twelve) : d798 (change pattern 12 1) = d798 pattern := by
  change (if pattern.j then d795 (change pattern 12 1) else d794 (change pattern 12 1)) = d798 pattern
  rw [s6676, s6673]
  rfl
theorem s6678 (pattern : Twelve) : d799 (change pattern 12 1) = d799 pattern := by
  change (if pattern.j then d101 (change pattern 12 1) else d794 (change pattern 12 1)) = d799 pattern
  rw [s6623, s6673]
  rfl
theorem s6679 (pattern : Twelve) : d802 (change pattern 12 1) = d802 pattern := by
  change (if pattern.d then d799 (change pattern 12 1) else d798 (change pattern 12 1)) = d802 pattern
  rw [s6678, s6677]
  rfl
theorem s6680 (pattern : Twelve) : d780 (change pattern 12 1) = d780 pattern := by
  change (if pattern.i then d5 (change pattern 12 1) else d3 (change pattern 12 1)) = d780 pattern
  rw [s6535, s6522]
  rfl
theorem s6681 (pattern : Twelve) : d784 (change pattern 12 1) = d784 pattern := by
  change (if pattern.h then d780 (change pattern 12 1) else d38 (change pattern 12 1)) = d784 pattern
  rw [s6680, s6572]
  rfl
theorem s6682 (pattern : Twelve) : d791 (change pattern 12 1) = d791 pattern := by
  change (if pattern.f then d784 (change pattern 12 1) else d38 (change pattern 12 1)) = d791 pattern
  rw [s6681, s6572]
  rfl
theorem s6683 (pattern : Twelve) : d796 (change pattern 12 1) = d796 pattern := by
  change (if pattern.e then d90 (change pattern 12 1) else d791 (change pattern 12 1)) = d796 pattern
  rw [s6622, s6682]
  rfl
theorem s6684 (pattern : Twelve) : d781 (change pattern 12 1) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d5 (change pattern 12 1)) = d781 pattern
  rw [s6529, s6535]
  rfl
theorem s6685 (pattern : Twelve) : d785 (change pattern 12 1) = d785 pattern := by
  change (if pattern.h then d781 (change pattern 12 1) else d48 (change pattern 12 1)) = d785 pattern
  rw [s6684, s6618]
  rfl
theorem s6686 (pattern : Twelve) : d792 (change pattern 12 1) = d792 pattern := by
  change (if pattern.f then d785 (change pattern 12 1) else d48 (change pattern 12 1)) = d792 pattern
  rw [s6685, s6618]
  rfl
theorem s6687 (pattern : Twelve) : d786 (change pattern 12 1) = d786 pattern := by
  change (if pattern.h then d6 (change pattern 12 1) else d48 (change pattern 12 1)) = d786 pattern
  rw [s6529, s6618]
  rfl
theorem s6688 (pattern : Twelve) : d787 (change pattern 12 1) = d787 pattern := by
  change (if pattern.h then d6 (change pattern 12 1) else d49 (change pattern 12 1)) = d787 pattern
  rw [s6529, s6620]
  rfl
theorem s6689 (pattern : Twelve) : d793 (change pattern 12 1) = d793 pattern := by
  change (if pattern.f then d787 (change pattern 12 1) else d786 (change pattern 12 1)) = d793 pattern
  rw [s6688, s6687]
  rfl
theorem s6690 (pattern : Twelve) : d797 (change pattern 12 1) = d797 pattern := by
  change (if pattern.e then d793 (change pattern 12 1) else d792 (change pattern 12 1)) = d797 pattern
  rw [s6689, s6686]
  rfl
theorem s6691 (pattern : Twelve) : d800 (change pattern 12 1) = d800 pattern := by
  change (if pattern.j then d797 (change pattern 12 1) else d796 (change pattern 12 1)) = d800 pattern
  rw [s6690, s6683]
  rfl
theorem s6692 (pattern : Twelve) : d801 (change pattern 12 1) = d801 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d101 (change pattern 12 1)) = d801 pattern
  rw [s6529, s6623]
  rfl
theorem s6693 (pattern : Twelve) : d803 (change pattern 12 1) = d803 pattern := by
  change (if pattern.d then d801 (change pattern 12 1) else d800 (change pattern 12 1)) = d803 pattern
  rw [s6692, s6691]
  rfl
theorem s6694 (pattern : Twelve) : d804 (change pattern 12 1) = d804 pattern := by
  change (if pattern.c then d803 (change pattern 12 1) else d802 (change pattern 12 1)) = d804 pattern
  rw [s6693, s6679]
  rfl
theorem s6695 (pattern : Twelve) : d805 (change pattern 12 1) = d805 pattern := by
  change (if pattern.g then d804 (change pattern 12 1) else d155 (change pattern 12 1)) = d805 pattern
  rw [s6694, s6667]
  rfl
theorem s6696 (pattern : Twelve) : d806 (change pattern 12 1) = d806 pattern := by
  change (if pattern.a then d805 (change pattern 12 1) else d116 (change pattern 12 1)) = d806 pattern
  rw [s6695, s6628]
  rfl
theorem s6697 (pattern : Twelve) : d814 (change pattern 12 1) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 1) else d7 (change pattern 12 1)) = d814 pattern
  rw [s6513, s6515]
  rfl
theorem s6698 (pattern : Twelve) : d816 (change pattern 12 1) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 1) else d814 (change pattern 12 1)) = d816 pattern
  rw [s6513, s6697]
  rfl
theorem s6699 (pattern : Twelve) : d824 (change pattern 12 1) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 1) else d27 (change pattern 12 1)) = d824 pattern
  rw [s6698, s6517]
  rfl
theorem s6700 (pattern : Twelve) : d838 (change pattern 12 1) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 12 1) else d0 (change pattern 12 1)) = d838 pattern
  rw [s6699, s6512]
  rfl
theorem s6701 (pattern : Twelve) : d817 (change pattern 12 1) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 1) else d19 (change pattern 12 1)) = d817 pattern
  rw [s6582, s6528]
  rfl
theorem s6702 (pattern : Twelve) : d825 (change pattern 12 1) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 1) else d817 (change pattern 12 1)) = d825 pattern
  rw [s6583, s6701]
  rfl
theorem s6703 (pattern : Twelve) : d839 (change pattern 12 1) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d17 (change pattern 12 1)) = d839 pattern
  rw [s6702, s6516]
  rfl
theorem s6704 (pattern : Twelve) : d853 (change pattern 12 1) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 12 1) else d838 (change pattern 12 1)) = d853 pattern
  rw [s6703, s6700]
  rfl
theorem s6705 (pattern : Twelve) : d818 (change pattern 12 1) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d814 (change pattern 12 1)) = d818 pattern
  rw [s6529, s6697]
  rfl
theorem s6706 (pattern : Twelve) : d826 (change pattern 12 1) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 12 1) else d34 (change pattern 12 1)) = d826 pattern
  rw [s6705, s6551]
  rfl
theorem s6707 (pattern : Twelve) : d840 (change pattern 12 1) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 12 1) else d56 (change pattern 12 1)) = d840 pattern
  rw [s6706, s6559]
  rfl
theorem s6708 (pattern : Twelve) : d827 (change pattern 12 1) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 12 1) else d34 (change pattern 12 1)) = d827 pattern
  rw [s6560, s6551]
  rfl
theorem s6709 (pattern : Twelve) : d841 (change pattern 12 1) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d827 (change pattern 12 1)) = d841 pattern
  rw [s6702, s6708]
  rfl
theorem s6710 (pattern : Twelve) : d854 (change pattern 12 1) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 12 1) else d840 (change pattern 12 1)) = d854 pattern
  rw [s6709, s6707]
  rfl
theorem s6711 (pattern : Twelve) : d861 (change pattern 12 1) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 12 1) else d853 (change pattern 12 1)) = d861 pattern
  rw [s6710, s6704]
  rfl
theorem s6712 (pattern : Twelve) : d819 (change pattern 12 1) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 12 1) else d814 (change pattern 12 1)) = d819 pattern
  rw [s6522, s6697]
  rfl
theorem s6713 (pattern : Twelve) : d828 (change pattern 12 1) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 12 1) else d34 (change pattern 12 1)) = d828 pattern
  rw [s6712, s6551]
  rfl
theorem s6714 (pattern : Twelve) : d842 (change pattern 12 1) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 12 1) else d30 (change pattern 12 1)) = d842 pattern
  rw [s6713, s6534]
  rfl
theorem s6715 (pattern : Twelve) : d843 (change pattern 12 1) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d34 (change pattern 12 1)) = d843 pattern
  rw [s6702, s6551]
  rfl
theorem s6716 (pattern : Twelve) : d855 (change pattern 12 1) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 12 1) else d842 (change pattern 12 1)) = d855 pattern
  rw [s6715, s6714]
  rfl
theorem s6717 (pattern : Twelve) : d815 (change pattern 12 1) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 1) else d9 (change pattern 12 1)) = d815 pattern
  rw [s6522, s6523]
  rfl
theorem s6718 (pattern : Twelve) : d820 (change pattern 12 1) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d815 (change pattern 12 1)) = d820 pattern
  rw [s6529, s6717]
  rfl
theorem s6719 (pattern : Twelve) : d829 (change pattern 12 1) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 12 1) else d41 (change pattern 12 1)) = d829 pattern
  rw [s6718, s6580]
  rfl
theorem s6720 (pattern : Twelve) : d844 (change pattern 12 1) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 12 1) else d59 (change pattern 12 1)) = d844 pattern
  rw [s6719, s6574]
  rfl
theorem s6721 (pattern : Twelve) : d830 (change pattern 12 1) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 12 1) else d41 (change pattern 12 1)) = d830 pattern
  rw [s6575, s6580]
  rfl
theorem s6722 (pattern : Twelve) : d821 (change pattern 12 1) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 1) else d25 (change pattern 12 1)) = d821 pattern
  rw [s6543, s6582]
  rfl
theorem s6723 (pattern : Twelve) : d822 (change pattern 12 1) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 12 1) else d21 (change pattern 12 1)) = d822 pattern
  rw [s6529, s6543]
  rfl
theorem s6724 (pattern : Twelve) : d831 (change pattern 12 1) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 12 1) else d821 (change pattern 12 1)) = d831 pattern
  rw [s6723, s6722]
  rfl
theorem s6725 (pattern : Twelve) : d845 (change pattern 12 1) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 12 1) else d830 (change pattern 12 1)) = d845 pattern
  rw [s6724, s6721]
  rfl
theorem s6726 (pattern : Twelve) : d856 (change pattern 12 1) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 12 1) else d844 (change pattern 12 1)) = d856 pattern
  rw [s6725, s6720]
  rfl
theorem s6727 (pattern : Twelve) : d862 (change pattern 12 1) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 12 1) else d855 (change pattern 12 1)) = d862 pattern
  rw [s6726, s6716]
  rfl
theorem s6728 (pattern : Twelve) : d863 (change pattern 12 1) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 12 1) else d854 (change pattern 12 1)) = d863 pattern
  rw [s6529, s6710]
  rfl
theorem s6729 (pattern : Twelve) : d867 (change pattern 12 1) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 12 1) else d862 (change pattern 12 1)) = d867 pattern
  rw [s6728, s6727]
  rfl
theorem s6730 (pattern : Twelve) : d869 (change pattern 12 1) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 12 1) else d861 (change pattern 12 1)) = d869 pattern
  rw [s6729, s6711]
  rfl
theorem s6731 (pattern : Twelve) : d823 (change pattern 12 1) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 12 1) else d17 (change pattern 12 1)) = d823 pattern
  rw [s6520, s6516]
  rfl
theorem s6732 (pattern : Twelve) : d846 (change pattern 12 1) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d823 (change pattern 12 1)) = d846 pattern
  rw [s6702, s6731]
  rfl
theorem s6733 (pattern : Twelve) : d857 (change pattern 12 1) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 12 1) else d838 (change pattern 12 1)) = d857 pattern
  rw [s6732, s6700]
  rfl
theorem s6734 (pattern : Twelve) : d832 (change pattern 12 1) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 12 1) else d34 (change pattern 12 1)) = d832 pattern
  rw [s6601, s6551]
  rfl
theorem s6735 (pattern : Twelve) : d847 (change pattern 12 1) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 12 1) else d56 (change pattern 12 1)) = d847 pattern
  rw [s6734, s6559]
  rfl
theorem s6736 (pattern : Twelve) : d833 (change pattern 12 1) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 12 1) else d34 (change pattern 12 1)) = d833 pattern
  rw [s6573, s6551]
  rfl
theorem s6737 (pattern : Twelve) : d848 (change pattern 12 1) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d833 (change pattern 12 1)) = d848 pattern
  rw [s6702, s6736]
  rfl
theorem s6738 (pattern : Twelve) : d858 (change pattern 12 1) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 12 1) else d847 (change pattern 12 1)) = d858 pattern
  rw [s6737, s6735]
  rfl
theorem s6739 (pattern : Twelve) : d864 (change pattern 12 1) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 12 1) else d857 (change pattern 12 1)) = d864 pattern
  rw [s6738, s6733]
  rfl
theorem s6740 (pattern : Twelve) : d834 (change pattern 12 1) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 12 1) else d34 (change pattern 12 1)) = d834 pattern
  rw [s6609, s6551]
  rfl
theorem s6741 (pattern : Twelve) : d849 (change pattern 12 1) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 12 1) else d30 (change pattern 12 1)) = d849 pattern
  rw [s6740, s6534]
  rfl
theorem s6742 (pattern : Twelve) : d835 (change pattern 12 1) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 12 1) else d34 (change pattern 12 1)) = d835 pattern
  rw [s6572, s6551]
  rfl
theorem s6743 (pattern : Twelve) : d850 (change pattern 12 1) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 12 1) else d835 (change pattern 12 1)) = d850 pattern
  rw [s6702, s6742]
  rfl
theorem s6744 (pattern : Twelve) : d859 (change pattern 12 1) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 12 1) else d849 (change pattern 12 1)) = d859 pattern
  rw [s6743, s6741]
  rfl
theorem s6745 (pattern : Twelve) : d836 (change pattern 12 1) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 12 1) else d41 (change pattern 12 1)) = d836 pattern
  rw [s6615, s6580]
  rfl
theorem s6746 (pattern : Twelve) : d851 (change pattern 12 1) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 12 1) else d59 (change pattern 12 1)) = d851 pattern
  rw [s6745, s6574]
  rfl
theorem s6747 (pattern : Twelve) : d837 (change pattern 12 1) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 12 1) else d41 (change pattern 12 1)) = d837 pattern
  rw [s6618, s6580]
  rfl
theorem s6748 (pattern : Twelve) : d852 (change pattern 12 1) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 12 1) else d837 (change pattern 12 1)) = d852 pattern
  rw [s6724, s6747]
  rfl
theorem s6749 (pattern : Twelve) : d860 (change pattern 12 1) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 12 1) else d851 (change pattern 12 1)) = d860 pattern
  rw [s6748, s6746]
  rfl
end NetHack.Sokoban21.Diagram
