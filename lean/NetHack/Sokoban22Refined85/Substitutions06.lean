/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub720 (p : Pattern) : d64 (change p 48 (some 49)) = d64 p := by
  change (if p 162 then d63 (change p 48 (some 49)) else d61 (change p 48 (some 49))) = d64 p
  rw [sub719, sub717]
  rfl
theorem sub721 (p : Pattern) : d65 (change p 48 (some 49)) = d65 p := by
  change (if p 161 then d64 (change p 48 (some 49)) else d56 (change p 48 (some 49))) = d65 p
  rw [sub720, sub711]
  rfl
theorem sub722 (p : Pattern) : d66 (change p 48 (some 49)) = d66 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d31 (change p 48 (some 49))) = d66 p
  rw [sub662, sub684]
  rfl
theorem sub723 (p : Pattern) : d67 (change p 48 (some 49)) = d67 p := by
  change (if p 163 then d66 (change p 48 (some 49)) else d37 (change p 48 (some 49))) = d67 p
  rw [sub722, sub691]
  rfl
theorem sub724 (p : Pattern) : d68 (change p 48 (some 49)) = d68 p := by
  change (if p 163 then d48 (change p 48 (some 49)) else d43 (change p 48 (some 49))) = d68 p
  rw [sub703, sub698]
  rfl
theorem sub725 (p : Pattern) : d69 (change p 48 (some 49)) = d69 p := by
  change (if p 162 then d68 (change p 48 (some 49)) else d67 (change p 48 (some 49))) = d69 p
  rw [sub724, sub723]
  rfl
theorem sub726 (p : Pattern) : d70 (change p 48 (some 49)) = d70 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d58 (change p 48 (some 49))) = d70 p
  rw [sub662, sub714]
  rfl
theorem sub727 (p : Pattern) : d71 (change p 48 (some 49)) = d71 p := by
  change (if p 163 then d70 (change p 48 (some 49)) else d43 (change p 48 (some 49))) = d71 p
  rw [sub726, sub698]
  rfl
theorem sub728 (p : Pattern) : d72 (change p 48 (some 49)) = d72 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d40 (change p 48 (some 49))) = d72 p
  rw [sub662, sub695]
  rfl
theorem sub729 (p : Pattern) : d73 (change p 48 (some 49)) = d73 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d72 (change p 48 (some 49))) = d73 p
  rw [sub662, sub728]
  rfl
theorem sub730 (p : Pattern) : d74 (change p 48 (some 49)) = d74 p := by
  change (if p 162 then d73 (change p 48 (some 49)) else d71 (change p 48 (some 49))) = d74 p
  rw [sub729, sub727]
  rfl
theorem sub731 (p : Pattern) : d75 (change p 48 (some 49)) = d75 p := by
  change (if p 161 then d74 (change p 48 (some 49)) else d69 (change p 48 (some 49))) = d75 p
  rw [sub730, sub725]
  rfl
theorem sub732 (p : Pattern) : d76 (change p 48 (some 49)) = d76 p := by
  change (if p 160 then d75 (change p 48 (some 49)) else d65 (change p 48 (some 49))) = d76 p
  rw [sub731, sub721]
  rfl
theorem sub733 (p : Pattern) : d77 (change p 48 (some 49)) = d77 p := by
  change (if p 141 then d76 (change p 48 (some 49)) else d52 (change p 48 (some 49))) = d77 p
  rw [sub732, sub707]
  rfl
theorem sub734 (p : Pattern) : d78 (change p 48 (some 49)) = d78 p := by
  change (if p 182 then d36 (change p 48 (some 49)) else d35 (change p 48 (some 49))) = d78 p
  rw [sub690, sub689]
  rfl
theorem sub735 (p : Pattern) : d79 (change p 48 (some 49)) = d79 p := by
  change (if p 163 then d78 (change p 48 (some 49)) else d53 (change p 48 (some 49))) = d79 p
  rw [sub734, sub708]
  rfl
theorem sub736 (p : Pattern) : d80 (change p 48 (some 49)) = d80 p := by
  change (if p 162 then d63 (change p 48 (some 49)) else d79 (change p 48 (some 49))) = d80 p
  rw [sub719, sub735]
  rfl
theorem sub737 (p : Pattern) : d81 (change p 48 (some 49)) = d81 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d80 (change p 48 (some 49))) = d81 p
  rw [sub662, sub736]
  rfl
theorem sub738 (p : Pattern) : d82 (change p 48 (some 49)) = d82 p := by
  change (if p 160 then d81 (change p 48 (some 49)) else d29 (change p 48 (some 49))) = d82 p
  rw [sub737, sub681]
  rfl
theorem sub739 (p : Pattern) : d83 (change p 48 (some 49)) = d83 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d78 (change p 48 (some 49))) = d83 p
  rw [sub662, sub734]
  rfl
theorem sub740 (p : Pattern) : d84 (change p 48 (some 49)) = d84 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d83 (change p 48 (some 49))) = d84 p
  rw [sub662, sub739]
  rfl
theorem sub741 (p : Pattern) : d85 (change p 48 (some 49)) = d85 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d84 (change p 48 (some 49))) = d85 p
  rw [sub662, sub740]
  rfl
theorem sub742 (p : Pattern) : d86 (change p 48 (some 49)) = d86 p := by
  change (if p 160 then d85 (change p 48 (some 49)) else d65 (change p 48 (some 49))) = d86 p
  rw [sub741, sub721]
  rfl
theorem sub743 (p : Pattern) : d87 (change p 48 (some 49)) = d87 p := by
  change (if p 141 then d86 (change p 48 (some 49)) else d82 (change p 48 (some 49))) = d87 p
  rw [sub742, sub738]
  rfl
theorem sub744 (p : Pattern) : d88 (change p 48 (some 49)) = d88 p := by
  change (if p 138 then d87 (change p 48 (some 49)) else d77 (change p 48 (some 49))) = d88 p
  rw [sub743, sub733]
  rfl
theorem sub745 (p : Pattern) : d89 (change p 48 (some 49)) = d89 p := by
  change (if p 163 then d62 (change p 48 (some 49)) else d26 (change p 48 (some 49))) = d89 p
  rw [sub718, sub678]
  rfl
theorem sub746 (p : Pattern) : d90 (change p 48 (some 49)) = d90 p := by
  change (if p 162 then d63 (change p 48 (some 49)) else d89 (change p 48 (some 49))) = d90 p
  rw [sub719, sub745]
  rfl
theorem sub747 (p : Pattern) : d91 (change p 48 (some 49)) = d91 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d63 (change p 48 (some 49))) = d91 p
  rw [sub662, sub719]
  rfl
theorem sub748 (p : Pattern) : d92 (change p 48 (some 49)) = d92 p := by
  change (if p 161 then d91 (change p 48 (some 49)) else d90 (change p 48 (some 49))) = d92 p
  rw [sub747, sub746]
  rfl
theorem sub749 (p : Pattern) : d93 (change p 48 (some 49)) = d93 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d91 (change p 48 (some 49))) = d93 p
  rw [sub662, sub747]
  rfl
theorem sub750 (p : Pattern) : d94 (change p 48 (some 49)) = d94 p := by
  change (if p 160 then d93 (change p 48 (some 49)) else d92 (change p 48 (some 49))) = d94 p
  rw [sub749, sub748]
  rfl
theorem sub751 (p : Pattern) : d95 (change p 48 (some 49)) = d95 p := by
  change (if p 160 then d12 (change p 48 (some 49)) else d93 (change p 48 (some 49))) = d95 p
  rw [sub662, sub749]
  rfl
theorem sub752 (p : Pattern) : d96 (change p 48 (some 49)) = d96 p := by
  change (if p 141 then d95 (change p 48 (some 49)) else d94 (change p 48 (some 49))) = d96 p
  rw [sub751, sub750]
  rfl
theorem sub753 (p : Pattern) : d97 (change p 48 (some 49)) = d97 p := by
  change (if p 138 then d96 (change p 48 (some 49)) else d87 (change p 48 (some 49))) = d97 p
  rw [sub752, sub743]
  rfl
theorem sub754 (p : Pattern) : d98 (change p 48 (some 49)) = d98 p := by
  change (if p 116 then d97 (change p 48 (some 49)) else d88 (change p 48 (some 49))) = d98 p
  rw [sub753, sub744]
  rfl
theorem sub755 (p : Pattern) : d99 (change p 48 (some 49)) = d99 p := by
  change (if p 138 then d12 (change p 48 (some 49)) else d87 (change p 48 (some 49))) = d99 p
  rw [sub662, sub743]
  rfl
theorem sub756 (p : Pattern) : d100 (change p 48 (some 49)) = d100 p := by
  change (if p 116 then d99 (change p 48 (some 49)) else d88 (change p 48 (some 49))) = d100 p
  rw [sub755, sub744]
  rfl
theorem sub757 (p : Pattern) : d101 (change p 48 (some 49)) = d101 p := by
  change (if p 115 then d100 (change p 48 (some 49)) else d98 (change p 48 (some 49))) = d101 p
  rw [sub756, sub754]
  rfl
theorem sub758 (p : Pattern) : d1 (change p 48 (some 49)) = d1 p := by
  rfl
theorem sub759 (p : Pattern) : d102 (change p 48 (some 49)) = d102 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d1 (change p 48 (some 49))) = d102 p
  rw [sub662, sub758]
  rfl
theorem sub760 (p : Pattern) : d103 (change p 48 (some 49)) = d103 p := by
  change (if p 246 then d102 (change p 48 (some 49)) else d1 (change p 48 (some 49))) = d103 p
  rw [sub759, sub758]
  rfl
theorem sub761 (p : Pattern) : d104 (change p 48 (some 49)) = d104 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d103 (change p 48 (some 49))) = d104 p
  rw [sub662, sub760]
  rfl
theorem sub762 (p : Pattern) : d105 (change p 48 (some 49)) = d105 p := by
  change (if p 182 then d104 (change p 48 (some 49)) else d103 (change p 48 (some 49))) = d105 p
  rw [sub761, sub760]
  rfl
theorem sub763 (p : Pattern) : d5 (change p 48 (some 49)) = d5 p := by
  rfl
theorem sub764 (p : Pattern) : d106 (change p 48 (some 49)) = d106 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d5 (change p 48 (some 49))) = d106 p
  rw [sub662, sub763]
  rfl
theorem sub765 (p : Pattern) : d107 (change p 48 (some 49)) = d107 p := by
  change (if p 246 then d106 (change p 48 (some 49)) else d5 (change p 48 (some 49))) = d107 p
  rw [sub764, sub763]
  rfl
theorem sub766 (p : Pattern) : d108 (change p 48 (some 49)) = d108 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d107 (change p 48 (some 49))) = d108 p
  rw [sub662, sub765]
  rfl
theorem sub767 (p : Pattern) : d109 (change p 48 (some 49)) = d109 p := by
  change (if p 182 then d108 (change p 48 (some 49)) else d107 (change p 48 (some 49))) = d109 p
  rw [sub766, sub765]
  rfl
theorem sub768 (p : Pattern) : d110 (change p 48 (some 49)) = d110 p := by
  change (if p 163 then d109 (change p 48 (some 49)) else d105 (change p 48 (some 49))) = d110 p
  rw [sub767, sub762]
  rfl
theorem sub769 (p : Pattern) : d111 (change p 48 (some 49)) = d111 p := by
  change (if p 162 then d110 (change p 48 (some 49)) else d105 (change p 48 (some 49))) = d111 p
  rw [sub768, sub762]
  rfl
theorem sub770 (p : Pattern) : d112 (change p 48 (some 49)) = d112 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d60 (change p 48 (some 49))) = d112 p
  rw [sub662, sub716]
  rfl
theorem sub771 (p : Pattern) : d113 (change p 48 (some 49)) = d113 p := by
  change (if p 162 then d112 (change p 48 (some 49)) else d110 (change p 48 (some 49))) = d113 p
  rw [sub770, sub768]
  rfl
theorem sub772 (p : Pattern) : d114 (change p 48 (some 49)) = d114 p := by
  change (if p 161 then d113 (change p 48 (some 49)) else d111 (change p 48 (some 49))) = d114 p
  rw [sub771, sub769]
  rfl
theorem sub773 (p : Pattern) : d3 (change p 48 (some 49)) = d3 p := by
  rfl
theorem sub774 (p : Pattern) : d115 (change p 48 (some 49)) = d115 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d3 (change p 48 (some 49))) = d115 p
  rw [sub662, sub773]
  rfl
theorem sub775 (p : Pattern) : d116 (change p 48 (some 49)) = d116 p := by
  change (if p 246 then d115 (change p 48 (some 49)) else d3 (change p 48 (some 49))) = d116 p
  rw [sub774, sub773]
  rfl
theorem sub776 (p : Pattern) : d117 (change p 48 (some 49)) = d117 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d116 (change p 48 (some 49))) = d117 p
  rw [sub662, sub775]
  rfl
theorem sub777 (p : Pattern) : d118 (change p 48 (some 49)) = d118 p := by
  change (if p 182 then d117 (change p 48 (some 49)) else d103 (change p 48 (some 49))) = d118 p
  rw [sub776, sub760]
  rfl
theorem sub778 (p : Pattern) : d7 (change p 48 (some 49)) = d7 p := by
  rfl
theorem sub779 (p : Pattern) : d119 (change p 48 (some 49)) = d119 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d7 (change p 48 (some 49))) = d119 p
  rw [sub662, sub778]
  rfl
theorem sub780 (p : Pattern) : d120 (change p 48 (some 49)) = d120 p := by
  change (if p 246 then d119 (change p 48 (some 49)) else d7 (change p 48 (some 49))) = d120 p
  rw [sub779, sub778]
  rfl
theorem sub781 (p : Pattern) : d121 (change p 48 (some 49)) = d121 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d120 (change p 48 (some 49))) = d121 p
  rw [sub662, sub780]
  rfl
theorem sub782 (p : Pattern) : d122 (change p 48 (some 49)) = d122 p := by
  change (if p 182 then d121 (change p 48 (some 49)) else d103 (change p 48 (some 49))) = d122 p
  rw [sub781, sub760]
  rfl
theorem sub783 (p : Pattern) : d123 (change p 48 (some 49)) = d123 p := by
  change (if p 163 then d122 (change p 48 (some 49)) else d118 (change p 48 (some 49))) = d123 p
  rw [sub782, sub777]
  rfl
theorem sub784 (p : Pattern) : d124 (change p 48 (some 49)) = d124 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d103 (change p 48 (some 49))) = d124 p
  rw [sub662, sub760]
  rfl
theorem sub785 (p : Pattern) : d125 (change p 48 (some 49)) = d125 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d107 (change p 48 (some 49))) = d125 p
  rw [sub662, sub765]
  rfl
theorem sub786 (p : Pattern) : d126 (change p 48 (some 49)) = d126 p := by
  change (if p 163 then d125 (change p 48 (some 49)) else d124 (change p 48 (some 49))) = d126 p
  rw [sub785, sub784]
  rfl
theorem sub787 (p : Pattern) : d127 (change p 48 (some 49)) = d127 p := by
  change (if p 162 then d126 (change p 48 (some 49)) else d123 (change p 48 (some 49))) = d127 p
  rw [sub786, sub783]
  rfl
theorem sub788 (p : Pattern) : d128 (change p 48 (some 49)) = d128 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d70 (change p 48 (some 49))) = d128 p
  rw [sub662, sub726]
  rfl
theorem sub789 (p : Pattern) : d129 (change p 48 (some 49)) = d129 p := by
  change (if p 162 then d128 (change p 48 (some 49)) else d126 (change p 48 (some 49))) = d129 p
  rw [sub788, sub786]
  rfl
theorem sub790 (p : Pattern) : d130 (change p 48 (some 49)) = d130 p := by
  change (if p 161 then d129 (change p 48 (some 49)) else d127 (change p 48 (some 49))) = d130 p
  rw [sub789, sub787]
  rfl
theorem sub791 (p : Pattern) : d131 (change p 48 (some 49)) = d131 p := by
  change (if p 160 then d130 (change p 48 (some 49)) else d114 (change p 48 (some 49))) = d131 p
  rw [sub790, sub772]
  rfl
theorem sub792 (p : Pattern) : d132 (change p 48 (some 49)) = d132 p := by
  change (if p 182 then d117 (change p 48 (some 49)) else d116 (change p 48 (some 49))) = d132 p
  rw [sub776, sub775]
  rfl
theorem sub793 (p : Pattern) : d133 (change p 48 (some 49)) = d133 p := by
  change (if p 163 then d132 (change p 48 (some 49)) else d105 (change p 48 (some 49))) = d133 p
  rw [sub792, sub762]
  rfl
theorem sub794 (p : Pattern) : d134 (change p 48 (some 49)) = d134 p := by
  change (if p 163 then d60 (change p 48 (some 49)) else d109 (change p 48 (some 49))) = d134 p
  rw [sub716, sub767]
  rfl
theorem sub795 (p : Pattern) : d135 (change p 48 (some 49)) = d135 p := by
  change (if p 162 then d134 (change p 48 (some 49)) else d133 (change p 48 (some 49))) = d135 p
  rw [sub794, sub793]
  rfl
theorem sub796 (p : Pattern) : d136 (change p 48 (some 49)) = d136 p := by
  change (if p 163 then d62 (change p 48 (some 49)) else d109 (change p 48 (some 49))) = d136 p
  rw [sub718, sub767]
  rfl
theorem sub797 (p : Pattern) : d137 (change p 48 (some 49)) = d137 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d136 (change p 48 (some 49))) = d137 p
  rw [sub662, sub796]
  rfl
theorem sub798 (p : Pattern) : d138 (change p 48 (some 49)) = d138 p := by
  change (if p 161 then d137 (change p 48 (some 49)) else d135 (change p 48 (some 49))) = d138 p
  rw [sub797, sub795]
  rfl
theorem sub799 (p : Pattern) : d139 (change p 48 (some 49)) = d139 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d116 (change p 48 (some 49))) = d139 p
  rw [sub662, sub775]
  rfl
theorem sub800 (p : Pattern) : d140 (change p 48 (some 49)) = d140 p := by
  change (if p 163 then d139 (change p 48 (some 49)) else d122 (change p 48 (some 49))) = d140 p
  rw [sub799, sub782]
  rfl
theorem sub801 (p : Pattern) : d141 (change p 48 (some 49)) = d141 p := by
  change (if p 163 then d70 (change p 48 (some 49)) else d125 (change p 48 (some 49))) = d141 p
  rw [sub726, sub785]
  rfl
theorem sub802 (p : Pattern) : d142 (change p 48 (some 49)) = d142 p := by
  change (if p 162 then d141 (change p 48 (some 49)) else d140 (change p 48 (some 49))) = d142 p
  rw [sub801, sub800]
  rfl
theorem sub803 (p : Pattern) : d143 (change p 48 (some 49)) = d143 p := by
  change (if p 163 then d72 (change p 48 (some 49)) else d125 (change p 48 (some 49))) = d143 p
  rw [sub728, sub785]
  rfl
theorem sub804 (p : Pattern) : d144 (change p 48 (some 49)) = d144 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d143 (change p 48 (some 49))) = d144 p
  rw [sub662, sub803]
  rfl
theorem sub805 (p : Pattern) : d145 (change p 48 (some 49)) = d145 p := by
  change (if p 161 then d144 (change p 48 (some 49)) else d142 (change p 48 (some 49))) = d145 p
  rw [sub804, sub802]
  rfl
theorem sub806 (p : Pattern) : d146 (change p 48 (some 49)) = d146 p := by
  change (if p 160 then d145 (change p 48 (some 49)) else d138 (change p 48 (some 49))) = d146 p
  rw [sub805, sub798]
  rfl
theorem sub807 (p : Pattern) : d147 (change p 48 (some 49)) = d147 p := by
  change (if p 141 then d146 (change p 48 (some 49)) else d131 (change p 48 (some 49))) = d147 p
  rw [sub806, sub791]
  rfl
theorem sub808 (p : Pattern) : d148 (change p 48 (some 49)) = d148 p := by
  change (if p 182 then d121 (change p 48 (some 49)) else d120 (change p 48 (some 49))) = d148 p
  rw [sub781, sub780]
  rfl
theorem sub809 (p : Pattern) : d149 (change p 48 (some 49)) = d149 p := by
  change (if p 163 then d148 (change p 48 (some 49)) else d132 (change p 48 (some 49))) = d149 p
  rw [sub808, sub792]
  rfl
theorem sub810 (p : Pattern) : d150 (change p 48 (some 49)) = d150 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d149 (change p 48 (some 49))) = d150 p
  rw [sub662, sub809]
  rfl
theorem sub811 (p : Pattern) : d151 (change p 48 (some 49)) = d151 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d150 (change p 48 (some 49))) = d151 p
  rw [sub662, sub810]
  rfl
theorem sub812 (p : Pattern) : d152 (change p 48 (some 49)) = d152 p := by
  change (if p 160 then d151 (change p 48 (some 49)) else d114 (change p 48 (some 49))) = d152 p
  rw [sub811, sub772]
  rfl
theorem sub813 (p : Pattern) : d153 (change p 48 (some 49)) = d153 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d148 (change p 48 (some 49))) = d153 p
  rw [sub662, sub808]
  rfl
theorem sub814 (p : Pattern) : d154 (change p 48 (some 49)) = d154 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d153 (change p 48 (some 49))) = d154 p
  rw [sub662, sub813]
  rfl
theorem sub815 (p : Pattern) : d155 (change p 48 (some 49)) = d155 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d154 (change p 48 (some 49))) = d155 p
  rw [sub662, sub814]
  rfl
theorem sub816 (p : Pattern) : d156 (change p 48 (some 49)) = d156 p := by
  change (if p 160 then d155 (change p 48 (some 49)) else d138 (change p 48 (some 49))) = d156 p
  rw [sub815, sub798]
  rfl
theorem sub817 (p : Pattern) : d157 (change p 48 (some 49)) = d157 p := by
  change (if p 141 then d156 (change p 48 (some 49)) else d152 (change p 48 (some 49))) = d157 p
  rw [sub816, sub812]
  rfl
theorem sub818 (p : Pattern) : d158 (change p 48 (some 49)) = d158 p := by
  change (if p 138 then d157 (change p 48 (some 49)) else d147 (change p 48 (some 49))) = d158 p
  rw [sub817, sub807]
  rfl
theorem sub819 (p : Pattern) : d159 (change p 48 (some 49)) = d159 p := by
  change (if p 162 then d12 (change p 48 (some 49)) else d112 (change p 48 (some 49))) = d159 p
  rw [sub662, sub770]
  rfl
theorem sub820 (p : Pattern) : d160 (change p 48 (some 49)) = d160 p := by
  change (if p 161 then d12 (change p 48 (some 49)) else d159 (change p 48 (some 49))) = d160 p
  rw [sub662, sub819]
  rfl
theorem sub821 (p : Pattern) : d161 (change p 48 (some 49)) = d161 p := by
  change (if p 160 then d12 (change p 48 (some 49)) else d160 (change p 48 (some 49))) = d161 p
  rw [sub662, sub820]
  rfl
theorem sub822 (p : Pattern) : d162 (change p 48 (some 49)) = d162 p := by
  change (if p 141 then d12 (change p 48 (some 49)) else d161 (change p 48 (some 49))) = d162 p
  rw [sub662, sub821]
  rfl
theorem sub823 (p : Pattern) : d163 (change p 48 (some 49)) = d163 p := by
  change (if p 138 then d162 (change p 48 (some 49)) else d157 (change p 48 (some 49))) = d163 p
  rw [sub822, sub817]
  rfl
theorem sub824 (p : Pattern) : d164 (change p 48 (some 49)) = d164 p := by
  change (if p 116 then d163 (change p 48 (some 49)) else d158 (change p 48 (some 49))) = d164 p
  rw [sub823, sub818]
  rfl
theorem sub825 (p : Pattern) : d165 (change p 48 (some 49)) = d165 p := by
  change (if p 138 then d12 (change p 48 (some 49)) else d157 (change p 48 (some 49))) = d165 p
  rw [sub662, sub817]
  rfl
theorem sub826 (p : Pattern) : d166 (change p 48 (some 49)) = d166 p := by
  change (if p 116 then d165 (change p 48 (some 49)) else d158 (change p 48 (some 49))) = d166 p
  rw [sub825, sub818]
  rfl
theorem sub827 (p : Pattern) : d167 (change p 48 (some 49)) = d167 p := by
  change (if p 115 then d166 (change p 48 (some 49)) else d164 (change p 48 (some 49))) = d167 p
  rw [sub826, sub824]
  rfl
theorem sub828 (p : Pattern) : d168 (change p 48 (some 49)) = d168 p := by
  change (if p 71 then d167 (change p 48 (some 49)) else d101 (change p 48 (some 49))) = d168 p
  rw [sub827, sub757]
  rfl
theorem sub829 (p : Pattern) : d169 (change p 48 (some 49)) = d168 p := by
  change d168 (change p 48 (some 49)) = d168 p
  exact sub828 p
theorem sub830 (p : Pattern) : d481 (change p 48 (some 49)) = d168 p := by
  change d169 (change p 48 (some 49)) = d168 p
  exact sub829 p
theorem sub831 (p : Pattern) : d0 (change p 49 none) = d0 p := by
  rfl
theorem sub832 (p : Pattern) : d12 (change p 49 none) = d12 p := by
  rfl
theorem sub833 (p : Pattern) : d13 (change p 49 none) = d13 p := by
  change (if p 247 then d12 (change p 49 none) else d0 (change p 49 none)) = d13 p
  rw [sub832, sub831]
  rfl
theorem sub834 (p : Pattern) : d14 (change p 49 none) = d14 p := by
  change (if p 246 then d13 (change p 49 none) else d0 (change p 49 none)) = d14 p
  rw [sub833, sub831]
  rfl
theorem sub835 (p : Pattern) : d15 (change p 49 none) = d15 p := by
  change (if p 204 then d12 (change p 49 none) else d14 (change p 49 none)) = d15 p
  rw [sub832, sub834]
  rfl
theorem sub836 (p : Pattern) : d16 (change p 49 none) = d16 p := by
  change (if p 182 then d15 (change p 49 none) else d14 (change p 49 none)) = d16 p
  rw [sub835, sub834]
  rfl
theorem sub837 (p : Pattern) : d4 (change p 49 none) = d4 p := by
  rfl
theorem sub838 (p : Pattern) : d17 (change p 49 none) = d17 p := by
  change (if p 247 then d12 (change p 49 none) else d4 (change p 49 none)) = d17 p
  rw [sub832, sub837]
  rfl
theorem sub839 (p : Pattern) : d18 (change p 49 none) = d18 p := by
  change (if p 246 then d17 (change p 49 none) else d4 (change p 49 none)) = d18 p
  rw [sub838, sub837]
  rfl
end NetHack.Sokoban22Refined85
