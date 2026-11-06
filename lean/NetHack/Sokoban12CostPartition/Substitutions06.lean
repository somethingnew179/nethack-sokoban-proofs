/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub720 (p : Pattern) : d9 (change p 160 (some 186)) = d9 p := by
  change (if p 271 then d3 (change p 160 (some 186)) else d2 (change p 160 (some 186))) = d9 p
  rw [sub719, sub713]
  rfl
theorem sub721 (p : Pattern) : d10 (change p 160 (some 186)) = d10 p := by
  change (if p 193 then d9 (change p 160 (some 186)) else d8 (change p 160 (some 186))) = d10 p
  rw [sub720, sub718]
  rfl
theorem sub722 (p : Pattern) : d11 (change p 160 (some 186)) = d11 p := by
  change (if p 192 then d10 (change p 160 (some 186)) else d8 (change p 160 (some 186))) = d11 p
  rw [sub721, sub718]
  rfl
theorem sub723 (p : Pattern) : d12 (change p 160 (some 186)) = d12 p := by
  change (if p 168 then d11 (change p 160 (some 186)) else d7 (change p 160 (some 186))) = d12 p
  rw [sub722, sub715]
  rfl
theorem sub724 (p : Pattern) : d109 (change p 160 (some 186)) = d12 p := by
  change d12 (change p 160 (some 186)) = d12 p
  exact sub723 p
theorem sub725 (p : Pattern) : d227 (change p 160 (some 186)) = d13 p := by
  change (if p 141 then d109 (change p 160 (some 186)) else d106 (change p 160 (some 186))) = d13 p
  rw [sub724, sub716]
  rfl
theorem sub726 (p : Pattern) : d4 (change p 160 (some 186)) = d4 p := by
  rfl
theorem sub727 (p : Pattern) : d54 (change p 160 (some 186)) = d54 p := by
  change (if p 193 then d4 (change p 160 (some 186)) else d2 (change p 160 (some 186))) = d54 p
  rw [sub726, sub713]
  rfl
theorem sub728 (p : Pattern) : d55 (change p 160 (some 186)) = d55 p := by
  change (if p 192 then d54 (change p 160 (some 186)) else d2 (change p 160 (some 186))) = d55 p
  rw [sub727, sub713]
  rfl
theorem sub729 (p : Pattern) : d229 (change p 160 (some 186)) = d832 p := by
  change (if p 158 then d55 (change p 160 (some 186)) else d106 (change p 160 (some 186))) = d832 p
  rw [sub728, sub716]
  rfl
theorem sub730 (p : Pattern) : d5 (change p 160 (some 186)) = d5 p := by
  rfl
theorem sub731 (p : Pattern) : d58 (change p 160 (some 186)) = d58 p := by
  change (if p 271 then d5 (change p 160 (some 186)) else d4 (change p 160 (some 186))) = d58 p
  rw [sub730, sub726]
  rfl
theorem sub732 (p : Pattern) : d59 (change p 160 (some 186)) = d59 p := by
  change (if p 193 then d58 (change p 160 (some 186)) else d9 (change p 160 (some 186))) = d59 p
  rw [sub731, sub720]
  rfl
theorem sub733 (p : Pattern) : d60 (change p 160 (some 186)) = d60 p := by
  change (if p 192 then d59 (change p 160 (some 186)) else d9 (change p 160 (some 186))) = d60 p
  rw [sub732, sub720]
  rfl
theorem sub734 (p : Pattern) : d65 (change p 160 (some 186)) = d65 p := by
  change (if p 168 then d60 (change p 160 (some 186)) else d55 (change p 160 (some 186))) = d65 p
  rw [sub733, sub728]
  rfl
theorem sub735 (p : Pattern) : d230 (change p 160 (some 186)) = d833 p := by
  change (if p 158 then d65 (change p 160 (some 186)) else d109 (change p 160 (some 186))) = d833 p
  rw [sub734, sub724]
  rfl
theorem sub736 (p : Pattern) : d231 (change p 160 (some 186)) = d834 p := by
  change (if p 141 then d230 (change p 160 (some 186)) else d229 (change p 160 (some 186))) = d834 p
  rw [sub735, sub729]
  rfl
theorem sub737 (p : Pattern) : d366 (change p 160 (some 186)) = d835 p := by
  change (if p 133 then d231 (change p 160 (some 186)) else d227 (change p 160 (some 186))) = d835 p
  rw [sub736, sub725]
  rfl
theorem sub738 (p : Pattern) : d66 (change p 160 (some 186)) = d66 p := by
  change (if p 141 then d65 (change p 160 (some 186)) else d55 (change p 160 (some 186))) = d66 p
  rw [sub734, sub728]
  rfl
theorem sub739 (p : Pattern) : d367 (change p 160 (some 186)) = d836 p := by
  change (if p 133 then d66 (change p 160 (some 186)) else d231 (change p 160 (some 186))) = d836 p
  rw [sub738, sub736]
  rfl
theorem sub740 (p : Pattern) : d368 (change p 160 (some 186)) = d837 p := by
  change (if p 132 then d367 (change p 160 (some 186)) else d366 (change p 160 (some 186))) = d837 p
  rw [sub739, sub737]
  rfl
theorem sub741 (p : Pattern) : d369 (change p 160 (some 186)) = d838 p := by
  change (if p 134 then d66 (change p 160 (some 186)) else d227 (change p 160 (some 186))) = d838 p
  rw [sub738, sub725]
  rfl
theorem sub742 (p : Pattern) : d370 (change p 160 (some 186)) = d839 p := by
  change (if p 134 then d66 (change p 160 (some 186)) else d231 (change p 160 (some 186))) = d839 p
  rw [sub738, sub736]
  rfl
theorem sub743 (p : Pattern) : d371 (change p 160 (some 186)) = d840 p := by
  change (if p 133 then d370 (change p 160 (some 186)) else d369 (change p 160 (some 186))) = d840 p
  rw [sub742, sub741]
  rfl
theorem sub744 (p : Pattern) : d372 (change p 160 (some 186)) = d841 p := by
  change (if p 133 then d66 (change p 160 (some 186)) else d370 (change p 160 (some 186))) = d841 p
  rw [sub738, sub742]
  rfl
theorem sub745 (p : Pattern) : d373 (change p 160 (some 186)) = d842 p := by
  change (if p 132 then d372 (change p 160 (some 186)) else d371 (change p 160 (some 186))) = d842 p
  rw [sub744, sub743]
  rfl
theorem sub746 (p : Pattern) : d374 (change p 160 (some 186)) = d843 p := by
  change (if p 108 then d373 (change p 160 (some 186)) else d368 (change p 160 (some 186))) = d843 p
  rw [sub745, sub740]
  rfl
theorem sub747 (p : Pattern) : d0 (change p 133 (some 132)) = d0 p := by
  rfl
theorem sub748 (p : Pattern) : d2 (change p 133 (some 132)) = d2 p := by
  rfl
theorem sub749 (p : Pattern) : d6 (change p 133 (some 132)) = d6 p := by
  change (if p 193 then d2 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d6 p
  rw [sub748, sub747]
  rfl
theorem sub750 (p : Pattern) : d7 (change p 133 (some 132)) = d7 p := by
  change (if p 192 then d6 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d7 p
  rw [sub749, sub747]
  rfl
theorem sub751 (p : Pattern) : d4 (change p 133 (some 132)) = d4 p := by
  rfl
theorem sub752 (p : Pattern) : d54 (change p 133 (some 132)) = d54 p := by
  change (if p 193 then d4 (change p 133 (some 132)) else d2 (change p 133 (some 132))) = d54 p
  rw [sub751, sub748]
  rfl
theorem sub753 (p : Pattern) : d55 (change p 133 (some 132)) = d55 p := by
  change (if p 192 then d54 (change p 133 (some 132)) else d2 (change p 133 (some 132))) = d55 p
  rw [sub752, sub748]
  rfl
theorem sub754 (p : Pattern) : d56 (change p 133 (some 132)) = d56 p := by
  change (if p 186 then d55 (change p 133 (some 132)) else d7 (change p 133 (some 132))) = d56 p
  rw [sub753, sub750]
  rfl
theorem sub755 (p : Pattern) : d57 (change p 133 (some 132)) = d57 p := by
  change (if p 160 then d56 (change p 133 (some 132)) else d7 (change p 133 (some 132))) = d57 p
  rw [sub754, sub750]
  rfl
theorem sub756 (p : Pattern) : d68 (change p 133 (some 132)) = d68 p := by
  change (if p 158 then d55 (change p 133 (some 132)) else d57 (change p 133 (some 132))) = d68 p
  rw [sub753, sub755]
  rfl
theorem sub757 (p : Pattern) : d1 (change p 133 (some 132)) = d1 p := by
  rfl
theorem sub758 (p : Pattern) : d8 (change p 133 (some 132)) = d8 p := by
  change (if p 271 then d1 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d8 p
  rw [sub757, sub747]
  rfl
theorem sub759 (p : Pattern) : d3 (change p 133 (some 132)) = d3 p := by
  rfl
theorem sub760 (p : Pattern) : d9 (change p 133 (some 132)) = d9 p := by
  change (if p 271 then d3 (change p 133 (some 132)) else d2 (change p 133 (some 132))) = d9 p
  rw [sub759, sub748]
  rfl
theorem sub761 (p : Pattern) : d10 (change p 133 (some 132)) = d10 p := by
  change (if p 193 then d9 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d10 p
  rw [sub760, sub758]
  rfl
theorem sub762 (p : Pattern) : d11 (change p 133 (some 132)) = d11 p := by
  change (if p 192 then d10 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d11 p
  rw [sub761, sub758]
  rfl
theorem sub763 (p : Pattern) : d12 (change p 133 (some 132)) = d12 p := by
  change (if p 168 then d11 (change p 133 (some 132)) else d7 (change p 133 (some 132))) = d12 p
  rw [sub762, sub750]
  rfl
theorem sub764 (p : Pattern) : d5 (change p 133 (some 132)) = d5 p := by
  rfl
theorem sub765 (p : Pattern) : d58 (change p 133 (some 132)) = d58 p := by
  change (if p 271 then d5 (change p 133 (some 132)) else d4 (change p 133 (some 132))) = d58 p
  rw [sub764, sub751]
  rfl
theorem sub766 (p : Pattern) : d59 (change p 133 (some 132)) = d59 p := by
  change (if p 193 then d58 (change p 133 (some 132)) else d9 (change p 133 (some 132))) = d59 p
  rw [sub765, sub760]
  rfl
theorem sub767 (p : Pattern) : d60 (change p 133 (some 132)) = d60 p := by
  change (if p 192 then d59 (change p 133 (some 132)) else d9 (change p 133 (some 132))) = d60 p
  rw [sub766, sub760]
  rfl
theorem sub768 (p : Pattern) : d61 (change p 133 (some 132)) = d61 p := by
  change (if p 186 then d60 (change p 133 (some 132)) else d11 (change p 133 (some 132))) = d61 p
  rw [sub767, sub762]
  rfl
theorem sub769 (p : Pattern) : d62 (change p 133 (some 132)) = d62 p := by
  change (if p 168 then d61 (change p 133 (some 132)) else d56 (change p 133 (some 132))) = d62 p
  rw [sub768, sub754]
  rfl
theorem sub770 (p : Pattern) : d63 (change p 133 (some 132)) = d63 p := by
  change (if p 160 then d62 (change p 133 (some 132)) else d12 (change p 133 (some 132))) = d63 p
  rw [sub769, sub763]
  rfl
theorem sub771 (p : Pattern) : d65 (change p 133 (some 132)) = d65 p := by
  change (if p 168 then d60 (change p 133 (some 132)) else d55 (change p 133 (some 132))) = d65 p
  rw [sub767, sub753]
  rfl
theorem sub772 (p : Pattern) : d69 (change p 133 (some 132)) = d69 p := by
  change (if p 158 then d65 (change p 133 (some 132)) else d63 (change p 133 (some 132))) = d69 p
  rw [sub771, sub770]
  rfl
theorem sub773 (p : Pattern) : d70 (change p 133 (some 132)) = d70 p := by
  change (if p 141 then d69 (change p 133 (some 132)) else d68 (change p 133 (some 132))) = d70 p
  rw [sub772, sub756]
  rfl
theorem sub774 (p : Pattern) : d106 (change p 133 (some 132)) = d106 p := by
  change (if p 160 then d55 (change p 133 (some 132)) else d7 (change p 133 (some 132))) = d106 p
  rw [sub753, sub750]
  rfl
theorem sub775 (p : Pattern) : d107 (change p 133 (some 132)) = d107 p := by
  change (if p 159 then d55 (change p 133 (some 132)) else d106 (change p 133 (some 132))) = d107 p
  rw [sub753, sub774]
  rfl
theorem sub776 (p : Pattern) : d211 (change p 133 (some 132)) = d211 p := by
  change (if p 158 then d55 (change p 133 (some 132)) else d107 (change p 133 (some 132))) = d211 p
  rw [sub753, sub775]
  rfl
theorem sub777 (p : Pattern) : d109 (change p 133 (some 132)) = d109 p := by
  change (if p 160 then d65 (change p 133 (some 132)) else d12 (change p 133 (some 132))) = d109 p
  rw [sub771, sub763]
  rfl
theorem sub778 (p : Pattern) : d110 (change p 133 (some 132)) = d110 p := by
  change (if p 159 then d65 (change p 133 (some 132)) else d109 (change p 133 (some 132))) = d110 p
  rw [sub771, sub777]
  rfl
theorem sub779 (p : Pattern) : d212 (change p 133 (some 132)) = d212 p := by
  change (if p 158 then d65 (change p 133 (some 132)) else d110 (change p 133 (some 132))) = d212 p
  rw [sub771, sub778]
  rfl
theorem sub780 (p : Pattern) : d213 (change p 133 (some 132)) = d213 p := by
  change (if p 141 then d212 (change p 133 (some 132)) else d211 (change p 133 (some 132))) = d213 p
  rw [sub779, sub776]
  rfl
theorem sub781 (p : Pattern) : d214 (change p 133 (some 132)) = d214 p := by
  change (if p 134 then d213 (change p 133 (some 132)) else d70 (change p 133 (some 132))) = d214 p
  rw [sub780, sub773]
  rfl
theorem sub782 (p : Pattern) : d215 (change p 133 (some 132)) = d214 p := by
  change d214 (change p 133 (some 132)) = d214 p
  exact sub781 p
theorem sub783 (p : Pattern) : d216 (change p 133 (some 132)) = d214 p := by
  change d215 (change p 133 (some 132)) = d214 p
  exact sub782 p
theorem sub784 (p : Pattern) : d66 (change p 133 (some 132)) = d66 p := by
  change (if p 141 then d65 (change p 133 (some 132)) else d55 (change p 133 (some 132))) = d66 p
  rw [sub771, sub753]
  rfl
theorem sub785 (p : Pattern) : d71 (change p 133 (some 132)) = d71 p := by
  change (if p 134 then d66 (change p 133 (some 132)) else d70 (change p 133 (some 132))) = d71 p
  rw [sub784, sub773]
  rfl
theorem sub786 (p : Pattern) : d73 (change p 133 (some 132)) = d71 p := by
  change d71 (change p 133 (some 132)) = d71 p
  exact sub785 p
theorem sub787 (p : Pattern) : d218 (change p 133 (some 132)) = d71 p := by
  change d73 (change p 133 (some 132)) = d71 p
  exact sub786 p
theorem sub788 (p : Pattern) : d219 (change p 133 (some 132)) = d844 p := by
  change (if p 108 then d218 (change p 133 (some 132)) else d216 (change p 133 (some 132))) = d844 p
  rw [sub787, sub783]
  rfl
theorem sub789 (p : Pattern) : d0 (change p 10000 (some 187)) = d0 p := by
  rfl
theorem sub790 (p : Pattern) : d2 (change p 10000 (some 187)) = d2 p := by
  rfl
theorem sub791 (p : Pattern) : d6 (change p 10000 (some 187)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 187)) else d0 (change p 10000 (some 187))) = d6 p
  rw [sub790, sub789]
  rfl
theorem sub792 (p : Pattern) : d7 (change p 10000 (some 187)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 187)) else d0 (change p 10000 (some 187))) = d7 p
  rw [sub791, sub789]
  rfl
theorem sub793 (p : Pattern) : d4 (change p 10000 (some 187)) = d4 p := by
  rfl
theorem sub794 (p : Pattern) : d54 (change p 10000 (some 187)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 187)) else d2 (change p 10000 (some 187))) = d54 p
  rw [sub793, sub790]
  rfl
theorem sub795 (p : Pattern) : d55 (change p 10000 (some 187)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 187)) else d2 (change p 10000 (some 187))) = d55 p
  rw [sub794, sub790]
  rfl
theorem sub796 (p : Pattern) : d56 (change p 10000 (some 187)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d56 p
  rw [sub795, sub792]
  rfl
theorem sub797 (p : Pattern) : d57 (change p 10000 (some 187)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d57 p
  rw [sub796, sub792]
  rfl
theorem sub798 (p : Pattern) : d1 (change p 10000 (some 187)) = d1 p := by
  rfl
theorem sub799 (p : Pattern) : d8 (change p 10000 (some 187)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 187)) else d0 (change p 10000 (some 187))) = d8 p
  rw [sub798, sub789]
  rfl
theorem sub800 (p : Pattern) : d3 (change p 10000 (some 187)) = d3 p := by
  rfl
theorem sub801 (p : Pattern) : d9 (change p 10000 (some 187)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 187)) else d2 (change p 10000 (some 187))) = d9 p
  rw [sub800, sub790]
  rfl
theorem sub802 (p : Pattern) : d10 (change p 10000 (some 187)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 187)) else d8 (change p 10000 (some 187))) = d10 p
  rw [sub801, sub799]
  rfl
theorem sub803 (p : Pattern) : d11 (change p 10000 (some 187)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 187)) else d8 (change p 10000 (some 187))) = d11 p
  rw [sub802, sub799]
  rfl
theorem sub804 (p : Pattern) : d12 (change p 10000 (some 187)) = d12 p := by
  change (if p 168 then d11 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d12 p
  rw [sub803, sub792]
  rfl
theorem sub805 (p : Pattern) : d5 (change p 10000 (some 187)) = d5 p := by
  rfl
theorem sub806 (p : Pattern) : d58 (change p 10000 (some 187)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 187)) else d4 (change p 10000 (some 187))) = d58 p
  rw [sub805, sub793]
  rfl
theorem sub807 (p : Pattern) : d59 (change p 10000 (some 187)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 187)) else d9 (change p 10000 (some 187))) = d59 p
  rw [sub806, sub801]
  rfl
theorem sub808 (p : Pattern) : d60 (change p 10000 (some 187)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 187)) else d9 (change p 10000 (some 187))) = d60 p
  rw [sub807, sub801]
  rfl
theorem sub809 (p : Pattern) : d61 (change p 10000 (some 187)) = d61 p := by
  change (if p 186 then d60 (change p 10000 (some 187)) else d11 (change p 10000 (some 187))) = d61 p
  rw [sub808, sub803]
  rfl
theorem sub810 (p : Pattern) : d62 (change p 10000 (some 187)) = d62 p := by
  change (if p 168 then d61 (change p 10000 (some 187)) else d56 (change p 10000 (some 187))) = d62 p
  rw [sub809, sub796]
  rfl
theorem sub811 (p : Pattern) : d63 (change p 10000 (some 187)) = d63 p := by
  change (if p 160 then d62 (change p 10000 (some 187)) else d12 (change p 10000 (some 187))) = d63 p
  rw [sub810, sub804]
  rfl
theorem sub812 (p : Pattern) : d64 (change p 10000 (some 187)) = d64 p := by
  change (if p 141 then d63 (change p 10000 (some 187)) else d57 (change p 10000 (some 187))) = d64 p
  rw [sub811, sub797]
  rfl
theorem sub813 (p : Pattern) : d106 (change p 10000 (some 187)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d106 p
  rw [sub795, sub792]
  rfl
theorem sub814 (p : Pattern) : d65 (change p 10000 (some 187)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 187)) else d55 (change p 10000 (some 187))) = d65 p
  rw [sub808, sub795]
  rfl
theorem sub815 (p : Pattern) : d109 (change p 10000 (some 187)) = d109 p := by
  change (if p 160 then d65 (change p 10000 (some 187)) else d12 (change p 10000 (some 187))) = d109 p
  rw [sub814, sub804]
  rfl
theorem sub816 (p : Pattern) : d227 (change p 10000 (some 187)) = d227 p := by
  change (if p 141 then d109 (change p 10000 (some 187)) else d106 (change p 10000 (some 187))) = d227 p
  rw [sub815, sub813]
  rfl
theorem sub817 (p : Pattern) : d228 (change p 10000 (some 187)) = d228 p := by
  change (if p 134 then d227 (change p 10000 (some 187)) else d64 (change p 10000 (some 187))) = d228 p
  rw [sub816, sub812]
  rfl
theorem sub818 (p : Pattern) : d68 (change p 10000 (some 187)) = d68 p := by
  change (if p 158 then d55 (change p 10000 (some 187)) else d57 (change p 10000 (some 187))) = d68 p
  rw [sub795, sub797]
  rfl
theorem sub819 (p : Pattern) : d69 (change p 10000 (some 187)) = d69 p := by
  change (if p 158 then d65 (change p 10000 (some 187)) else d63 (change p 10000 (some 187))) = d69 p
  rw [sub814, sub811]
  rfl
theorem sub820 (p : Pattern) : d70 (change p 10000 (some 187)) = d70 p := by
  change (if p 141 then d69 (change p 10000 (some 187)) else d68 (change p 10000 (some 187))) = d70 p
  rw [sub819, sub818]
  rfl
theorem sub821 (p : Pattern) : d229 (change p 10000 (some 187)) = d229 p := by
  change (if p 158 then d55 (change p 10000 (some 187)) else d106 (change p 10000 (some 187))) = d229 p
  rw [sub795, sub813]
  rfl
theorem sub822 (p : Pattern) : d230 (change p 10000 (some 187)) = d230 p := by
  change (if p 158 then d65 (change p 10000 (some 187)) else d109 (change p 10000 (some 187))) = d230 p
  rw [sub814, sub815]
  rfl
theorem sub823 (p : Pattern) : d231 (change p 10000 (some 187)) = d231 p := by
  change (if p 141 then d230 (change p 10000 (some 187)) else d229 (change p 10000 (some 187))) = d231 p
  rw [sub822, sub821]
  rfl
theorem sub824 (p : Pattern) : d232 (change p 10000 (some 187)) = d232 p := by
  change (if p 134 then d231 (change p 10000 (some 187)) else d70 (change p 10000 (some 187))) = d232 p
  rw [sub823, sub820]
  rfl
theorem sub825 (p : Pattern) : d233 (change p 10000 (some 187)) = d233 p := by
  change (if p 133 then d232 (change p 10000 (some 187)) else d228 (change p 10000 (some 187))) = d233 p
  rw [sub824, sub817]
  rfl
theorem sub826 (p : Pattern) : d66 (change p 10000 (some 187)) = d66 p := by
  change (if p 141 then d65 (change p 10000 (some 187)) else d55 (change p 10000 (some 187))) = d66 p
  rw [sub814, sub795]
  rfl
theorem sub827 (p : Pattern) : d234 (change p 10000 (some 187)) = d234 p := by
  change (if p 133 then d66 (change p 10000 (some 187)) else d232 (change p 10000 (some 187))) = d234 p
  rw [sub826, sub824]
  rfl
theorem sub828 (p : Pattern) : d235 (change p 10000 (some 187)) = d235 p := by
  change (if p 132 then d234 (change p 10000 (some 187)) else d233 (change p 10000 (some 187))) = d235 p
  rw [sub827, sub825]
  rfl
theorem sub829 (p : Pattern) : d67 (change p 10000 (some 187)) = d67 p := by
  change (if p 134 then d66 (change p 10000 (some 187)) else d64 (change p 10000 (some 187))) = d67 p
  rw [sub826, sub812]
  rfl
theorem sub830 (p : Pattern) : d71 (change p 10000 (some 187)) = d71 p := by
  change (if p 134 then d66 (change p 10000 (some 187)) else d70 (change p 10000 (some 187))) = d71 p
  rw [sub826, sub820]
  rfl
theorem sub831 (p : Pattern) : d72 (change p 10000 (some 187)) = d72 p := by
  change (if p 133 then d71 (change p 10000 (some 187)) else d67 (change p 10000 (some 187))) = d72 p
  rw [sub830, sub829]
  rfl
theorem sub832 (p : Pattern) : d73 (change p 10000 (some 187)) = d73 p := by
  change (if p 133 then d66 (change p 10000 (some 187)) else d71 (change p 10000 (some 187))) = d73 p
  rw [sub826, sub830]
  rfl
theorem sub833 (p : Pattern) : d74 (change p 10000 (some 187)) = d74 p := by
  change (if p 132 then d73 (change p 10000 (some 187)) else d72 (change p 10000 (some 187))) = d74 p
  rw [sub832, sub831]
  rfl
theorem sub834 (p : Pattern) : d236 (change p 10000 (some 187)) = d236 p := by
  change (if p 108 then d74 (change p 10000 (some 187)) else d235 (change p 10000 (some 187))) = d236 p
  rw [sub833, sub828]
  rfl
theorem sub835 (p : Pattern) : d0 (change p 134 (some 133)) = d0 p := by
  rfl
theorem sub836 (p : Pattern) : d2 (change p 134 (some 133)) = d2 p := by
  rfl
theorem sub837 (p : Pattern) : d6 (change p 134 (some 133)) = d6 p := by
  change (if p 193 then d2 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d6 p
  rw [sub836, sub835]
  rfl
theorem sub838 (p : Pattern) : d7 (change p 134 (some 133)) = d7 p := by
  change (if p 192 then d6 (change p 134 (some 133)) else d0 (change p 134 (some 133))) = d7 p
  rw [sub837, sub835]
  rfl
theorem sub839 (p : Pattern) : d4 (change p 134 (some 133)) = d4 p := by
  rfl
end NetHack.Sokoban12CostPartition
