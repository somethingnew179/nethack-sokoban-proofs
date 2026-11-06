/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub720 (p : Pattern) : d115 (change p 80 none) = d115 p := by
  change (if p 106 then d114 (change p 80 none) else d103 (change p 80 none)) = d115 p
  rw [sub719, sub708]
  rfl
theorem sub721 (p : Pattern) : d116 (change p 80 none) = d116 p := by
  change (if p 86 then d115 (change p 80 none) else d85 (change p 80 none)) = d116 p
  rw [sub720, sub690]
  rfl
theorem sub722 (p : Pattern) : d173 (change p 80 none) = d116 p := by
  change d116 (change p 80 none) = d116 p
  exact sub721 p
theorem sub723 (p : Pattern) : d0 (change p 132 (some 158)) = d0 p := by
  rfl
theorem sub724 (p : Pattern) : d2 (change p 132 (some 158)) = d2 p := by
  rfl
theorem sub725 (p : Pattern) : d3 (change p 132 (some 158)) = d3 p := by
  change (if p 161 then d2 (change p 132 (some 158)) else d0 (change p 132 (some 158))) = d3 p
  rw [sub724, sub723]
  rfl
theorem sub726 (p : Pattern) : d4 (change p 132 (some 158)) = d4 p := by
  change (if p 160 then d3 (change p 132 (some 158)) else d0 (change p 132 (some 158))) = d4 p
  rw [sub725, sub723]
  rfl
theorem sub727 (p : Pattern) : d7 (change p 132 (some 158)) = d7 p := by
  change (if p 159 then d2 (change p 132 (some 158)) else d4 (change p 132 (some 158))) = d7 p
  rw [sub724, sub726]
  rfl
theorem sub728 (p : Pattern) : d8 (change p 132 (some 158)) = d7 p := by
  change d7 (change p 132 (some 158)) = d7 p
  exact sub727 p
theorem sub729 (p : Pattern) : d1 (change p 132 (some 158)) = d1 p := by
  rfl
theorem sub730 (p : Pattern) : d9 (change p 132 (some 158)) = d9 p := by
  change (if p 161 then d2 (change p 132 (some 158)) else d1 (change p 132 (some 158))) = d9 p
  rw [sub724, sub729]
  rfl
theorem sub731 (p : Pattern) : d10 (change p 132 (some 158)) = d10 p := by
  change (if p 160 then d9 (change p 132 (some 158)) else d1 (change p 132 (some 158))) = d10 p
  rw [sub730, sub729]
  rfl
theorem sub732 (p : Pattern) : d13 (change p 132 (some 158)) = d13 p := by
  change (if p 159 then d2 (change p 132 (some 158)) else d10 (change p 132 (some 158))) = d13 p
  rw [sub724, sub731]
  rfl
theorem sub733 (p : Pattern) : d14 (change p 132 (some 158)) = d13 p := by
  change d13 (change p 132 (some 158)) = d13 p
  exact sub732 p
theorem sub734 (p : Pattern) : d15 (change p 132 (some 158)) = d653 p := by
  change (if p 139 then d14 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d653 p
  rw [sub733, sub728]
  rfl
theorem sub735 (p : Pattern) : d16 (change p 132 (some 158)) = d654 p := by
  change (if p 138 then d15 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d654 p
  rw [sub734, sub728]
  rfl
theorem sub736 (p : Pattern) : d17 (change p 132 (some 158)) = d17 p := by
  change (if p 160 then d2 (change p 132 (some 158)) else d3 (change p 132 (some 158))) = d17 p
  rw [sub724, sub725]
  rfl
theorem sub737 (p : Pattern) : d19 (change p 132 (some 158)) = d19 p := by
  change (if p 159 then d2 (change p 132 (some 158)) else d17 (change p 132 (some 158))) = d19 p
  rw [sub724, sub736]
  rfl
theorem sub738 (p : Pattern) : d20 (change p 132 (some 158)) = d19 p := by
  change d19 (change p 132 (some 158)) = d19 p
  exact sub737 p
theorem sub739 (p : Pattern) : d21 (change p 132 (some 158)) = d21 p := by
  change (if p 160 then d2 (change p 132 (some 158)) else d9 (change p 132 (some 158))) = d21 p
  rw [sub724, sub730]
  rfl
theorem sub740 (p : Pattern) : d23 (change p 132 (some 158)) = d23 p := by
  change (if p 159 then d2 (change p 132 (some 158)) else d21 (change p 132 (some 158))) = d23 p
  rw [sub724, sub739]
  rfl
theorem sub741 (p : Pattern) : d24 (change p 132 (some 158)) = d23 p := by
  change d23 (change p 132 (some 158)) = d23 p
  exact sub740 p
theorem sub742 (p : Pattern) : d25 (change p 132 (some 158)) = d876 p := by
  change (if p 139 then d24 (change p 132 (some 158)) else d20 (change p 132 (some 158))) = d876 p
  rw [sub741, sub738]
  rfl
theorem sub743 (p : Pattern) : d26 (change p 132 (some 158)) = d877 p := by
  change (if p 138 then d25 (change p 132 (some 158)) else d20 (change p 132 (some 158))) = d877 p
  rw [sub742, sub738]
  rfl
theorem sub744 (p : Pattern) : d27 (change p 132 (some 158)) = d878 p := by
  change (if p 134 then d26 (change p 132 (some 158)) else d16 (change p 132 (some 158))) = d878 p
  rw [sub743, sub735]
  rfl
theorem sub745 (p : Pattern) : d28 (change p 132 (some 158)) = d879 p := by
  change (if p 133 then d27 (change p 132 (some 158)) else d16 (change p 132 (some 158))) = d879 p
  rw [sub744, sub735]
  rfl
theorem sub746 (p : Pattern) : d256 (change p 132 (some 158)) = d879 p := by
  change d28 (change p 132 (some 158)) = d879 p
  exact sub745 p
theorem sub747 (p : Pattern) : d46 (change p 132 (some 158)) = d880 p := by
  change (if p 134 then d25 (change p 132 (some 158)) else d15 (change p 132 (some 158))) = d880 p
  rw [sub742, sub734]
  rfl
theorem sub748 (p : Pattern) : d47 (change p 132 (some 158)) = d881 p := by
  change (if p 133 then d46 (change p 132 (some 158)) else d15 (change p 132 (some 158))) = d881 p
  rw [sub747, sub734]
  rfl
theorem sub749 (p : Pattern) : d257 (change p 132 (some 158)) = d881 p := by
  change d47 (change p 132 (some 158)) = d881 p
  exact sub748 p
theorem sub750 (p : Pattern) : d52 (change p 132 (some 158)) = d655 p := by
  change (if p 139 then d2 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d655 p
  rw [sub724, sub728]
  rfl
theorem sub751 (p : Pattern) : d53 (change p 132 (some 158)) = d656 p := by
  change (if p 138 then d52 (change p 132 (some 158)) else d15 (change p 132 (some 158))) = d656 p
  rw [sub750, sub734]
  rfl
theorem sub752 (p : Pattern) : d54 (change p 132 (some 158)) = d882 p := by
  change (if p 139 then d2 (change p 132 (some 158)) else d20 (change p 132 (some 158))) = d882 p
  rw [sub724, sub738]
  rfl
theorem sub753 (p : Pattern) : d55 (change p 132 (some 158)) = d883 p := by
  change (if p 138 then d54 (change p 132 (some 158)) else d25 (change p 132 (some 158))) = d883 p
  rw [sub752, sub742]
  rfl
theorem sub754 (p : Pattern) : d56 (change p 132 (some 158)) = d884 p := by
  change (if p 134 then d55 (change p 132 (some 158)) else d53 (change p 132 (some 158))) = d884 p
  rw [sub753, sub751]
  rfl
theorem sub755 (p : Pattern) : d57 (change p 132 (some 158)) = d885 p := by
  change (if p 133 then d56 (change p 132 (some 158)) else d53 (change p 132 (some 158))) = d885 p
  rw [sub754, sub751]
  rfl
theorem sub756 (p : Pattern) : d258 (change p 132 (some 158)) = d885 p := by
  change d57 (change p 132 (some 158)) = d885 p
  exact sub755 p
theorem sub757 (p : Pattern) : d259 (change p 132 (some 158)) = d886 p := by
  change (if p 113 then d258 (change p 132 (some 158)) else d257 (change p 132 (some 158))) = d886 p
  rw [sub756, sub749]
  rfl
theorem sub758 (p : Pattern) : d260 (change p 132 (some 158)) = d887 p := by
  change (if p 112 then d259 (change p 132 (some 158)) else d256 (change p 132 (some 158))) = d887 p
  rw [sub757, sub746]
  rfl
theorem sub759 (p : Pattern) : d261 (change p 132 (some 158)) = d879 p := by
  change d28 (change p 132 (some 158)) = d879 p
  exact sub745 p
theorem sub760 (p : Pattern) : d262 (change p 132 (some 158)) = d879 p := by
  change (if p 113 then d261 (change p 132 (some 158)) else d256 (change p 132 (some 158))) = d879 p
  rw [sub759, sub746]
  simp only [ite_self]
theorem sub761 (p : Pattern) : d263 (change p 132 (some 158)) = d885 p := by
  change d57 (change p 132 (some 158)) = d885 p
  exact sub755 p
theorem sub762 (p : Pattern) : d264 (change p 132 (some 158)) = d886 p := by
  change (if p 113 then d263 (change p 132 (some 158)) else d257 (change p 132 (some 158))) = d886 p
  rw [sub761, sub749]
  rfl
theorem sub763 (p : Pattern) : d265 (change p 132 (some 158)) = d887 p := by
  change (if p 112 then d264 (change p 132 (some 158)) else d262 (change p 132 (some 158))) = d887 p
  rw [sub762, sub760]
  rfl
theorem sub764 (p : Pattern) : d266 (change p 132 (some 158)) = d887 p := by
  change (if p 106 then d265 (change p 132 (some 158)) else d260 (change p 132 (some 158))) = d887 p
  rw [sub763, sub758]
  simp only [ite_self]
theorem sub765 (p : Pattern) : d86 (change p 132 (some 158)) = d673 p := by
  change (if p 138 then d52 (change p 132 (some 158)) else d8 (change p 132 (some 158))) = d673 p
  rw [sub750, sub728]
  rfl
theorem sub766 (p : Pattern) : d87 (change p 132 (some 158)) = d888 p := by
  change (if p 138 then d54 (change p 132 (some 158)) else d20 (change p 132 (some 158))) = d888 p
  rw [sub752, sub738]
  rfl
theorem sub767 (p : Pattern) : d88 (change p 132 (some 158)) = d889 p := by
  change (if p 134 then d87 (change p 132 (some 158)) else d86 (change p 132 (some 158))) = d889 p
  rw [sub766, sub765]
  rfl
theorem sub768 (p : Pattern) : d89 (change p 132 (some 158)) = d890 p := by
  change (if p 133 then d88 (change p 132 (some 158)) else d86 (change p 132 (some 158))) = d890 p
  rw [sub767, sub765]
  rfl
theorem sub769 (p : Pattern) : d267 (change p 132 (some 158)) = d890 p := by
  change d89 (change p 132 (some 158)) = d890 p
  exact sub768 p
theorem sub770 (p : Pattern) : d268 (change p 132 (some 158)) = d891 p := by
  change (if p 113 then d267 (change p 132 (some 158)) else d256 (change p 132 (some 158))) = d891 p
  rw [sub769, sub746]
  rfl
theorem sub771 (p : Pattern) : d97 (change p 132 (some 158)) = d659 p := by
  change (if p 139 then d2 (change p 132 (some 158)) else d14 (change p 132 (some 158))) = d659 p
  rw [sub724, sub733]
  rfl
theorem sub772 (p : Pattern) : d98 (change p 132 (some 158)) = d660 p := by
  change (if p 138 then d97 (change p 132 (some 158)) else d14 (change p 132 (some 158))) = d660 p
  rw [sub771, sub733]
  rfl
theorem sub773 (p : Pattern) : d70 (change p 132 (some 158)) = d892 p := by
  change (if p 139 then d2 (change p 132 (some 158)) else d24 (change p 132 (some 158))) = d892 p
  rw [sub724, sub741]
  rfl
theorem sub774 (p : Pattern) : d71 (change p 132 (some 158)) = d893 p := by
  change (if p 138 then d70 (change p 132 (some 158)) else d24 (change p 132 (some 158))) = d893 p
  rw [sub773, sub741]
  rfl
theorem sub775 (p : Pattern) : d99 (change p 132 (some 158)) = d894 p := by
  change (if p 134 then d71 (change p 132 (some 158)) else d98 (change p 132 (some 158))) = d894 p
  rw [sub774, sub772]
  rfl
theorem sub776 (p : Pattern) : d100 (change p 132 (some 158)) = d895 p := by
  change (if p 133 then d99 (change p 132 (some 158)) else d98 (change p 132 (some 158))) = d895 p
  rw [sub775, sub772]
  rfl
theorem sub777 (p : Pattern) : d269 (change p 132 (some 158)) = d895 p := by
  change d100 (change p 132 (some 158)) = d895 p
  exact sub776 p
theorem sub778 (p : Pattern) : d270 (change p 132 (some 158)) = d895 p := by
  change d100 (change p 132 (some 158)) = d895 p
  exact sub776 p
theorem sub779 (p : Pattern) : d271 (change p 132 (some 158)) = d895 p := by
  change (if p 113 then d270 (change p 132 (some 158)) else d269 (change p 132 (some 158))) = d895 p
  rw [sub778, sub777]
  simp only [ite_self]
theorem sub780 (p : Pattern) : d272 (change p 132 (some 158)) = d896 p := by
  change (if p 112 then d271 (change p 132 (some 158)) else d268 (change p 132 (some 158))) = d896 p
  rw [sub779, sub770]
  rfl
theorem sub781 (p : Pattern) : d273 (change p 132 (some 158)) = d890 p := by
  change d89 (change p 132 (some 158)) = d890 p
  exact sub768 p
theorem sub782 (p : Pattern) : d274 (change p 132 (some 158)) = d891 p := by
  change (if p 113 then d273 (change p 132 (some 158)) else d261 (change p 132 (some 158))) = d891 p
  rw [sub781, sub759]
  rfl
theorem sub783 (p : Pattern) : d109 (change p 132 (some 158)) = d897 p := by
  change (if p 134 then d70 (change p 132 (some 158)) else d97 (change p 132 (some 158))) = d897 p
  rw [sub773, sub771]
  rfl
theorem sub784 (p : Pattern) : d110 (change p 132 (some 158)) = d898 p := by
  change (if p 133 then d109 (change p 132 (some 158)) else d97 (change p 132 (some 158))) = d898 p
  rw [sub783, sub771]
  rfl
theorem sub785 (p : Pattern) : d275 (change p 132 (some 158)) = d898 p := by
  change d110 (change p 132 (some 158)) = d898 p
  exact sub784 p
theorem sub786 (p : Pattern) : d276 (change p 132 (some 158)) = d899 p := by
  change (if p 113 then d275 (change p 132 (some 158)) else d270 (change p 132 (some 158))) = d899 p
  rw [sub785, sub778]
  rfl
theorem sub787 (p : Pattern) : d277 (change p 132 (some 158)) = d900 p := by
  change (if p 112 then d276 (change p 132 (some 158)) else d274 (change p 132 (some 158))) = d900 p
  rw [sub786, sub782]
  rfl
theorem sub788 (p : Pattern) : d278 (change p 132 (some 158)) = d901 p := by
  change (if p 106 then d277 (change p 132 (some 158)) else d272 (change p 132 (some 158))) = d901 p
  rw [sub787, sub780]
  rfl
theorem sub789 (p : Pattern) : d279 (change p 132 (some 158)) = d902 p := by
  change (if p 86 then d278 (change p 132 (some 158)) else d266 (change p 132 (some 158))) = d902 p
  rw [sub788, sub764]
  rfl
theorem sub790 (p : Pattern) : d280 (change p 132 (some 158)) = d879 p := by
  change d28 (change p 132 (some 158)) = d879 p
  exact sub745 p
theorem sub791 (p : Pattern) : d281 (change p 132 (some 158)) = d879 p := by
  change (if p 113 then d280 (change p 132 (some 158)) else d261 (change p 132 (some 158))) = d879 p
  rw [sub790, sub759]
  simp only [ite_self]
theorem sub792 (p : Pattern) : d282 (change p 132 (some 158)) = d881 p := by
  change d47 (change p 132 (some 158)) = d881 p
  exact sub748 p
theorem sub793 (p : Pattern) : d283 (change p 132 (some 158)) = d885 p := by
  change d57 (change p 132 (some 158)) = d885 p
  exact sub755 p
theorem sub794 (p : Pattern) : d284 (change p 132 (some 158)) = d886 p := by
  change (if p 113 then d283 (change p 132 (some 158)) else d282 (change p 132 (some 158))) = d886 p
  rw [sub793, sub792]
  rfl
theorem sub795 (p : Pattern) : d285 (change p 132 (some 158)) = d887 p := by
  change (if p 112 then d284 (change p 132 (some 158)) else d281 (change p 132 (some 158))) = d887 p
  rw [sub794, sub791]
  rfl
theorem sub796 (p : Pattern) : d286 (change p 132 (some 158)) = d887 p := by
  change (if p 106 then d285 (change p 132 (some 158)) else d265 (change p 132 (some 158))) = d887 p
  rw [sub795, sub763]
  simp only [ite_self]
theorem sub797 (p : Pattern) : d287 (change p 132 (some 158)) = d903 p := by
  change (if p 113 then d283 (change p 132 (some 158)) else d280 (change p 132 (some 158))) = d903 p
  rw [sub793, sub790]
  rfl
theorem sub798 (p : Pattern) : d288 (change p 132 (some 158)) = d904 p := by
  change (if p 113 then d2 (change p 132 (some 158)) else d275 (change p 132 (some 158))) = d904 p
  rw [sub724, sub785]
  rfl
theorem sub799 (p : Pattern) : d289 (change p 132 (some 158)) = d905 p := by
  change (if p 112 then d288 (change p 132 (some 158)) else d287 (change p 132 (some 158))) = d905 p
  rw [sub798, sub797]
  rfl
theorem sub800 (p : Pattern) : d290 (change p 132 (some 158)) = d906 p := by
  change (if p 106 then d289 (change p 132 (some 158)) else d277 (change p 132 (some 158))) = d906 p
  rw [sub799, sub787]
  rfl
theorem sub801 (p : Pattern) : d291 (change p 132 (some 158)) = d907 p := by
  change (if p 86 then d290 (change p 132 (some 158)) else d286 (change p 132 (some 158))) = d907 p
  rw [sub800, sub796]
  rfl
theorem sub802 (p : Pattern) : d292 (change p 132 (some 158)) = d908 p := by
  change (if p 80 then d291 (change p 132 (some 158)) else d279 (change p 132 (some 158))) = d908 p
  rw [sub801, sub789]
  rfl
theorem sub803 (p : Pattern) : d0 (change p 134 (some 160)) = d0 p := by
  rfl
theorem sub804 (p : Pattern) : d2 (change p 134 (some 160)) = d2 p := by
  rfl
theorem sub805 (p : Pattern) : d3 (change p 134 (some 160)) = d3 p := by
  change (if p 161 then d2 (change p 134 (some 160)) else d0 (change p 134 (some 160))) = d3 p
  rw [sub804, sub803]
  rfl
theorem sub806 (p : Pattern) : d4 (change p 134 (some 160)) = d3 p := by
  change d3 (change p 134 (some 160)) = d3 p
  exact sub805 p
theorem sub807 (p : Pattern) : d5 (change p 134 (some 160)) = d2 p := by
  change d2 (change p 134 (some 160)) = d2 p
  exact sub804 p
theorem sub808 (p : Pattern) : d6 (change p 134 (some 160)) = d744 p := by
  change (if p 159 then d5 (change p 134 (some 160)) else d4 (change p 134 (some 160))) = d744 p
  rw [sub807, sub806]
  rfl
theorem sub809 (p : Pattern) : d7 (change p 134 (some 160)) = d744 p := by
  change (if p 159 then d2 (change p 134 (some 160)) else d4 (change p 134 (some 160))) = d744 p
  rw [sub804, sub806]
  rfl
theorem sub810 (p : Pattern) : d8 (change p 134 (some 160)) = d744 p := by
  change (if p 158 then d7 (change p 134 (some 160)) else d6 (change p 134 (some 160))) = d744 p
  rw [sub809, sub808]
  simp only [ite_self]
theorem sub811 (p : Pattern) : d1 (change p 134 (some 160)) = d1 p := by
  rfl
theorem sub812 (p : Pattern) : d9 (change p 134 (some 160)) = d9 p := by
  change (if p 161 then d2 (change p 134 (some 160)) else d1 (change p 134 (some 160))) = d9 p
  rw [sub804, sub811]
  rfl
theorem sub813 (p : Pattern) : d10 (change p 134 (some 160)) = d9 p := by
  change d9 (change p 134 (some 160)) = d9 p
  exact sub812 p
theorem sub814 (p : Pattern) : d11 (change p 134 (some 160)) = d2 p := by
  change d2 (change p 134 (some 160)) = d2 p
  exact sub804 p
theorem sub815 (p : Pattern) : d12 (change p 134 (some 160)) = d747 p := by
  change (if p 159 then d11 (change p 134 (some 160)) else d10 (change p 134 (some 160))) = d747 p
  rw [sub814, sub813]
  rfl
theorem sub816 (p : Pattern) : d13 (change p 134 (some 160)) = d747 p := by
  change (if p 159 then d2 (change p 134 (some 160)) else d10 (change p 134 (some 160))) = d747 p
  rw [sub804, sub813]
  rfl
theorem sub817 (p : Pattern) : d14 (change p 134 (some 160)) = d747 p := by
  change (if p 158 then d13 (change p 134 (some 160)) else d12 (change p 134 (some 160))) = d747 p
  rw [sub816, sub815]
  simp only [ite_self]
theorem sub818 (p : Pattern) : d15 (change p 134 (some 160)) = d919 p := by
  change (if p 139 then d14 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d919 p
  rw [sub817, sub810]
  rfl
theorem sub819 (p : Pattern) : d16 (change p 134 (some 160)) = d920 p := by
  change (if p 138 then d15 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d920 p
  rw [sub818, sub810]
  rfl
theorem sub820 (p : Pattern) : d328 (change p 134 (some 160)) = d920 p := by
  change d16 (change p 134 (some 160)) = d920 p
  exact sub819 p
theorem sub821 (p : Pattern) : d37 (change p 134 (some 160)) = d2 p := by
  change (if p 159 then d2 (change p 134 (some 160)) else d5 (change p 134 (some 160))) = d2 p
  rw [sub804, sub807]
  simp only [ite_self]
theorem sub822 (p : Pattern) : d38 (change p 134 (some 160)) = d921 p := by
  change (if p 158 then d37 (change p 134 (some 160)) else d6 (change p 134 (some 160))) = d921 p
  rw [sub821, sub808]
  rfl
theorem sub823 (p : Pattern) : d39 (change p 134 (some 160)) = d2 p := by
  change (if p 159 then d2 (change p 134 (some 160)) else d11 (change p 134 (some 160))) = d2 p
  rw [sub804, sub814]
  simp only [ite_self]
theorem sub824 (p : Pattern) : d40 (change p 134 (some 160)) = d922 p := by
  change (if p 158 then d39 (change p 134 (some 160)) else d12 (change p 134 (some 160))) = d922 p
  rw [sub823, sub815]
  rfl
theorem sub825 (p : Pattern) : d41 (change p 134 (some 160)) = d923 p := by
  change (if p 139 then d40 (change p 134 (some 160)) else d38 (change p 134 (some 160))) = d923 p
  rw [sub824, sub822]
  rfl
theorem sub826 (p : Pattern) : d42 (change p 134 (some 160)) = d924 p := by
  change (if p 138 then d41 (change p 134 (some 160)) else d38 (change p 134 (some 160))) = d924 p
  rw [sub825, sub822]
  rfl
theorem sub827 (p : Pattern) : d329 (change p 134 (some 160)) = d924 p := by
  change d42 (change p 134 (some 160)) = d924 p
  exact sub826 p
theorem sub828 (p : Pattern) : d330 (change p 134 (some 160)) = d925 p := by
  change (if p 133 then d329 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d925 p
  rw [sub827, sub820]
  rfl
theorem sub829 (p : Pattern) : d331 (change p 134 (some 160)) = d926 p := by
  change (if p 132 then d330 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d926 p
  rw [sub828, sub820]
  rfl
theorem sub830 (p : Pattern) : d332 (change p 134 (some 160)) = d919 p := by
  change d15 (change p 134 (some 160)) = d919 p
  exact sub818 p
theorem sub831 (p : Pattern) : d333 (change p 134 (some 160)) = d923 p := by
  change d41 (change p 134 (some 160)) = d923 p
  exact sub825 p
theorem sub832 (p : Pattern) : d334 (change p 134 (some 160)) = d927 p := by
  change (if p 133 then d333 (change p 134 (some 160)) else d332 (change p 134 (some 160))) = d927 p
  rw [sub831, sub830]
  rfl
theorem sub833 (p : Pattern) : d335 (change p 134 (some 160)) = d928 p := by
  change (if p 132 then d334 (change p 134 (some 160)) else d332 (change p 134 (some 160))) = d928 p
  rw [sub832, sub830]
  rfl
theorem sub834 (p : Pattern) : d52 (change p 134 (some 160)) = d929 p := by
  change (if p 139 then d2 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d929 p
  rw [sub804, sub810]
  rfl
theorem sub835 (p : Pattern) : d53 (change p 134 (some 160)) = d930 p := by
  change (if p 138 then d52 (change p 134 (some 160)) else d15 (change p 134 (some 160))) = d930 p
  rw [sub834, sub818]
  rfl
theorem sub836 (p : Pattern) : d336 (change p 134 (some 160)) = d930 p := by
  change d53 (change p 134 (some 160)) = d930 p
  exact sub835 p
theorem sub837 (p : Pattern) : d61 (change p 134 (some 160)) = d931 p := by
  change (if p 139 then d2 (change p 134 (some 160)) else d38 (change p 134 (some 160))) = d931 p
  rw [sub804, sub822]
  rfl
theorem sub838 (p : Pattern) : d62 (change p 134 (some 160)) = d932 p := by
  change (if p 138 then d61 (change p 134 (some 160)) else d41 (change p 134 (some 160))) = d932 p
  rw [sub837, sub825]
  rfl
theorem sub839 (p : Pattern) : d337 (change p 134 (some 160)) = d932 p := by
  change d62 (change p 134 (some 160)) = d932 p
  exact sub838 p
end NetHack.Sokoban32Refined
