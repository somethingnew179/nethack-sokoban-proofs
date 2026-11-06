/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions47
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s7200 (pattern : Twelve) : d1657 (change pattern 0 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 0 12) else d1651 (change pattern 0 12)) = d1657 pattern
  rw [s7167, s7199]
  rfl
theorem s7201 (pattern : Twelve) : d1660 (change pattern 0 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 0 12) else d1656 (change pattern 0 12)) = d1660 pattern
  rw [s7200, s7195]
  rfl
theorem s7202 (pattern : Twelve) : d1652 (change pattern 0 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 0 12) else d817 (change pattern 0 12)) = d1652 pattern
  rw [s7196, s7083]
  rfl
theorem s7203 (pattern : Twelve) : d1653 (change pattern 0 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d821 (change pattern 0 12)) = d1653 pattern
  rw [s6978, s7104]
  rfl
theorem s7204 (pattern : Twelve) : d1658 (change pattern 0 12) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 0 12) else d1652 (change pattern 0 12)) = d1658 pattern
  rw [s7203, s7202]
  rfl
theorem s7205 (pattern : Twelve) : d1646 (change pattern 0 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 0 12) else d20 (change pattern 0 12)) = d1646 pattern
  rw [s6996, s6988]
  rfl
theorem s7206 (pattern : Twelve) : d128 (change pattern 0 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 0 12) else d20 (change pattern 0 12)) = d128 pattern
  rw [s6978, s6988]
  rfl
theorem s7207 (pattern : Twelve) : d1648 (change pattern 0 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 0 12) else d1646 (change pattern 0 12)) = d1648 pattern
  rw [s7206, s7205]
  rfl
theorem s7208 (pattern : Twelve) : d1654 (change pattern 0 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 0 12) else d1289 (change pattern 0 12)) = d1654 pattern
  rw [s7207, s7166]
  rfl
theorem s7209 (pattern : Twelve) : d1655 (change pattern 0 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 0 12) else d822 (change pattern 0 12)) = d1655 pattern
  rw [s6978, s7105]
  rfl
theorem s7210 (pattern : Twelve) : d1659 (change pattern 0 12) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 0 12) else d1654 (change pattern 0 12)) = d1659 pattern
  rw [s7209, s7208]
  rfl
theorem s7211 (pattern : Twelve) : d1661 (change pattern 0 12) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 0 12) else d1658 (change pattern 0 12)) = d1661 pattern
  rw [s7210, s7204]
  rfl
theorem s7212 (pattern : Twelve) : d1662 (change pattern 0 12) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 0 12) else d1657 (change pattern 0 12)) = d1662 pattern
  rw [s6978, s7200]
  rfl
theorem s7213 (pattern : Twelve) : d1663 (change pattern 0 12) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 0 12) else d1661 (change pattern 0 12)) = d1663 pattern
  rw [s7212, s7211]
  rfl
theorem s7214 (pattern : Twelve) : d1664 (change pattern 0 12) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 0 12) else d1660 (change pattern 0 12)) = d1664 pattern
  rw [s7213, s7201]
  rfl
theorem s7215 (pattern : Twelve) : d1834 (change pattern 0 12) = d1664 pattern := by
  change d1664 (change pattern 0 12) = d1664 pattern
  exact s7214 pattern
theorem s7216 (pattern : Twelve) : d120 (change pattern 12 0) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 12 0) else d17 (change pattern 12 0)) = d120 pattern
  rw [s6331, s6265]
  rfl
theorem s7217 (pattern : Twelve) : d129 (change pattern 12 0) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 12 0) else d120 (change pattern 12 0)) = d129 pattern
  rw [s6279, s7216]
  rfl
theorem s7218 (pattern : Twelve) : d136 (change pattern 12 0) = d136 pattern := by
  change (if pattern.f then d129 (change pattern 12 0) else d0 (change pattern 12 0)) = d136 pattern
  rw [s7217, s6261]
  rfl
theorem s7219 (pattern : Twelve) : d144 (change pattern 12 0) = d144 pattern := by
  change (if pattern.e then d136 (change pattern 12 0) else d72 (change pattern 12 0)) = d144 pattern
  rw [s7218, s6268]
  rfl
theorem s7220 (pattern : Twelve) : d121 (change pattern 12 0) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 12 0) else d0 (change pattern 12 0)) = d121 pattern
  rw [s6299, s6261]
  rfl
theorem s7221 (pattern : Twelve) : d130 (change pattern 12 0) = d130 pattern := by
  change (if pattern.h then d36 (change pattern 12 0) else d121 (change pattern 12 0)) = d130 pattern
  rw [s6309, s7220]
  rfl
theorem s7222 (pattern : Twelve) : d137 (change pattern 12 0) = d137 pattern := by
  change (if pattern.f then d130 (change pattern 12 0) else d52 (change pattern 12 0)) = d137 pattern
  rw [s7221, s6290]
  rfl
theorem s7223 (pattern : Twelve) : d138 (change pattern 12 0) = d138 pattern := by
  change (if pattern.f then d129 (change pattern 12 0) else d56 (change pattern 12 0)) = d138 pattern
  rw [s7217, s6308]
  rfl
theorem s7224 (pattern : Twelve) : d145 (change pattern 12 0) = d145 pattern := by
  change (if pattern.e then d138 (change pattern 12 0) else d137 (change pattern 12 0)) = d145 pattern
  rw [s7223, s7222]
  rfl
theorem s7225 (pattern : Twelve) : d149 (change pattern 12 0) = d149 pattern := by
  change (if pattern.j then d145 (change pattern 12 0) else d144 (change pattern 12 0)) = d149 pattern
  rw [s7224, s7219]
  rfl
theorem s7226 (pattern : Twelve) : d139 (change pattern 12 0) = d139 pattern := by
  change (if pattern.f then d130 (change pattern 12 0) else d56 (change pattern 12 0)) = d139 pattern
  rw [s7221, s6308]
  rfl
theorem s7227 (pattern : Twelve) : d146 (change pattern 12 0) = d146 pattern := by
  change (if pattern.e then d138 (change pattern 12 0) else d139 (change pattern 12 0)) = d146 pattern
  rw [s7223, s7226]
  rfl
theorem s7228 (pattern : Twelve) : d150 (change pattern 12 0) = d150 pattern := by
  change (if pattern.j then d146 (change pattern 12 0) else d144 (change pattern 12 0)) = d150 pattern
  rw [s7227, s7219]
  rfl
theorem s7229 (pattern : Twelve) : d153 (change pattern 12 0) = d153 pattern := by
  change (if pattern.d then d150 (change pattern 12 0) else d149 (change pattern 12 0)) = d153 pattern
  rw [s7228, s7225]
  rfl
theorem s7230 (pattern : Twelve) : d122 (change pattern 12 0) = d122 pattern := by
  change (if pattern.i then d4 (change pattern 12 0) else d17 (change pattern 12 0)) = d122 pattern
  rw [s6286, s6265]
  rfl
theorem s7231 (pattern : Twelve) : d131 (change pattern 12 0) = d131 pattern := by
  change (if pattern.h then d122 (change pattern 12 0) else d121 (change pattern 12 0)) = d131 pattern
  rw [s7230, s7220]
  rfl
theorem s7232 (pattern : Twelve) : d140 (change pattern 12 0) = d140 pattern := by
  change (if pattern.f then d131 (change pattern 12 0) else d30 (change pattern 12 0)) = d140 pattern
  rw [s7231, s6283]
  rfl
theorem s7233 (pattern : Twelve) : d123 (change pattern 12 0) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d0 (change pattern 12 0)) = d123 pattern
  rw [s6271, s6261]
  rfl
theorem s7234 (pattern : Twelve) : d132 (change pattern 12 0) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 12 0) else d30 (change pattern 12 0)) = d132 pattern
  rw [s7233, s6283]
  rfl
theorem s7235 (pattern : Twelve) : d141 (change pattern 12 0) = d141 pattern := by
  change (if pattern.f then d129 (change pattern 12 0) else d132 (change pattern 12 0)) = d141 pattern
  rw [s7217, s7234]
  rfl
theorem s7236 (pattern : Twelve) : d147 (change pattern 12 0) = d147 pattern := by
  change (if pattern.e then d141 (change pattern 12 0) else d140 (change pattern 12 0)) = d147 pattern
  rw [s7235, s7232]
  rfl
theorem s7237 (pattern : Twelve) : d118 (change pattern 12 0) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 12 0) else d5 (change pattern 12 0)) = d118 pattern
  rw [s6291, s6284]
  rfl
theorem s7238 (pattern : Twelve) : d124 (change pattern 12 0) = d124 pattern := by
  change (if pattern.i then d118 (change pattern 12 0) else d2 (change pattern 12 0)) = d124 pattern
  rw [s7237, s6269]
  rfl
theorem s7239 (pattern : Twelve) : d133 (change pattern 12 0) = d133 pattern := by
  change (if pattern.h then d125 (change pattern 12 0) else d124 (change pattern 12 0)) = d133 pattern
  rw [s6461, s7238]
  rfl
theorem s7240 (pattern : Twelve) : d142 (change pattern 12 0) = d142 pattern := by
  change (if pattern.f then d133 (change pattern 12 0) else d59 (change pattern 12 0)) = d142 pattern
  rw [s7239, s6323]
  rfl
theorem s7241 (pattern : Twelve) : d126 (change pattern 12 0) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 12 0) else d2 (change pattern 12 0)) = d126 pattern
  rw [s6284, s6269]
  rfl
theorem s7242 (pattern : Twelve) : d134 (change pattern 12 0) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 12 0) else d126 (change pattern 12 0)) = d134 pattern
  rw [s6364, s7241]
  rfl
theorem s7243 (pattern : Twelve) : d127 (change pattern 12 0) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d23 (change pattern 12 0)) = d127 pattern
  rw [s6296, s6299]
  rfl
theorem s7244 (pattern : Twelve) : d135 (change pattern 12 0) = d135 pattern := by
  change (if pattern.h then d128 (change pattern 12 0) else d127 (change pattern 12 0)) = d135 pattern
  rw [s6503, s7243]
  rfl
theorem s7245 (pattern : Twelve) : d143 (change pattern 12 0) = d143 pattern := by
  change (if pattern.f then d135 (change pattern 12 0) else d134 (change pattern 12 0)) = d143 pattern
  rw [s7244, s7242]
  rfl
theorem s7246 (pattern : Twelve) : d148 (change pattern 12 0) = d148 pattern := by
  change (if pattern.e then d143 (change pattern 12 0) else d142 (change pattern 12 0)) = d148 pattern
  rw [s7245, s7240]
  rfl
theorem s7247 (pattern : Twelve) : d151 (change pattern 12 0) = d151 pattern := by
  change (if pattern.j then d148 (change pattern 12 0) else d147 (change pattern 12 0)) = d151 pattern
  rw [s7246, s7236]
  rfl
theorem s7248 (pattern : Twelve) : d152 (change pattern 12 0) = d152 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d146 (change pattern 12 0)) = d152 pattern
  rw [s6278, s7227]
  rfl
theorem s7249 (pattern : Twelve) : d154 (change pattern 12 0) = d154 pattern := by
  change (if pattern.d then d152 (change pattern 12 0) else d151 (change pattern 12 0)) = d154 pattern
  rw [s7248, s7247]
  rfl
theorem s7250 (pattern : Twelve) : d155 (change pattern 12 0) = d155 pattern := by
  change (if pattern.c then d154 (change pattern 12 0) else d153 (change pattern 12 0)) = d155 pattern
  rw [s7249, s7229]
  rfl
theorem s7251 (pattern : Twelve) : d778 (change pattern 12 0) = d778 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d2 (change pattern 12 0)) = d778 pattern
  rw [s6271, s6269]
  rfl
theorem s7252 (pattern : Twelve) : d779 (change pattern 12 0) = d779 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d23 (change pattern 12 0)) = d779 pattern
  rw [s6271, s6299]
  rfl
theorem s7253 (pattern : Twelve) : d782 (change pattern 12 0) = d782 pattern := by
  change (if pattern.h then d779 (change pattern 12 0) else d778 (change pattern 12 0)) = d782 pattern
  rw [s7252, s7251]
  rfl
theorem s7254 (pattern : Twelve) : d788 (change pattern 12 0) = d788 pattern := by
  change (if pattern.f then d782 (change pattern 12 0) else d2 (change pattern 12 0)) = d788 pattern
  rw [s7253, s6269]
  rfl
theorem s7255 (pattern : Twelve) : d789 (change pattern 12 0) = d789 pattern := by
  change (if pattern.f then d61 (change pattern 12 0) else d38 (change pattern 12 0)) = d789 pattern
  rw [s6333, s6321]
  rfl
theorem s7256 (pattern : Twelve) : d794 (change pattern 12 0) = d794 pattern := by
  change (if pattern.e then d789 (change pattern 12 0) else d788 (change pattern 12 0)) = d794 pattern
  rw [s7255, s7254]
  rfl
theorem s7257 (pattern : Twelve) : d783 (change pattern 12 0) = d783 pattern := by
  change (if pattern.h then d44 (change pattern 12 0) else d38 (change pattern 12 0)) = d783 pattern
  rw [s6344, s6321]
  rfl
theorem s7258 (pattern : Twelve) : d790 (change pattern 12 0) = d790 pattern := by
  change (if pattern.f then d69 (change pattern 12 0) else d783 (change pattern 12 0)) = d790 pattern
  rw [s6365, s7257]
  rfl
theorem s7259 (pattern : Twelve) : d795 (change pattern 12 0) = d795 pattern := by
  change (if pattern.e then d90 (change pattern 12 0) else d790 (change pattern 12 0)) = d795 pattern
  rw [s6371, s7258]
  rfl
theorem s7260 (pattern : Twelve) : d798 (change pattern 12 0) = d798 pattern := by
  change (if pattern.j then d795 (change pattern 12 0) else d794 (change pattern 12 0)) = d798 pattern
  rw [s7259, s7256]
  rfl
theorem s7261 (pattern : Twelve) : d799 (change pattern 12 0) = d799 pattern := by
  change (if pattern.j then d101 (change pattern 12 0) else d794 (change pattern 12 0)) = d799 pattern
  rw [s6372, s7256]
  rfl
theorem s7262 (pattern : Twelve) : d802 (change pattern 12 0) = d802 pattern := by
  change (if pattern.d then d799 (change pattern 12 0) else d798 (change pattern 12 0)) = d802 pattern
  rw [s7261, s7260]
  rfl
theorem s7263 (pattern : Twelve) : d780 (change pattern 12 0) = d780 pattern := by
  change (if pattern.i then d5 (change pattern 12 0) else d3 (change pattern 12 0)) = d780 pattern
  rw [s6284, s6271]
  rfl
theorem s7264 (pattern : Twelve) : d784 (change pattern 12 0) = d784 pattern := by
  change (if pattern.h then d780 (change pattern 12 0) else d38 (change pattern 12 0)) = d784 pattern
  rw [s7263, s6321]
  rfl
theorem s7265 (pattern : Twelve) : d791 (change pattern 12 0) = d791 pattern := by
  change (if pattern.f then d784 (change pattern 12 0) else d38 (change pattern 12 0)) = d791 pattern
  rw [s7264, s6321]
  rfl
theorem s7266 (pattern : Twelve) : d796 (change pattern 12 0) = d796 pattern := by
  change (if pattern.e then d90 (change pattern 12 0) else d791 (change pattern 12 0)) = d796 pattern
  rw [s6371, s7265]
  rfl
theorem s7267 (pattern : Twelve) : d781 (change pattern 12 0) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d5 (change pattern 12 0)) = d781 pattern
  rw [s6278, s6284]
  rfl
theorem s7268 (pattern : Twelve) : d785 (change pattern 12 0) = d785 pattern := by
  change (if pattern.h then d781 (change pattern 12 0) else d48 (change pattern 12 0)) = d785 pattern
  rw [s7267, s6367]
  rfl
theorem s7269 (pattern : Twelve) : d792 (change pattern 12 0) = d792 pattern := by
  change (if pattern.f then d785 (change pattern 12 0) else d48 (change pattern 12 0)) = d792 pattern
  rw [s7268, s6367]
  rfl
theorem s7270 (pattern : Twelve) : d786 (change pattern 12 0) = d786 pattern := by
  change (if pattern.h then d6 (change pattern 12 0) else d48 (change pattern 12 0)) = d786 pattern
  rw [s6278, s6367]
  rfl
theorem s7271 (pattern : Twelve) : d787 (change pattern 12 0) = d787 pattern := by
  change (if pattern.h then d6 (change pattern 12 0) else d49 (change pattern 12 0)) = d787 pattern
  rw [s6278, s6369]
  rfl
theorem s7272 (pattern : Twelve) : d793 (change pattern 12 0) = d793 pattern := by
  change (if pattern.f then d787 (change pattern 12 0) else d786 (change pattern 12 0)) = d793 pattern
  rw [s7271, s7270]
  rfl
theorem s7273 (pattern : Twelve) : d797 (change pattern 12 0) = d797 pattern := by
  change (if pattern.e then d793 (change pattern 12 0) else d792 (change pattern 12 0)) = d797 pattern
  rw [s7272, s7269]
  rfl
theorem s7274 (pattern : Twelve) : d800 (change pattern 12 0) = d800 pattern := by
  change (if pattern.j then d797 (change pattern 12 0) else d796 (change pattern 12 0)) = d800 pattern
  rw [s7273, s7266]
  rfl
theorem s7275 (pattern : Twelve) : d801 (change pattern 12 0) = d801 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d101 (change pattern 12 0)) = d801 pattern
  rw [s6278, s6372]
  rfl
theorem s7276 (pattern : Twelve) : d803 (change pattern 12 0) = d803 pattern := by
  change (if pattern.d then d801 (change pattern 12 0) else d800 (change pattern 12 0)) = d803 pattern
  rw [s7275, s7274]
  rfl
theorem s7277 (pattern : Twelve) : d804 (change pattern 12 0) = d804 pattern := by
  change (if pattern.c then d803 (change pattern 12 0) else d802 (change pattern 12 0)) = d804 pattern
  rw [s7276, s7262]
  rfl
theorem s7278 (pattern : Twelve) : d805 (change pattern 12 0) = d805 pattern := by
  change (if pattern.g then d804 (change pattern 12 0) else d155 (change pattern 12 0)) = d805 pattern
  rw [s7277, s7250]
  rfl
theorem s7279 (pattern : Twelve) : d806 (change pattern 12 0) = d805 pattern := by
  change d805 (change pattern 12 0) = d805 pattern
  exact s7278 pattern
theorem s7280 (pattern : Twelve) : d874 (change pattern 12 0) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 12 0) else d17 (change pattern 12 0)) = d874 pattern
  rw [s6437, s6265]
  rfl
theorem s7281 (pattern : Twelve) : d875 (change pattern 12 0) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 12 0) else d814 (change pattern 12 0)) = d875 pattern
  rw [s6437, s6378]
  rfl
theorem s7282 (pattern : Twelve) : d882 (change pattern 12 0) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 12 0) else d874 (change pattern 12 0)) = d882 pattern
  rw [s7281, s7280]
  rfl
theorem s7283 (pattern : Twelve) : d890 (change pattern 12 0) = d890 pattern := by
  change (if pattern.f then d882 (change pattern 12 0) else d0 (change pattern 12 0)) = d890 pattern
  rw [s7282, s6261]
  rfl
theorem s7284 (pattern : Twelve) : d876 (change pattern 12 0) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 12 0) else d19 (change pattern 12 0)) = d876 pattern
  rw [s6292, s6277]
  rfl
theorem s7285 (pattern : Twelve) : d883 (change pattern 12 0) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 12 0) else d876 (change pattern 12 0)) = d883 pattern
  rw [s6332, s7284]
  rfl
theorem s7286 (pattern : Twelve) : d891 (change pattern 12 0) = d891 pattern := by
  change (if pattern.f then d883 (change pattern 12 0) else d17 (change pattern 12 0)) = d891 pattern
  rw [s7285, s6265]
  rfl
theorem s7287 (pattern : Twelve) : d898 (change pattern 12 0) = d898 pattern := by
  change (if pattern.e then d891 (change pattern 12 0) else d890 (change pattern 12 0)) = d898 pattern
  rw [s7286, s7283]
  rfl
theorem s7288 (pattern : Twelve) : d877 (change pattern 12 0) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 12 0) else d17 (change pattern 12 0)) = d877 pattern
  rw [s6398, s6265]
  rfl
theorem s7289 (pattern : Twelve) : d884 (change pattern 12 0) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 12 0) else d877 (change pattern 12 0)) = d884 pattern
  rw [s6386, s7288]
  rfl
theorem s7290 (pattern : Twelve) : d892 (change pattern 12 0) = d892 pattern := by
  change (if pattern.f then d884 (change pattern 12 0) else d56 (change pattern 12 0)) = d892 pattern
  rw [s7289, s6308]
  rfl
theorem s7291 (pattern : Twelve) : d893 (change pattern 12 0) = d893 pattern := by
  change (if pattern.f then d883 (change pattern 12 0) else d827 (change pattern 12 0)) = d893 pattern
  rw [s7285, s6389]
  rfl
theorem s7292 (pattern : Twelve) : d899 (change pattern 12 0) = d899 pattern := by
  change (if pattern.e then d893 (change pattern 12 0) else d892 (change pattern 12 0)) = d899 pattern
  rw [s7291, s7290]
  rfl
theorem s7293 (pattern : Twelve) : d902 (change pattern 12 0) = d902 pattern := by
  change (if pattern.j then d899 (change pattern 12 0) else d898 (change pattern 12 0)) = d902 pattern
  rw [s7292, s7287]
  rfl
theorem s7294 (pattern : Twelve) : d878 (change pattern 12 0) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 12 0) else d814 (change pattern 12 0)) = d878 pattern
  rw [s6328, s6378]
  rfl
theorem s7295 (pattern : Twelve) : d885 (change pattern 12 0) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 12 0) else d877 (change pattern 12 0)) = d885 pattern
  rw [s7294, s7288]
  rfl
theorem s7296 (pattern : Twelve) : d894 (change pattern 12 0) = d894 pattern := by
  change (if pattern.f then d885 (change pattern 12 0) else d30 (change pattern 12 0)) = d894 pattern
  rw [s7295, s6283]
  rfl
theorem s7297 (pattern : Twelve) : d879 (change pattern 12 0) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 12 0) else d17 (change pattern 12 0)) = d879 pattern
  rw [s6453, s6265]
  rfl
theorem s7298 (pattern : Twelve) : d886 (change pattern 12 0) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 12 0) else d34 (change pattern 12 0)) = d886 pattern
  rw [s7297, s6300]
  rfl
theorem s7299 (pattern : Twelve) : d895 (change pattern 12 0) = d895 pattern := by
  change (if pattern.f then d883 (change pattern 12 0) else d886 (change pattern 12 0)) = d895 pattern
  rw [s7285, s7298]
  rfl
theorem s7300 (pattern : Twelve) : d900 (change pattern 12 0) = d900 pattern := by
  change (if pattern.e then d895 (change pattern 12 0) else d894 (change pattern 12 0)) = d900 pattern
  rw [s7299, s7296]
  rfl
theorem s7301 (pattern : Twelve) : d873 (change pattern 12 0) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 12 0) else d117 (change pattern 12 0)) = d873 pattern
  rw [s6327, s6443]
  rfl
theorem s7302 (pattern : Twelve) : d880 (change pattern 12 0) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d873 (change pattern 12 0)) = d880 pattern
  rw [s6278, s7301]
  rfl
theorem s7303 (pattern : Twelve) : d887 (change pattern 12 0) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 12 0) else d127 (change pattern 12 0)) = d887 pattern
  rw [s7302, s7243]
  rfl
theorem s7304 (pattern : Twelve) : d896 (change pattern 12 0) = d896 pattern := by
  change (if pattern.f then d887 (change pattern 12 0) else d59 (change pattern 12 0)) = d896 pattern
  rw [s7303, s6323]
  rfl
theorem s7305 (pattern : Twelve) : d881 (change pattern 12 0) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 12 0) else d23 (change pattern 12 0)) = d881 pattern
  rw [s7237, s6299]
  rfl
theorem s7306 (pattern : Twelve) : d888 (change pattern 12 0) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 12 0) else d881 (change pattern 12 0)) = d888 pattern
  rw [s6461, s7305]
  rfl
theorem s7307 (pattern : Twelve) : d889 (change pattern 12 0) = d889 pattern := by
  change (if pattern.h then d6 (change pattern 12 0) else d42 (change pattern 12 0)) = d889 pattern
  rw [s6278, s6332]
  rfl
theorem s7308 (pattern : Twelve) : d897 (change pattern 12 0) = d897 pattern := by
  change (if pattern.f then d889 (change pattern 12 0) else d888 (change pattern 12 0)) = d897 pattern
  rw [s7307, s7306]
  rfl
theorem s7309 (pattern : Twelve) : d901 (change pattern 12 0) = d901 pattern := by
  change (if pattern.e then d897 (change pattern 12 0) else d896 (change pattern 12 0)) = d901 pattern
  rw [s7308, s7304]
  rfl
theorem s7310 (pattern : Twelve) : d903 (change pattern 12 0) = d903 pattern := by
  change (if pattern.j then d901 (change pattern 12 0) else d900 (change pattern 12 0)) = d903 pattern
  rw [s7309, s7300]
  rfl
theorem s7311 (pattern : Twelve) : d904 (change pattern 12 0) = d904 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d899 (change pattern 12 0)) = d904 pattern
  rw [s6278, s7292]
  rfl
theorem s7312 (pattern : Twelve) : d905 (change pattern 12 0) = d905 pattern := by
  change (if pattern.d then d904 (change pattern 12 0) else d903 (change pattern 12 0)) = d905 pattern
  rw [s7311, s7310]
  rfl
theorem s7313 (pattern : Twelve) : d906 (change pattern 12 0) = d906 pattern := by
  change (if pattern.c then d905 (change pattern 12 0) else d902 (change pattern 12 0)) = d906 pattern
  rw [s7312, s7293]
  rfl
theorem s7314 (pattern : Twelve) : d1247 (change pattern 12 0) = d1247 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d815 (change pattern 12 0)) = d1247 pattern
  rw [s6271, s6398]
  rfl
theorem s7315 (pattern : Twelve) : d1249 (change pattern 12 0) = d1249 pattern := by
  change (if pattern.h then d1247 (change pattern 12 0) else d779 (change pattern 12 0)) = d1249 pattern
  rw [s7314, s7252]
  rfl
theorem s7316 (pattern : Twelve) : d1253 (change pattern 12 0) = d1253 pattern := by
  change (if pattern.f then d1249 (change pattern 12 0) else d2 (change pattern 12 0)) = d1253 pattern
  rw [s7315, s6269]
  rfl
theorem s7317 (pattern : Twelve) : d1248 (change pattern 12 0) = d1248 pattern := by
  change (if pattern.i then d4 (change pattern 12 0) else d23 (change pattern 12 0)) = d1248 pattern
  rw [s6286, s6299]
  rfl
theorem s7318 (pattern : Twelve) : d1254 (change pattern 12 0) = d1254 pattern := by
  change (if pattern.f then d831 (change pattern 12 0) else d1248 (change pattern 12 0)) = d1254 pattern
  rw [s6405, s7317]
  rfl
theorem s7319 (pattern : Twelve) : d1258 (change pattern 12 0) = d1258 pattern := by
  change (if pattern.e then d1254 (change pattern 12 0) else d1253 (change pattern 12 0)) = d1258 pattern
  rw [s7318, s7316]
  rfl
theorem s7320 (pattern : Twelve) : d1261 (change pattern 12 0) = d1261 pattern := by
  change (if pattern.j then d860 (change pattern 12 0) else d1258 (change pattern 12 0)) = d1261 pattern
  rw [s6430, s7319]
  rfl
theorem s7321 (pattern : Twelve) : d1250 (change pattern 12 0) = d1250 pattern := by
  change (if pattern.h then d780 (change pattern 12 0) else d41 (change pattern 12 0)) = d1250 pattern
  rw [s7263, s6329]
  rfl
theorem s7322 (pattern : Twelve) : d1255 (change pattern 12 0) = d1255 pattern := by
  change (if pattern.f then d1250 (change pattern 12 0) else d38 (change pattern 12 0)) = d1255 pattern
  rw [s7321, s6321]
  rfl
theorem s7323 (pattern : Twelve) : d1259 (change pattern 12 0) = d1259 pattern := by
  change (if pattern.e then d852 (change pattern 12 0) else d1255 (change pattern 12 0)) = d1259 pattern
  rw [s6429, s7322]
  rfl
theorem s7324 (pattern : Twelve) : d1251 (change pattern 12 0) = d1251 pattern := by
  change (if pattern.h then d781 (change pattern 12 0) else d49 (change pattern 12 0)) = d1251 pattern
  rw [s7267, s6369]
  rfl
theorem s7325 (pattern : Twelve) : d1256 (change pattern 12 0) = d1256 pattern := by
  change (if pattern.f then d1251 (change pattern 12 0) else d48 (change pattern 12 0)) = d1256 pattern
  rw [s7324, s6367]
  rfl
theorem s7326 (pattern : Twelve) : d1252 (change pattern 12 0) = d1252 pattern := by
  change (if pattern.h then d6 (change pattern 12 0) else d822 (change pattern 12 0)) = d1252 pattern
  rw [s6278, s6404]
  rfl
theorem s7327 (pattern : Twelve) : d1257 (change pattern 12 0) = d1257 pattern := by
  change (if pattern.f then d1252 (change pattern 12 0) else d787 (change pattern 12 0)) = d1257 pattern
  rw [s7326, s7271]
  rfl
theorem s7328 (pattern : Twelve) : d1260 (change pattern 12 0) = d1260 pattern := by
  change (if pattern.e then d1257 (change pattern 12 0) else d1256 (change pattern 12 0)) = d1260 pattern
  rw [s7327, s7325]
  rfl
theorem s7329 (pattern : Twelve) : d1262 (change pattern 12 0) = d1262 pattern := by
  change (if pattern.j then d1260 (change pattern 12 0) else d1259 (change pattern 12 0)) = d1262 pattern
  rw [s7328, s7323]
  rfl
theorem s7330 (pattern : Twelve) : d1263 (change pattern 12 0) = d1263 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d860 (change pattern 12 0)) = d1263 pattern
  rw [s6278, s6430]
  rfl
theorem s7331 (pattern : Twelve) : d1264 (change pattern 12 0) = d1264 pattern := by
  change (if pattern.d then d1263 (change pattern 12 0) else d1262 (change pattern 12 0)) = d1264 pattern
  rw [s7330, s7329]
  rfl
theorem s7332 (pattern : Twelve) : d1265 (change pattern 12 0) = d1265 pattern := by
  change (if pattern.c then d1264 (change pattern 12 0) else d1261 (change pattern 12 0)) = d1265 pattern
  rw [s7331, s7320]
  rfl
theorem s7333 (pattern : Twelve) : d1266 (change pattern 12 0) = d1266 pattern := by
  change (if pattern.g then d1265 (change pattern 12 0) else d906 (change pattern 12 0)) = d1266 pattern
  rw [s7332, s7313]
  rfl
theorem s7334 (pattern : Twelve) : d1267 (change pattern 12 0) = d1266 pattern := by
  change d1266 (change pattern 12 0) = d1266 pattern
  exact s7333 pattern
theorem s7335 (pattern : Twelve) : d1325 (change pattern 12 0) = d1325 pattern := by
  change (if pattern.i then d1324 (change pattern 12 0) else d1275 (change pattern 12 0)) = d1325 pattern
  rw [s6489, s6436]
  rfl
theorem s7336 (pattern : Twelve) : d1326 (change pattern 12 0) = d1326 pattern := by
  change (if pattern.i then d1324 (change pattern 12 0) else d872 (change pattern 12 0)) = d1326 pattern
  rw [s6489, s6437]
  rfl
theorem s7337 (pattern : Twelve) : d1333 (change pattern 12 0) = d1333 pattern := by
  change (if pattern.h then d1326 (change pattern 12 0) else d1325 (change pattern 12 0)) = d1333 pattern
  rw [s7336, s7335]
  rfl
theorem s7338 (pattern : Twelve) : d1339 (change pattern 12 0) = d1339 pattern := by
  change (if pattern.f then d1333 (change pattern 12 0) else d17 (change pattern 12 0)) = d1339 pattern
  rw [s7337, s6265]
  rfl
theorem s7339 (pattern : Twelve) : d1345 (change pattern 12 0) = d1345 pattern := by
  change (if pattern.e then d1294 (change pattern 12 0) else d1339 (change pattern 12 0)) = d1345 pattern
  rw [s6441, s7338]
  rfl
theorem s7340 (pattern : Twelve) : d1327 (change pattern 12 0) = d1327 pattern := by
  change (if pattern.i then d119 (change pattern 12 0) else d1275 (change pattern 12 0)) = d1327 pattern
  rw [s6453, s6436]
  rfl
theorem s7341 (pattern : Twelve) : d1334 (change pattern 12 0) = d1334 pattern := by
  change (if pattern.h then d1280 (change pattern 12 0) else d1327 (change pattern 12 0)) = d1334 pattern
  rw [s6446, s7340]
  rfl
theorem s7342 (pattern : Twelve) : d1340 (change pattern 12 0) = d1340 pattern := by
  change (if pattern.f then d1334 (change pattern 12 0) else d827 (change pattern 12 0)) = d1340 pattern
  rw [s7341, s6389]
  rfl
theorem s7343 (pattern : Twelve) : d1346 (change pattern 12 0) = d1346 pattern := by
  change (if pattern.e then d1296 (change pattern 12 0) else d1340 (change pattern 12 0)) = d1346 pattern
  rw [s6450, s7342]
  rfl
theorem s7344 (pattern : Twelve) : d1349 (change pattern 12 0) = d1349 pattern := by
  change (if pattern.j then d1346 (change pattern 12 0) else d1345 (change pattern 12 0)) = d1349 pattern
  rw [s7343, s7339]
  rfl
theorem s7345 (pattern : Twelve) : d1328 (change pattern 12 0) = d1328 pattern := by
  change (if pattern.i then d1277 (change pattern 12 0) else d872 (change pattern 12 0)) = d1328 pattern
  rw [s6459, s6437]
  rfl
theorem s7346 (pattern : Twelve) : d1335 (change pattern 12 0) = d1335 pattern := by
  change (if pattern.h then d1328 (change pattern 12 0) else d1327 (change pattern 12 0)) = d1335 pattern
  rw [s7345, s7340]
  rfl
theorem s7347 (pattern : Twelve) : d1341 (change pattern 12 0) = d1341 pattern := by
  change (if pattern.f then d1335 (change pattern 12 0) else d34 (change pattern 12 0)) = d1341 pattern
  rw [s7346, s6300]
  rfl
theorem s7348 (pattern : Twelve) : d1329 (change pattern 12 0) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 12 0) else d19 (change pattern 12 0)) = d1329 pattern
  rw [s6288, s6277]
  rfl
theorem s7349 (pattern : Twelve) : d1336 (change pattern 12 0) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 12 0) else d817 (change pattern 12 0)) = d1336 pattern
  rw [s7348, s6382]
  rfl
end NetHack.Sokoban21.Diagram
