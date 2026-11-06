/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions59
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7200 (p : Pattern) : d755 (change p 160 (some 138)) = d4736 p := by
  change d747 (change p 160 (some 138)) = d4736 p
  exact sub7192 p
theorem sub7201 (p : Pattern) : d756 (change p 160 (some 138)) = d12 p := by
  change d12 (change p 160 (some 138)) = d12 p
  exact sub7095 p
theorem sub7202 (p : Pattern) : d757 (change p 160 (some 138)) = d4972 p := by
  change (if p 116 then d756 (change p 160 (some 138)) else d755 (change p 160 (some 138))) = d4972 p
  rw [sub7201, sub7200]
  rfl
theorem sub7203 (p : Pattern) : d758 (change p 160 (some 138)) = d4973 p := by
  change (if p 115 then d757 (change p 160 (some 138)) else d752 (change p 160 (some 138))) = d4973 p
  rw [sub7202, sub7199]
  rfl
theorem sub7204 (p : Pattern) : d759 (change p 160 (some 138)) = d4974 p := by
  change (if p 71 then d758 (change p 160 (some 138)) else d731 (change p 160 (some 138))) = d4974 p
  rw [sub7203, sub7156]
  rfl
theorem sub7205 (p : Pattern) : d760 (change p 160 (some 138)) = d4975 p := by
  change (if p 49 then d759 (change p 160 (some 138)) else d741 (change p 160 (some 138))) = d4975 p
  rw [sub7204, sub7163]
  rfl
theorem sub7206 (p : Pattern) : d6 (change p 160 (some 138)) = d6 p := by
  rfl
theorem sub7207 (p : Pattern) : d34 (change p 160 (some 138)) = d34 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d6 (change p 160 (some 138))) = d34 p
  rw [sub7095, sub7206]
  rfl
theorem sub7208 (p : Pattern) : d35 (change p 160 (some 138)) = d35 p := by
  change (if p 246 then d34 (change p 160 (some 138)) else d6 (change p 160 (some 138))) = d35 p
  rw [sub7207, sub7206]
  rfl
theorem sub7209 (p : Pattern) : d36 (change p 160 (some 138)) = d36 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d35 (change p 160 (some 138))) = d36 p
  rw [sub7095, sub7208]
  rfl
theorem sub7210 (p : Pattern) : d78 (change p 160 (some 138)) = d78 p := by
  change (if p 182 then d36 (change p 160 (some 138)) else d35 (change p 160 (some 138))) = d78 p
  rw [sub7209, sub7208]
  rfl
theorem sub7211 (p : Pattern) : d79 (change p 160 (some 138)) = d79 p := by
  change (if p 163 then d78 (change p 160 (some 138)) else d53 (change p 160 (some 138))) = d79 p
  rw [sub7210, sub7120]
  rfl
theorem sub7212 (p : Pattern) : d188 (change p 160 (some 138)) = d188 p := by
  change (if p 162 then d79 (change p 160 (some 138)) else d16 (change p 160 (some 138))) = d188 p
  rw [sub7211, sub7099]
  rfl
theorem sub7213 (p : Pattern) : d80 (change p 160 (some 138)) = d80 p := by
  change (if p 162 then d63 (change p 160 (some 138)) else d79 (change p 160 (some 138))) = d80 p
  rw [sub7135, sub7211]
  rfl
theorem sub7214 (p : Pattern) : d189 (change p 160 (some 138)) = d189 p := by
  change (if p 161 then d80 (change p 160 (some 138)) else d188 (change p 160 (some 138))) = d189 p
  rw [sub7213, sub7212]
  rfl
theorem sub7215 (p : Pattern) : d761 (change p 160 (some 138)) = d189 p := by
  change d189 (change p 160 (some 138)) = d189 p
  exact sub7214 p
theorem sub7216 (p : Pattern) : d198 (change p 160 (some 138)) = d198 p := by
  change (if p 163 then d62 (change p 160 (some 138)) else d20 (change p 160 (some 138))) = d198 p
  rw [sub7134, sub7104]
  rfl
theorem sub7217 (p : Pattern) : d199 (change p 160 (some 138)) = d199 p := by
  change (if p 162 then d198 (change p 160 (some 138)) else d53 (change p 160 (some 138))) = d199 p
  rw [sub7216, sub7120]
  rfl
theorem sub7218 (p : Pattern) : d83 (change p 160 (some 138)) = d83 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d78 (change p 160 (some 138))) = d83 p
  rw [sub7095, sub7210]
  rfl
theorem sub7219 (p : Pattern) : d84 (change p 160 (some 138)) = d84 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d83 (change p 160 (some 138))) = d84 p
  rw [sub7095, sub7218]
  rfl
theorem sub7220 (p : Pattern) : d200 (change p 160 (some 138)) = d200 p := by
  change (if p 161 then d84 (change p 160 (some 138)) else d199 (change p 160 (some 138))) = d200 p
  rw [sub7219, sub7217]
  rfl
theorem sub7221 (p : Pattern) : d762 (change p 160 (some 138)) = d200 p := by
  change d200 (change p 160 (some 138)) = d200 p
  exact sub7220 p
theorem sub7222 (p : Pattern) : d763 (change p 160 (some 138)) = d4745 p := by
  change (if p 141 then d762 (change p 160 (some 138)) else d761 (change p 160 (some 138))) = d4745 p
  rw [sub7221, sub7215]
  rfl
theorem sub7223 (p : Pattern) : d764 (change p 160 (some 138)) = d4745 p := by
  change d763 (change p 160 (some 138)) = d4745 p
  exact sub7222 p
theorem sub7224 (p : Pattern) : d765 (change p 160 (some 138)) = d12 p := by
  change d12 (change p 160 (some 138)) = d12 p
  exact sub7095 p
theorem sub7225 (p : Pattern) : d766 (change p 160 (some 138)) = d4976 p := by
  change (if p 116 then d765 (change p 160 (some 138)) else d764 (change p 160 (some 138))) = d4976 p
  rw [sub7224, sub7223]
  rfl
theorem sub7226 (p : Pattern) : d767 (change p 160 (some 138)) = d4977 p := by
  change (if p 115 then d766 (change p 160 (some 138)) else d737 (change p 160 (some 138))) = d4977 p
  rw [sub7225, sub7159]
  rfl
theorem sub7227 (p : Pattern) : d768 (change p 160 (some 138)) = d4978 p := by
  change (if p 71 then d767 (change p 160 (some 138)) else d731 (change p 160 (some 138))) = d4978 p
  rw [sub7226, sub7156]
  rfl
theorem sub7228 (p : Pattern) : d211 (change p 160 (some 138)) = d211 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d109 (change p 160 (some 138))) = d211 p
  rw [sub7095, sub7173]
  rfl
theorem sub7229 (p : Pattern) : d212 (change p 160 (some 138)) = d212 p := by
  change (if p 162 then d211 (change p 160 (some 138)) else d133 (change p 160 (some 138))) = d212 p
  rw [sub7228, sub7185]
  rfl
theorem sub7230 (p : Pattern) : d213 (change p 160 (some 138)) = d213 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d211 (change p 160 (some 138))) = d213 p
  rw [sub7095, sub7228]
  rfl
theorem sub7231 (p : Pattern) : d214 (change p 160 (some 138)) = d214 p := by
  change (if p 161 then d213 (change p 160 (some 138)) else d212 (change p 160 (some 138))) = d214 p
  rw [sub7230, sub7229]
  rfl
theorem sub7232 (p : Pattern) : d771 (change p 160 (some 138)) = d214 p := by
  change d214 (change p 160 (some 138)) = d214 p
  exact sub7231 p
theorem sub7233 (p : Pattern) : d772 (change p 160 (some 138)) = d4751 p := by
  change (if p 141 then d771 (change p 160 (some 138)) else d745 (change p 160 (some 138))) = d4751 p
  rw [sub7232, sub7179]
  rfl
theorem sub7234 (p : Pattern) : d773 (change p 160 (some 138)) = d4751 p := by
  change d772 (change p 160 (some 138)) = d4751 p
  exact sub7233 p
theorem sub7235 (p : Pattern) : d775 (change p 160 (some 138)) = d4737 p := by
  change d162 (change p 160 (some 138)) = d4737 p
  exact sub7197 p
theorem sub7236 (p : Pattern) : d776 (change p 160 (some 138)) = d4979 p := by
  change (if p 116 then d775 (change p 160 (some 138)) else d773 (change p 160 (some 138))) = d4979 p
  rw [sub7235, sub7234]
  rfl
theorem sub7237 (p : Pattern) : d241 (change p 160 (some 138)) = d241 p := by
  change (if p 163 then d62 (change p 160 (some 138)) else d132 (change p 160 (some 138))) = d241 p
  rw [sub7134, sub7184]
  rfl
theorem sub7238 (p : Pattern) : d242 (change p 160 (some 138)) = d242 p := by
  change (if p 162 then d241 (change p 160 (some 138)) else d105 (change p 160 (some 138))) = d242 p
  rw [sub7237, sub7168]
  rfl
theorem sub7239 (p : Pattern) : d243 (change p 160 (some 138)) = d243 p := by
  change (if p 161 then d137 (change p 160 (some 138)) else d242 (change p 160 (some 138))) = d243 p
  rw [sub7189, sub7238]
  rfl
theorem sub7240 (p : Pattern) : d778 (change p 160 (some 138)) = d243 p := by
  change d243 (change p 160 (some 138)) = d243 p
  exact sub7239 p
theorem sub7241 (p : Pattern) : d245 (change p 160 (some 138)) = d245 p := by
  change (if p 162 then d211 (change p 160 (some 138)) else d132 (change p 160 (some 138))) = d245 p
  rw [sub7228, sub7184]
  rfl
theorem sub7242 (p : Pattern) : d7 (change p 160 (some 138)) = d7 p := by
  rfl
theorem sub7243 (p : Pattern) : d119 (change p 160 (some 138)) = d119 p := by
  change (if p 247 then d12 (change p 160 (some 138)) else d7 (change p 160 (some 138))) = d119 p
  rw [sub7095, sub7242]
  rfl
theorem sub7244 (p : Pattern) : d120 (change p 160 (some 138)) = d120 p := by
  change (if p 246 then d119 (change p 160 (some 138)) else d7 (change p 160 (some 138))) = d120 p
  rw [sub7243, sub7242]
  rfl
theorem sub7245 (p : Pattern) : d121 (change p 160 (some 138)) = d121 p := by
  change (if p 204 then d12 (change p 160 (some 138)) else d120 (change p 160 (some 138))) = d121 p
  rw [sub7095, sub7244]
  rfl
theorem sub7246 (p : Pattern) : d148 (change p 160 (some 138)) = d148 p := by
  change (if p 182 then d121 (change p 160 (some 138)) else d120 (change p 160 (some 138))) = d148 p
  rw [sub7245, sub7244]
  rfl
theorem sub7247 (p : Pattern) : d153 (change p 160 (some 138)) = d153 p := by
  change (if p 163 then d12 (change p 160 (some 138)) else d148 (change p 160 (some 138))) = d153 p
  rw [sub7095, sub7246]
  rfl
theorem sub7248 (p : Pattern) : d154 (change p 160 (some 138)) = d154 p := by
  change (if p 162 then d12 (change p 160 (some 138)) else d153 (change p 160 (some 138))) = d154 p
  rw [sub7095, sub7247]
  rfl
theorem sub7249 (p : Pattern) : d246 (change p 160 (some 138)) = d246 p := by
  change (if p 161 then d154 (change p 160 (some 138)) else d245 (change p 160 (some 138))) = d246 p
  rw [sub7248, sub7241]
  rfl
theorem sub7250 (p : Pattern) : d779 (change p 160 (some 138)) = d246 p := by
  change d246 (change p 160 (some 138)) = d246 p
  exact sub7249 p
theorem sub7251 (p : Pattern) : d780 (change p 160 (some 138)) = d4754 p := by
  change (if p 141 then d779 (change p 160 (some 138)) else d778 (change p 160 (some 138))) = d4754 p
  rw [sub7250, sub7240]
  rfl
theorem sub7252 (p : Pattern) : d781 (change p 160 (some 138)) = d4754 p := by
  change d780 (change p 160 (some 138)) = d4754 p
  exact sub7251 p
theorem sub7253 (p : Pattern) : d784 (change p 160 (some 138)) = d12 p := by
  change d12 (change p 160 (some 138)) = d12 p
  exact sub7095 p
theorem sub7254 (p : Pattern) : d785 (change p 160 (some 138)) = d4980 p := by
  change (if p 116 then d784 (change p 160 (some 138)) else d781 (change p 160 (some 138))) = d4980 p
  rw [sub7253, sub7252]
  rfl
theorem sub7255 (p : Pattern) : d786 (change p 160 (some 138)) = d4981 p := by
  change (if p 115 then d785 (change p 160 (some 138)) else d776 (change p 160 (some 138))) = d4981 p
  rw [sub7254, sub7236]
  rfl
theorem sub7256 (p : Pattern) : d787 (change p 160 (some 138)) = d4982 p := by
  change (if p 71 then d786 (change p 160 (some 138)) else d731 (change p 160 (some 138))) = d4982 p
  rw [sub7255, sub7156]
  rfl
theorem sub7257 (p : Pattern) : d788 (change p 160 (some 138)) = d4983 p := by
  change (if p 49 then d787 (change p 160 (some 138)) else d768 (change p 160 (some 138))) = d4983 p
  rw [sub7256, sub7227]
  rfl
theorem sub7258 (p : Pattern) : d789 (change p 160 (some 138)) = d4984 p := by
  change (if p 48 then d788 (change p 160 (some 138)) else d760 (change p 160 (some 138))) = d4984 p
  rw [sub7257, sub7205]
  rfl
theorem sub7259 (p : Pattern) : d0 (change p 204 none) = d0 p := by
  rfl
theorem sub7260 (p : Pattern) : d12 (change p 204 none) = d12 p := by
  rfl
theorem sub7261 (p : Pattern) : d13 (change p 204 none) = d13 p := by
  change (if p 247 then d12 (change p 204 none) else d0 (change p 204 none)) = d13 p
  rw [sub7260, sub7259]
  rfl
theorem sub7262 (p : Pattern) : d14 (change p 204 none) = d14 p := by
  change (if p 246 then d13 (change p 204 none) else d0 (change p 204 none)) = d14 p
  rw [sub7261, sub7259]
  rfl
theorem sub7263 (p : Pattern) : d1682 (change p 204 none) = d14 p := by
  change d14 (change p 204 none) = d14 p
  exact sub7262 p
theorem sub7264 (p : Pattern) : d2 (change p 204 none) = d2 p := by
  rfl
theorem sub7265 (p : Pattern) : d1683 (change p 204 none) = d1683 p := by
  change (if p 247 then d2 (change p 204 none) else d0 (change p 204 none)) = d1683 p
  rw [sub7264, sub7259]
  rfl
theorem sub7266 (p : Pattern) : d30 (change p 204 none) = d30 p := by
  change (if p 247 then d12 (change p 204 none) else d2 (change p 204 none)) = d30 p
  rw [sub7260, sub7264]
  rfl
theorem sub7267 (p : Pattern) : d1684 (change p 204 none) = d1684 p := by
  change (if p 246 then d30 (change p 204 none) else d1683 (change p 204 none)) = d1684 p
  rw [sub7266, sub7265]
  rfl
theorem sub7268 (p : Pattern) : d1685 (change p 204 none) = d1685 p := by
  change (if p 225 then d1684 (change p 204 none) else d14 (change p 204 none)) = d1685 p
  rw [sub7267, sub7262]
  rfl
theorem sub7269 (p : Pattern) : d1686 (change p 204 none) = d1686 p := by
  change (if p 224 then d1684 (change p 204 none) else d1685 (change p 204 none)) = d1686 p
  rw [sub7267, sub7268]
  rfl
theorem sub7270 (p : Pattern) : d1687 (change p 204 none) = d1686 p := by
  change d1686 (change p 204 none) = d1686 p
  exact sub7269 p
theorem sub7271 (p : Pattern) : d1688 (change p 204 none) = d4986 p := by
  change (if p 182 then d1687 (change p 204 none) else d1682 (change p 204 none)) = d4986 p
  rw [sub7270, sub7263]
  rfl
theorem sub7272 (p : Pattern) : d1689 (change p 204 none) = d14 p := by
  change d14 (change p 204 none) = d14 p
  exact sub7262 p
theorem sub7273 (p : Pattern) : d1690 (change p 204 none) = d4986 p := by
  change (if p 182 then d1687 (change p 204 none) else d1689 (change p 204 none)) = d4986 p
  rw [sub7270, sub7272]
  rfl
theorem sub7274 (p : Pattern) : d1691 (change p 204 none) = d4986 p := by
  change (if p 163 then d1690 (change p 204 none) else d1688 (change p 204 none)) = d4986 p
  rw [sub7273, sub7271]
  simp only [ite_self]
theorem sub7275 (p : Pattern) : d15 (change p 204 none) = d14 p := by
  change d14 (change p 204 none) = d14 p
  exact sub7262 p
theorem sub7276 (p : Pattern) : d1692 (change p 204 none) = d4986 p := by
  change (if p 182 then d1687 (change p 204 none) else d15 (change p 204 none)) = d4986 p
  rw [sub7270, sub7275]
  rfl
theorem sub7277 (p : Pattern) : d4 (change p 204 none) = d4 p := by
  rfl
theorem sub7278 (p : Pattern) : d17 (change p 204 none) = d17 p := by
  change (if p 247 then d12 (change p 204 none) else d4 (change p 204 none)) = d17 p
  rw [sub7260, sub7277]
  rfl
theorem sub7279 (p : Pattern) : d18 (change p 204 none) = d18 p := by
  change (if p 246 then d17 (change p 204 none) else d4 (change p 204 none)) = d18 p
  rw [sub7278, sub7277]
  rfl
theorem sub7280 (p : Pattern) : d19 (change p 204 none) = d18 p := by
  change d18 (change p 204 none) = d18 p
  exact sub7279 p
theorem sub7281 (p : Pattern) : d6 (change p 204 none) = d6 p := by
  rfl
theorem sub7282 (p : Pattern) : d1693 (change p 204 none) = d1693 p := by
  change (if p 247 then d6 (change p 204 none) else d4 (change p 204 none)) = d1693 p
  rw [sub7281, sub7277]
  rfl
theorem sub7283 (p : Pattern) : d34 (change p 204 none) = d34 p := by
  change (if p 247 then d12 (change p 204 none) else d6 (change p 204 none)) = d34 p
  rw [sub7260, sub7281]
  rfl
theorem sub7284 (p : Pattern) : d1694 (change p 204 none) = d1694 p := by
  change (if p 246 then d34 (change p 204 none) else d1693 (change p 204 none)) = d1694 p
  rw [sub7283, sub7282]
  rfl
theorem sub7285 (p : Pattern) : d1695 (change p 204 none) = d1695 p := by
  change (if p 225 then d1694 (change p 204 none) else d18 (change p 204 none)) = d1695 p
  rw [sub7284, sub7279]
  rfl
theorem sub7286 (p : Pattern) : d1696 (change p 204 none) = d1696 p := by
  change (if p 224 then d1694 (change p 204 none) else d1695 (change p 204 none)) = d1696 p
  rw [sub7284, sub7285]
  rfl
theorem sub7287 (p : Pattern) : d1697 (change p 204 none) = d1696 p := by
  change d1696 (change p 204 none) = d1696 p
  exact sub7286 p
theorem sub7288 (p : Pattern) : d1698 (change p 204 none) = d4987 p := by
  change (if p 182 then d1697 (change p 204 none) else d19 (change p 204 none)) = d4987 p
  rw [sub7287, sub7280]
  rfl
theorem sub7289 (p : Pattern) : d1699 (change p 204 none) = d4988 p := by
  change (if p 163 then d1698 (change p 204 none) else d1692 (change p 204 none)) = d4988 p
  rw [sub7288, sub7276]
  rfl
theorem sub7290 (p : Pattern) : d1700 (change p 204 none) = d4989 p := by
  change (if p 162 then d1699 (change p 204 none) else d1691 (change p 204 none)) = d4989 p
  rw [sub7289, sub7274]
  rfl
theorem sub7291 (p : Pattern) : d9 (change p 204 none) = d9 p := by
  rfl
theorem sub7292 (p : Pattern) : d23 (change p 204 none) = d23 p := by
  change (if p 247 then d12 (change p 204 none) else d9 (change p 204 none)) = d23 p
  rw [sub7260, sub7291]
  rfl
theorem sub7293 (p : Pattern) : d24 (change p 204 none) = d24 p := by
  change (if p 246 then d23 (change p 204 none) else d9 (change p 204 none)) = d24 p
  rw [sub7292, sub7291]
  rfl
theorem sub7294 (p : Pattern) : d25 (change p 204 none) = d24 p := by
  change d24 (change p 204 none) = d24 p
  exact sub7293 p
theorem sub7295 (p : Pattern) : d11 (change p 204 none) = d11 p := by
  rfl
theorem sub7296 (p : Pattern) : d1701 (change p 204 none) = d1701 p := by
  change (if p 247 then d11 (change p 204 none) else d9 (change p 204 none)) = d1701 p
  rw [sub7295, sub7291]
  rfl
theorem sub7297 (p : Pattern) : d39 (change p 204 none) = d39 p := by
  change (if p 247 then d12 (change p 204 none) else d11 (change p 204 none)) = d39 p
  rw [sub7260, sub7295]
  rfl
theorem sub7298 (p : Pattern) : d1702 (change p 204 none) = d1702 p := by
  change (if p 246 then d39 (change p 204 none) else d1701 (change p 204 none)) = d1702 p
  rw [sub7297, sub7296]
  rfl
theorem sub7299 (p : Pattern) : d1703 (change p 204 none) = d1703 p := by
  change (if p 225 then d1702 (change p 204 none) else d24 (change p 204 none)) = d1703 p
  rw [sub7298, sub7293]
  rfl
theorem sub7300 (p : Pattern) : d1704 (change p 204 none) = d1704 p := by
  change (if p 224 then d1702 (change p 204 none) else d1703 (change p 204 none)) = d1704 p
  rw [sub7298, sub7299]
  rfl
theorem sub7301 (p : Pattern) : d1705 (change p 204 none) = d1704 p := by
  change d1704 (change p 204 none) = d1704 p
  exact sub7300 p
theorem sub7302 (p : Pattern) : d1706 (change p 204 none) = d4990 p := by
  change (if p 182 then d1705 (change p 204 none) else d25 (change p 204 none)) = d4990 p
  rw [sub7301, sub7294]
  rfl
theorem sub7303 (p : Pattern) : d1707 (change p 204 none) = d4991 p := by
  change (if p 163 then d12 (change p 204 none) else d1706 (change p 204 none)) = d4991 p
  rw [sub7260, sub7302]
  rfl
theorem sub7304 (p : Pattern) : d1708 (change p 204 none) = d4992 p := by
  change (if p 162 then d1707 (change p 204 none) else d1699 (change p 204 none)) = d4992 p
  rw [sub7303, sub7289]
  rfl
theorem sub7305 (p : Pattern) : d1709 (change p 204 none) = d4993 p := by
  change (if p 161 then d1708 (change p 204 none) else d1700 (change p 204 none)) = d4993 p
  rw [sub7304, sub7290]
  rfl
theorem sub7306 (p : Pattern) : d31 (change p 204 none) = d31 p := by
  change (if p 246 then d30 (change p 204 none) else d2 (change p 204 none)) = d31 p
  rw [sub7266, sub7264]
  rfl
theorem sub7307 (p : Pattern) : d8 (change p 204 none) = d8 p := by
  rfl
theorem sub7308 (p : Pattern) : d1710 (change p 204 none) = d1710 p := by
  change (if p 247 then d8 (change p 204 none) else d2 (change p 204 none)) = d1710 p
  rw [sub7307, sub7264]
  rfl
theorem sub7309 (p : Pattern) : d190 (change p 204 none) = d190 p := by
  change (if p 247 then d12 (change p 204 none) else d8 (change p 204 none)) = d190 p
  rw [sub7260, sub7307]
  rfl
theorem sub7310 (p : Pattern) : d1711 (change p 204 none) = d1711 p := by
  change (if p 246 then d190 (change p 204 none) else d1710 (change p 204 none)) = d1711 p
  rw [sub7309, sub7308]
  rfl
theorem sub7311 (p : Pattern) : d1712 (change p 204 none) = d1712 p := by
  change (if p 225 then d1711 (change p 204 none) else d31 (change p 204 none)) = d1712 p
  rw [sub7310, sub7306]
  rfl
theorem sub7312 (p : Pattern) : d1713 (change p 204 none) = d1713 p := by
  change (if p 247 then d6 (change p 204 none) else d2 (change p 204 none)) = d1713 p
  rw [sub7281, sub7264]
  rfl
theorem sub7313 (p : Pattern) : d1714 (change p 204 none) = d1714 p := by
  change (if p 246 then d34 (change p 204 none) else d1713 (change p 204 none)) = d1714 p
  rw [sub7283, sub7312]
  rfl
theorem sub7314 (p : Pattern) : d1715 (change p 204 none) = d1715 p := by
  change (if p 246 then d39 (change p 204 none) else d30 (change p 204 none)) = d1715 p
  rw [sub7297, sub7266]
  rfl
theorem sub7315 (p : Pattern) : d1716 (change p 204 none) = d1716 p := by
  change (if p 225 then d1715 (change p 204 none) else d1714 (change p 204 none)) = d1716 p
  rw [sub7314, sub7313]
  rfl
theorem sub7316 (p : Pattern) : d1717 (change p 204 none) = d1717 p := by
  change (if p 224 then d1716 (change p 204 none) else d1712 (change p 204 none)) = d1717 p
  rw [sub7315, sub7311]
  rfl
theorem sub7317 (p : Pattern) : d1718 (change p 204 none) = d1717 p := by
  change d1717 (change p 204 none) = d1717 p
  exact sub7316 p
theorem sub7318 (p : Pattern) : d1719 (change p 204 none) = d4994 p := by
  change (if p 182 then d1718 (change p 204 none) else d15 (change p 204 none)) = d4994 p
  rw [sub7317, sub7275]
  rfl
theorem sub7319 (p : Pattern) : d35 (change p 204 none) = d35 p := by
  change (if p 246 then d34 (change p 204 none) else d6 (change p 204 none)) = d35 p
  rw [sub7283, sub7281]
  rfl
end NetHack.Sokoban22Refined85
