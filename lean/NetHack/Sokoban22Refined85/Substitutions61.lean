/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions60
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7320 (p : Pattern) : d364 (change p 204 none) = d364 p := by
  change (if p 246 then d12 (change p 204 none) else d34 (change p 204 none)) = d364 p
  rw [sub7260, sub7283]
  rfl
theorem sub7321 (p : Pattern) : d1720 (change p 204 none) = d1720 p := by
  change (if p 225 then d364 (change p 204 none) else d35 (change p 204 none)) = d1720 p
  rw [sub7320, sub7319]
  rfl
theorem sub7322 (p : Pattern) : d10 (change p 204 none) = d10 p := by
  rfl
theorem sub7323 (p : Pattern) : d1721 (change p 204 none) = d1721 p := by
  change (if p 247 then d10 (change p 204 none) else d6 (change p 204 none)) = d1721 p
  rw [sub7322, sub7281]
  rfl
theorem sub7324 (p : Pattern) : d57 (change p 204 none) = d57 p := by
  change (if p 247 then d12 (change p 204 none) else d10 (change p 204 none)) = d57 p
  rw [sub7260, sub7322]
  rfl
theorem sub7325 (p : Pattern) : d1722 (change p 204 none) = d1722 p := by
  change (if p 246 then d57 (change p 204 none) else d1721 (change p 204 none)) = d1722 p
  rw [sub7324, sub7323]
  rfl
theorem sub7326 (p : Pattern) : d1723 (change p 204 none) = d1723 p := by
  change (if p 225 then d364 (change p 204 none) else d1722 (change p 204 none)) = d1723 p
  rw [sub7320, sub7325]
  rfl
theorem sub7327 (p : Pattern) : d1724 (change p 204 none) = d1724 p := by
  change (if p 224 then d1723 (change p 204 none) else d1720 (change p 204 none)) = d1724 p
  rw [sub7326, sub7321]
  rfl
theorem sub7328 (p : Pattern) : d1725 (change p 204 none) = d1724 p := by
  change d1724 (change p 204 none) = d1724 p
  exact sub7327 p
theorem sub7329 (p : Pattern) : d1726 (change p 204 none) = d4995 p := by
  change (if p 182 then d1725 (change p 204 none) else d15 (change p 204 none)) = d4995 p
  rw [sub7328, sub7275]
  rfl
theorem sub7330 (p : Pattern) : d1727 (change p 204 none) = d4996 p := by
  change (if p 163 then d1726 (change p 204 none) else d1719 (change p 204 none)) = d4996 p
  rw [sub7329, sub7318]
  rfl
theorem sub7331 (p : Pattern) : d40 (change p 204 none) = d40 p := by
  change (if p 246 then d39 (change p 204 none) else d11 (change p 204 none)) = d40 p
  rw [sub7297, sub7295]
  rfl
theorem sub7332 (p : Pattern) : d327 (change p 204 none) = d327 p := by
  change (if p 246 then d12 (change p 204 none) else d39 (change p 204 none)) = d327 p
  rw [sub7260, sub7297]
  rfl
theorem sub7333 (p : Pattern) : d1728 (change p 204 none) = d1728 p := by
  change (if p 225 then d327 (change p 204 none) else d40 (change p 204 none)) = d1728 p
  rw [sub7332, sub7331]
  rfl
theorem sub7334 (p : Pattern) : d1729 (change p 204 none) = d1729 p := by
  change (if p 224 then d327 (change p 204 none) else d1728 (change p 204 none)) = d1729 p
  rw [sub7332, sub7333]
  rfl
theorem sub7335 (p : Pattern) : d1730 (change p 204 none) = d1729 p := by
  change d1729 (change p 204 none) = d1729 p
  exact sub7334 p
theorem sub7336 (p : Pattern) : d1731 (change p 204 none) = d4997 p := by
  change (if p 182 then d1730 (change p 204 none) else d15 (change p 204 none)) = d4997 p
  rw [sub7335, sub7275]
  rfl
theorem sub7337 (p : Pattern) : d1732 (change p 204 none) = d43 p := by
  change (if p 182 then d12 (change p 204 none) else d19 (change p 204 none)) = d43 p
  rw [sub7260, sub7280]
  rfl
theorem sub7338 (p : Pattern) : d1733 (change p 204 none) = d4998 p := by
  change (if p 163 then d1732 (change p 204 none) else d1731 (change p 204 none)) = d4998 p
  rw [sub7337, sub7336]
  rfl
theorem sub7339 (p : Pattern) : d1734 (change p 204 none) = d4999 p := by
  change (if p 162 then d1733 (change p 204 none) else d1727 (change p 204 none)) = d4999 p
  rw [sub7338, sub7330]
  rfl
theorem sub7340 (p : Pattern) : d1735 (change p 204 none) = d46 p := by
  change (if p 182 then d12 (change p 204 none) else d15 (change p 204 none)) = d46 p
  rw [sub7260, sub7275]
  rfl
theorem sub7341 (p : Pattern) : d1736 (change p 204 none) = d47 p := by
  change (if p 163 then d1732 (change p 204 none) else d1735 (change p 204 none)) = d47 p
  rw [sub7337, sub7340]
  rfl
theorem sub7342 (p : Pattern) : d527 (change p 204 none) = d48 p := by
  change (if p 182 then d12 (change p 204 none) else d25 (change p 204 none)) = d48 p
  rw [sub7260, sub7294]
  rfl
theorem sub7343 (p : Pattern) : d528 (change p 204 none) = d49 p := by
  change (if p 163 then d12 (change p 204 none) else d527 (change p 204 none)) = d49 p
  rw [sub7260, sub7342]
  rfl
theorem sub7344 (p : Pattern) : d1737 (change p 204 none) = d50 p := by
  change (if p 162 then d528 (change p 204 none) else d1736 (change p 204 none)) = d50 p
  rw [sub7343, sub7341]
  rfl
theorem sub7345 (p : Pattern) : d1738 (change p 204 none) = d5000 p := by
  change (if p 161 then d1737 (change p 204 none) else d1734 (change p 204 none)) = d5000 p
  rw [sub7344, sub7339]
  rfl
theorem sub7346 (p : Pattern) : d1739 (change p 204 none) = d5001 p := by
  change (if p 160 then d1738 (change p 204 none) else d1709 (change p 204 none)) = d5001 p
  rw [sub7345, sub7305]
  rfl
theorem sub7347 (p : Pattern) : d1740 (change p 204 none) = d14 p := by
  change d14 (change p 204 none) = d14 p
  exact sub7262 p
theorem sub7348 (p : Pattern) : d1741 (change p 204 none) = d4986 p := by
  change (if p 182 then d1687 (change p 204 none) else d1740 (change p 204 none)) = d4986 p
  rw [sub7270, sub7347]
  rfl
theorem sub7349 (p : Pattern) : d32 (change p 204 none) = d31 p := by
  change d31 (change p 204 none) = d31 p
  exact sub7306 p
theorem sub7350 (p : Pattern) : d1742 (change p 204 none) = d1742 p := by
  change (if p 247 then d4 (change p 204 none) else d2 (change p 204 none)) = d1742 p
  rw [sub7277, sub7264]
  rfl
theorem sub7351 (p : Pattern) : d1743 (change p 204 none) = d1743 p := by
  change (if p 246 then d17 (change p 204 none) else d1742 (change p 204 none)) = d1743 p
  rw [sub7278, sub7350]
  rfl
theorem sub7352 (p : Pattern) : d1744 (change p 204 none) = d1744 p := by
  change (if p 225 then d1743 (change p 204 none) else d31 (change p 204 none)) = d1744 p
  rw [sub7351, sub7306]
  rfl
theorem sub7353 (p : Pattern) : d1745 (change p 204 none) = d1745 p := by
  change (if p 224 then d1743 (change p 204 none) else d1744 (change p 204 none)) = d1745 p
  rw [sub7351, sub7352]
  rfl
theorem sub7354 (p : Pattern) : d1746 (change p 204 none) = d1745 p := by
  change d1745 (change p 204 none) = d1745 p
  exact sub7353 p
theorem sub7355 (p : Pattern) : d1747 (change p 204 none) = d5002 p := by
  change (if p 182 then d1746 (change p 204 none) else d32 (change p 204 none)) = d5002 p
  rw [sub7354, sub7349]
  rfl
theorem sub7356 (p : Pattern) : d1748 (change p 204 none) = d5003 p := by
  change (if p 163 then d1747 (change p 204 none) else d1741 (change p 204 none)) = d5003 p
  rw [sub7355, sub7348]
  rfl
theorem sub7357 (p : Pattern) : d1749 (change p 204 none) = d5004 p := by
  change (if p 163 then d1706 (change p 204 none) else d1698 (change p 204 none)) = d5004 p
  rw [sub7302, sub7288]
  rfl
theorem sub7358 (p : Pattern) : d1750 (change p 204 none) = d5005 p := by
  change (if p 162 then d1749 (change p 204 none) else d1748 (change p 204 none)) = d5005 p
  rw [sub7357, sub7356]
  rfl
theorem sub7359 (p : Pattern) : d58 (change p 204 none) = d58 p := by
  change (if p 246 then d57 (change p 204 none) else d10 (change p 204 none)) = d58 p
  rw [sub7324, sub7322]
  rfl
theorem sub7360 (p : Pattern) : d59 (change p 204 none) = d58 p := by
  change d58 (change p 204 none) = d58 p
  exact sub7359 p
theorem sub7361 (p : Pattern) : d329 (change p 204 none) = d329 p := by
  change (if p 246 then d12 (change p 204 none) else d57 (change p 204 none)) = d329 p
  rw [sub7260, sub7324]
  rfl
theorem sub7362 (p : Pattern) : d1751 (change p 204 none) = d1751 p := by
  change (if p 225 then d329 (change p 204 none) else d58 (change p 204 none)) = d1751 p
  rw [sub7361, sub7359]
  rfl
theorem sub7363 (p : Pattern) : d1752 (change p 204 none) = d1752 p := by
  change (if p 224 then d329 (change p 204 none) else d1751 (change p 204 none)) = d1752 p
  rw [sub7361, sub7362]
  rfl
theorem sub7364 (p : Pattern) : d1753 (change p 204 none) = d1752 p := by
  change d1752 (change p 204 none) = d1752 p
  exact sub7363 p
theorem sub7365 (p : Pattern) : d1754 (change p 204 none) = d5006 p := by
  change (if p 182 then d1753 (change p 204 none) else d59 (change p 204 none)) = d5006 p
  rw [sub7364, sub7360]
  rfl
theorem sub7366 (p : Pattern) : d1755 (change p 204 none) = d5007 p := by
  change (if p 163 then d1754 (change p 204 none) else d1698 (change p 204 none)) = d5007 p
  rw [sub7365, sub7288]
  rfl
theorem sub7367 (p : Pattern) : d41 (change p 204 none) = d40 p := by
  change d40 (change p 204 none) = d40 p
  exact sub7331 p
theorem sub7368 (p : Pattern) : d1756 (change p 204 none) = d5008 p := by
  change (if p 182 then d1730 (change p 204 none) else d41 (change p 204 none)) = d5008 p
  rw [sub7335, sub7367]
  rfl
theorem sub7369 (p : Pattern) : d1757 (change p 204 none) = d5009 p := by
  change (if p 163 then d12 (change p 204 none) else d1756 (change p 204 none)) = d5009 p
  rw [sub7260, sub7368]
  rfl
theorem sub7370 (p : Pattern) : d1758 (change p 204 none) = d5010 p := by
  change (if p 162 then d1757 (change p 204 none) else d1755 (change p 204 none)) = d5010 p
  rw [sub7369, sub7366]
  rfl
theorem sub7371 (p : Pattern) : d1759 (change p 204 none) = d5011 p := by
  change (if p 161 then d1758 (change p 204 none) else d1750 (change p 204 none)) = d5011 p
  rw [sub7370, sub7358]
  rfl
theorem sub7372 (p : Pattern) : d1760 (change p 204 none) = d66 p := by
  change (if p 182 then d12 (change p 204 none) else d32 (change p 204 none)) = d66 p
  rw [sub7260, sub7349]
  rfl
theorem sub7373 (p : Pattern) : d1761 (change p 204 none) = d5012 p := by
  change (if p 163 then d1760 (change p 204 none) else d1726 (change p 204 none)) = d5012 p
  rw [sub7372, sub7329]
  rfl
theorem sub7374 (p : Pattern) : d1762 (change p 204 none) = d68 p := by
  change (if p 163 then d527 (change p 204 none) else d1732 (change p 204 none)) = d68 p
  rw [sub7342, sub7337]
  rfl
theorem sub7375 (p : Pattern) : d1763 (change p 204 none) = d5013 p := by
  change (if p 162 then d1762 (change p 204 none) else d1761 (change p 204 none)) = d5013 p
  rw [sub7374, sub7373]
  rfl
theorem sub7376 (p : Pattern) : d277 (change p 204 none) = d70 p := by
  change (if p 182 then d12 (change p 204 none) else d59 (change p 204 none)) = d70 p
  rw [sub7260, sub7360]
  rfl
theorem sub7377 (p : Pattern) : d1764 (change p 204 none) = d71 p := by
  change (if p 163 then d277 (change p 204 none) else d1732 (change p 204 none)) = d71 p
  rw [sub7376, sub7337]
  rfl
theorem sub7378 (p : Pattern) : d538 (change p 204 none) = d72 p := by
  change (if p 182 then d12 (change p 204 none) else d41 (change p 204 none)) = d72 p
  rw [sub7260, sub7367]
  rfl
theorem sub7379 (p : Pattern) : d539 (change p 204 none) = d73 p := by
  change (if p 163 then d12 (change p 204 none) else d538 (change p 204 none)) = d73 p
  rw [sub7260, sub7378]
  rfl
theorem sub7380 (p : Pattern) : d1765 (change p 204 none) = d74 p := by
  change (if p 162 then d539 (change p 204 none) else d1764 (change p 204 none)) = d74 p
  rw [sub7379, sub7377]
  rfl
theorem sub7381 (p : Pattern) : d1766 (change p 204 none) = d5014 p := by
  change (if p 161 then d1765 (change p 204 none) else d1763 (change p 204 none)) = d5014 p
  rw [sub7380, sub7375]
  rfl
theorem sub7382 (p : Pattern) : d1767 (change p 204 none) = d5015 p := by
  change (if p 160 then d1766 (change p 204 none) else d1759 (change p 204 none)) = d5015 p
  rw [sub7381, sub7371]
  rfl
theorem sub7383 (p : Pattern) : d1768 (change p 204 none) = d5016 p := by
  change (if p 141 then d1767 (change p 204 none) else d1739 (change p 204 none)) = d5016 p
  rw [sub7382, sub7346]
  rfl
theorem sub7384 (p : Pattern) : d1769 (change p 204 none) = d1769 p := by
  change (if p 247 then d4 (change p 204 none) else d0 (change p 204 none)) = d1769 p
  rw [sub7277, sub7259]
  rfl
theorem sub7385 (p : Pattern) : d1770 (change p 204 none) = d1770 p := by
  change (if p 246 then d17 (change p 204 none) else d1769 (change p 204 none)) = d1770 p
  rw [sub7278, sub7384]
  rfl
theorem sub7386 (p : Pattern) : d1771 (change p 204 none) = d1771 p := by
  change (if p 225 then d1770 (change p 204 none) else d14 (change p 204 none)) = d1771 p
  rw [sub7385, sub7262]
  rfl
theorem sub7387 (p : Pattern) : d1772 (change p 204 none) = d1772 p := by
  change (if p 224 then d1770 (change p 204 none) else d1771 (change p 204 none)) = d1772 p
  rw [sub7385, sub7386]
  rfl
theorem sub7388 (p : Pattern) : d1773 (change p 204 none) = d1772 p := by
  change d1772 (change p 204 none) = d1772 p
  exact sub7387 p
theorem sub7389 (p : Pattern) : d1774 (change p 204 none) = d5017 p := by
  change (if p 182 then d1773 (change p 204 none) else d15 (change p 204 none)) = d5017 p
  rw [sub7388, sub7275]
  rfl
theorem sub7390 (p : Pattern) : d1775 (change p 204 none) = d1775 p := by
  change (if p 247 then d6 (change p 204 none) else d0 (change p 204 none)) = d1775 p
  rw [sub7281, sub7259]
  rfl
theorem sub7391 (p : Pattern) : d1776 (change p 204 none) = d1776 p := by
  change (if p 246 then d34 (change p 204 none) else d1775 (change p 204 none)) = d1776 p
  rw [sub7283, sub7390]
  rfl
theorem sub7392 (p : Pattern) : d1777 (change p 204 none) = d1777 p := by
  change (if p 225 then d1776 (change p 204 none) else d14 (change p 204 none)) = d1777 p
  rw [sub7391, sub7262]
  rfl
theorem sub7393 (p : Pattern) : d1778 (change p 204 none) = d1778 p := by
  change (if p 247 then d8 (change p 204 none) else d0 (change p 204 none)) = d1778 p
  rw [sub7307, sub7259]
  rfl
theorem sub7394 (p : Pattern) : d1779 (change p 204 none) = d1779 p := by
  change (if p 246 then d190 (change p 204 none) else d1778 (change p 204 none)) = d1779 p
  rw [sub7309, sub7393]
  rfl
theorem sub7395 (p : Pattern) : d1780 (change p 204 none) = d1780 p := by
  change (if p 225 then d1779 (change p 204 none) else d1770 (change p 204 none)) = d1780 p
  rw [sub7394, sub7385]
  rfl
theorem sub7396 (p : Pattern) : d1781 (change p 204 none) = d1781 p := by
  change (if p 224 then d1780 (change p 204 none) else d1777 (change p 204 none)) = d1781 p
  rw [sub7395, sub7392]
  rfl
theorem sub7397 (p : Pattern) : d1782 (change p 204 none) = d1781 p := by
  change d1781 (change p 204 none) = d1781 p
  exact sub7396 p
theorem sub7398 (p : Pattern) : d1783 (change p 204 none) = d5018 p := by
  change (if p 182 then d1782 (change p 204 none) else d15 (change p 204 none)) = d5018 p
  rw [sub7397, sub7275]
  rfl
theorem sub7399 (p : Pattern) : d1784 (change p 204 none) = d5019 p := by
  change (if p 163 then d1783 (change p 204 none) else d1774 (change p 204 none)) = d5019 p
  rw [sub7398, sub7389]
  rfl
theorem sub7400 (p : Pattern) : d1785 (change p 204 none) = d1785 p := by
  change (if p 247 then d11 (change p 204 none) else d0 (change p 204 none)) = d1785 p
  rw [sub7295, sub7259]
  rfl
theorem sub7401 (p : Pattern) : d1786 (change p 204 none) = d1786 p := by
  change (if p 246 then d23 (change p 204 none) else d1785 (change p 204 none)) = d1786 p
  rw [sub7292, sub7400]
  rfl
theorem sub7402 (p : Pattern) : d1787 (change p 204 none) = d1787 p := by
  change (if p 225 then d1786 (change p 204 none) else d1770 (change p 204 none)) = d1787 p
  rw [sub7401, sub7385]
  rfl
theorem sub7403 (p : Pattern) : d1788 (change p 204 none) = d1788 p := by
  change (if p 224 then d1787 (change p 204 none) else d1777 (change p 204 none)) = d1788 p
  rw [sub7402, sub7392]
  rfl
theorem sub7404 (p : Pattern) : d1789 (change p 204 none) = d1788 p := by
  change d1788 (change p 204 none) = d1788 p
  exact sub7403 p
theorem sub7405 (p : Pattern) : d1790 (change p 204 none) = d5020 p := by
  change (if p 182 then d1789 (change p 204 none) else d15 (change p 204 none)) = d5020 p
  rw [sub7404, sub7275]
  rfl
theorem sub7406 (p : Pattern) : d1791 (change p 204 none) = d1791 p := by
  change (if p 247 then d10 (change p 204 none) else d4 (change p 204 none)) = d1791 p
  rw [sub7322, sub7277]
  rfl
theorem sub7407 (p : Pattern) : d1792 (change p 204 none) = d1792 p := by
  change (if p 246 then d57 (change p 204 none) else d1791 (change p 204 none)) = d1792 p
  rw [sub7324, sub7406]
  rfl
theorem sub7408 (p : Pattern) : d1793 (change p 204 none) = d1793 p := by
  change (if p 225 then d1792 (change p 204 none) else d18 (change p 204 none)) = d1793 p
  rw [sub7407, sub7279]
  rfl
theorem sub7409 (p : Pattern) : d1794 (change p 204 none) = d1794 p := by
  change (if p 247 then d8 (change p 204 none) else d4 (change p 204 none)) = d1794 p
  rw [sub7307, sub7277]
  rfl
theorem sub7410 (p : Pattern) : d1795 (change p 204 none) = d1795 p := by
  change (if p 246 then d190 (change p 204 none) else d1794 (change p 204 none)) = d1795 p
  rw [sub7309, sub7409]
  rfl
theorem sub7411 (p : Pattern) : d339 (change p 204 none) = d339 p := by
  change (if p 246 then d12 (change p 204 none) else d17 (change p 204 none)) = d339 p
  rw [sub7260, sub7278]
  rfl
theorem sub7412 (p : Pattern) : d1796 (change p 204 none) = d1796 p := by
  change (if p 225 then d339 (change p 204 none) else d1795 (change p 204 none)) = d1796 p
  rw [sub7411, sub7410]
  rfl
theorem sub7413 (p : Pattern) : d1797 (change p 204 none) = d1797 p := by
  change (if p 224 then d1796 (change p 204 none) else d1793 (change p 204 none)) = d1797 p
  rw [sub7412, sub7408]
  rfl
theorem sub7414 (p : Pattern) : d1798 (change p 204 none) = d1797 p := by
  change d1797 (change p 204 none) = d1797 p
  exact sub7413 p
theorem sub7415 (p : Pattern) : d1799 (change p 204 none) = d5021 p := by
  change (if p 182 then d1798 (change p 204 none) else d19 (change p 204 none)) = d5021 p
  rw [sub7414, sub7280]
  rfl
theorem sub7416 (p : Pattern) : d1800 (change p 204 none) = d5022 p := by
  change (if p 163 then d1799 (change p 204 none) else d1790 (change p 204 none)) = d5022 p
  rw [sub7415, sub7405]
  rfl
theorem sub7417 (p : Pattern) : d1801 (change p 204 none) = d5023 p := by
  change (if p 162 then d1800 (change p 204 none) else d1784 (change p 204 none)) = d5023 p
  rw [sub7416, sub7399]
  rfl
theorem sub7418 (p : Pattern) : d356 (change p 204 none) = d356 p := by
  change (if p 246 then d12 (change p 204 none) else d23 (change p 204 none)) = d356 p
  rw [sub7260, sub7292]
  rfl
theorem sub7419 (p : Pattern) : d1802 (change p 204 none) = d1802 p := by
  change (if p 225 then d356 (change p 204 none) else d24 (change p 204 none)) = d1802 p
  rw [sub7418, sub7293]
  rfl
theorem sub7420 (p : Pattern) : d1803 (change p 204 none) = d1803 p := by
  change (if p 224 then d356 (change p 204 none) else d1802 (change p 204 none)) = d1803 p
  rw [sub7418, sub7419]
  rfl
theorem sub7421 (p : Pattern) : d1804 (change p 204 none) = d1803 p := by
  change d1803 (change p 204 none) = d1803 p
  exact sub7420 p
theorem sub7422 (p : Pattern) : d1805 (change p 204 none) = d5024 p := by
  change (if p 182 then d1804 (change p 204 none) else d25 (change p 204 none)) = d5024 p
  rw [sub7421, sub7294]
  rfl
theorem sub7423 (p : Pattern) : d1806 (change p 204 none) = d5025 p := by
  change (if p 163 then d12 (change p 204 none) else d1805 (change p 204 none)) = d5025 p
  rw [sub7260, sub7422]
  rfl
theorem sub7424 (p : Pattern) : d1807 (change p 204 none) = d5026 p := by
  change (if p 162 then d1806 (change p 204 none) else d1800 (change p 204 none)) = d5026 p
  rw [sub7423, sub7416]
  rfl
theorem sub7425 (p : Pattern) : d1808 (change p 204 none) = d5027 p := by
  change (if p 161 then d1807 (change p 204 none) else d1801 (change p 204 none)) = d5027 p
  rw [sub7424, sub7417]
  rfl
theorem sub7426 (p : Pattern) : d1809 (change p 204 none) = d5028 p := by
  change (if p 182 then d1718 (change p 204 none) else d32 (change p 204 none)) = d5028 p
  rw [sub7317, sub7349]
  rfl
theorem sub7427 (p : Pattern) : d36 (change p 204 none) = d35 p := by
  change d35 (change p 204 none) = d35 p
  exact sub7319 p
theorem sub7428 (p : Pattern) : d1810 (change p 204 none) = d5029 p := by
  change (if p 182 then d1725 (change p 204 none) else d36 (change p 204 none)) = d5029 p
  rw [sub7328, sub7427]
  rfl
theorem sub7429 (p : Pattern) : d1811 (change p 204 none) = d5030 p := by
  change (if p 163 then d1810 (change p 204 none) else d1809 (change p 204 none)) = d5030 p
  rw [sub7428, sub7426]
  rfl
theorem sub7430 (p : Pattern) : d1812 (change p 204 none) = d5031 p := by
  change (if p 162 then d1757 (change p 204 none) else d1811 (change p 204 none)) = d5031 p
  rw [sub7369, sub7429]
  rfl
theorem sub7431 (p : Pattern) : d1813 (change p 204 none) = d5032 p := by
  change (if p 161 then d12 (change p 204 none) else d1812 (change p 204 none)) = d5032 p
  rw [sub7260, sub7430]
  rfl
theorem sub7432 (p : Pattern) : d1814 (change p 204 none) = d5033 p := by
  change (if p 160 then d1813 (change p 204 none) else d1808 (change p 204 none)) = d5033 p
  rw [sub7431, sub7425]
  rfl
theorem sub7433 (p : Pattern) : d1815 (change p 204 none) = d5034 p := by
  change (if p 163 then d1809 (change p 204 none) else d1783 (change p 204 none)) = d5034 p
  rw [sub7426, sub7398]
  rfl
theorem sub7434 (p : Pattern) : d1816 (change p 204 none) = d5035 p := by
  change (if p 163 then d1805 (change p 204 none) else d1799 (change p 204 none)) = d5035 p
  rw [sub7422, sub7415]
  rfl
theorem sub7435 (p : Pattern) : d1817 (change p 204 none) = d5036 p := by
  change (if p 162 then d1816 (change p 204 none) else d1815 (change p 204 none)) = d5036 p
  rw [sub7434, sub7433]
  rfl
theorem sub7436 (p : Pattern) : d1818 (change p 204 none) = d5037 p := by
  change (if p 163 then d1754 (change p 204 none) else d1799 (change p 204 none)) = d5037 p
  rw [sub7365, sub7415]
  rfl
theorem sub7437 (p : Pattern) : d1819 (change p 204 none) = d5038 p := by
  change (if p 162 then d1757 (change p 204 none) else d1818 (change p 204 none)) = d5038 p
  rw [sub7369, sub7436]
  rfl
theorem sub7438 (p : Pattern) : d1820 (change p 204 none) = d5039 p := by
  change (if p 161 then d1819 (change p 204 none) else d1817 (change p 204 none)) = d5039 p
  rw [sub7437, sub7435]
  rfl
theorem sub7439 (p : Pattern) : d1821 (change p 204 none) = d5040 p := by
  change (if p 163 then d12 (change p 204 none) else d1810 (change p 204 none)) = d5040 p
  rw [sub7260, sub7428]
  rfl
end NetHack.Sokoban22Refined85
