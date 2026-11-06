/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub12600 (p : Pattern) : d3524 (change p 246 none) = d6542 p := by
  change (if p 163 then d3246 (change p 246 none) else d3394 (change p 246 none)) = d6542 p
  rw [sub12313, sub12469]
  rfl
theorem sub12601 (p : Pattern) : d3525 (change p 246 none) = d6543 p := by
  change (if p 162 then d3524 (change p 246 none) else d3364 (change p 246 none)) = d6543 p
  rw [sub12600, sub12436]
  rfl
theorem sub12602 (p : Pattern) : d3526 (change p 246 none) = d6544 p := by
  change (if p 163 then d3246 (change p 246 none) else d3368 (change p 246 none)) = d6544 p
  rw [sub12313, sub12441]
  rfl
theorem sub12603 (p : Pattern) : d3527 (change p 246 none) = d6545 p := by
  change (if p 162 then d12 (change p 246 none) else d3526 (change p 246 none)) = d6545 p
  rw [sub12294, sub12602]
  rfl
theorem sub12604 (p : Pattern) : d3528 (change p 246 none) = d6546 p := by
  change (if p 161 then d3527 (change p 246 none) else d3525 (change p 246 none)) = d6546 p
  rw [sub12603, sub12601]
  rfl
theorem sub12605 (p : Pattern) : d3529 (change p 246 none) = d6547 p := by
  change (if p 163 then d3283 (change p 246 none) else d3412 (change p 246 none)) = d6547 p
  rw [sub12354, sub12487]
  rfl
theorem sub12606 (p : Pattern) : d3530 (change p 246 none) = d6548 p := by
  change (if p 162 then d12 (change p 246 none) else d3529 (change p 246 none)) = d6548 p
  rw [sub12294, sub12605]
  rfl
theorem sub12607 (p : Pattern) : d3531 (change p 246 none) = d6549 p := by
  change (if p 161 then d12 (change p 246 none) else d3530 (change p 246 none)) = d6549 p
  rw [sub12294, sub12606]
  rfl
theorem sub12608 (p : Pattern) : d3532 (change p 246 none) = d6550 p := by
  change (if p 160 then d3531 (change p 246 none) else d3528 (change p 246 none)) = d6550 p
  rw [sub12607, sub12604]
  rfl
theorem sub12609 (p : Pattern) : d3533 (change p 246 none) = d6551 p := by
  change (if p 141 then d3521 (change p 246 none) else d3532 (change p 246 none)) = d6551 p
  rw [sub12597, sub12608]
  rfl
theorem sub12610 (p : Pattern) : d3534 (change p 246 none) = d6552 p := by
  change (if p 138 then d12 (change p 246 none) else d3533 (change p 246 none)) = d6552 p
  rw [sub12294, sub12609]
  rfl
theorem sub12611 (p : Pattern) : d3535 (change p 246 none) = d6553 p := by
  change (if p 116 then d3534 (change p 246 none) else d3523 (change p 246 none)) = d6553 p
  rw [sub12610, sub12599]
  rfl
theorem sub12612 (p : Pattern) : d3536 (change p 246 none) = d6554 p := by
  change (if p 115 then d3535 (change p 246 none) else d3497 (change p 246 none)) = d6554 p
  rw [sub12611, sub12573]
  rfl
theorem sub12613 (p : Pattern) : d3537 (change p 246 none) = d6555 p := by
  change (if p 71 then d3536 (change p 246 none) else d3334 (change p 246 none)) = d6555 p
  rw [sub12612, sub12405]
  rfl
theorem sub12614 (p : Pattern) : d3538 (change p 246 none) = d6556 p := by
  change (if p 49 then d3537 (change p 246 none) else d3480 (change p 246 none)) = d6556 p
  rw [sub12613, sub12556]
  rfl
theorem sub12615 (p : Pattern) : d3539 (change p 246 none) = d6557 p := by
  change (if p 48 then d3538 (change p 246 none) else d3440 (change p 246 none)) = d6557 p
  rw [sub12614, sub12515]
  rfl
theorem sub12616 (p : Pattern) : d0 (change p 10000 (some 204)) = d0 p := by
  rfl
theorem sub12617 (p : Pattern) : d12 (change p 10000 (some 204)) = d12 p := by
  rfl
theorem sub12618 (p : Pattern) : d13 (change p 10000 (some 204)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d13 p
  rw [sub12617, sub12616]
  rfl
theorem sub12619 (p : Pattern) : d14 (change p 10000 (some 204)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d14 p
  rw [sub12618, sub12616]
  rfl
theorem sub12620 (p : Pattern) : d4 (change p 10000 (some 204)) = d4 p := by
  rfl
theorem sub12621 (p : Pattern) : d1769 (change p 10000 (some 204)) = d1769 p := by
  change (if p 247 then d4 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d1769 p
  rw [sub12620, sub12616]
  rfl
theorem sub12622 (p : Pattern) : d17 (change p 10000 (some 204)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d4 (change p 10000 (some 204))) = d17 p
  rw [sub12617, sub12620]
  rfl
theorem sub12623 (p : Pattern) : d1770 (change p 10000 (some 204)) = d1770 p := by
  change (if p 246 then d17 (change p 10000 (some 204)) else d1769 (change p 10000 (some 204))) = d1770 p
  rw [sub12622, sub12621]
  rfl
theorem sub12624 (p : Pattern) : d1771 (change p 10000 (some 204)) = d1771 p := by
  change (if p 225 then d1770 (change p 10000 (some 204)) else d14 (change p 10000 (some 204))) = d1771 p
  rw [sub12623, sub12619]
  rfl
theorem sub12625 (p : Pattern) : d1772 (change p 10000 (some 204)) = d1772 p := by
  change (if p 224 then d1770 (change p 10000 (some 204)) else d1771 (change p 10000 (some 204))) = d1772 p
  rw [sub12623, sub12624]
  rfl
theorem sub12626 (p : Pattern) : d2895 (change p 10000 (some 204)) = d1772 p := by
  change d1772 (change p 10000 (some 204)) = d1772 p
  exact sub12625 p
theorem sub12627 (p : Pattern) : d1687 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12628 (p : Pattern) : d2896 (change p 10000 (some 204)) = d7014 p := by
  change (if p 182 then d1687 (change p 10000 (some 204)) else d2895 (change p 10000 (some 204))) = d7014 p
  rw [sub12627, sub12626]
  rfl
theorem sub12629 (p : Pattern) : d18 (change p 10000 (some 204)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 204)) else d4 (change p 10000 (some 204))) = d18 p
  rw [sub12622, sub12620]
  rfl
theorem sub12630 (p : Pattern) : d8 (change p 10000 (some 204)) = d8 p := by
  rfl
theorem sub12631 (p : Pattern) : d1794 (change p 10000 (some 204)) = d1794 p := by
  change (if p 247 then d8 (change p 10000 (some 204)) else d4 (change p 10000 (some 204))) = d1794 p
  rw [sub12630, sub12620]
  rfl
theorem sub12632 (p : Pattern) : d190 (change p 10000 (some 204)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d8 (change p 10000 (some 204))) = d190 p
  rw [sub12617, sub12630]
  rfl
theorem sub12633 (p : Pattern) : d1795 (change p 10000 (some 204)) = d1795 p := by
  change (if p 246 then d190 (change p 10000 (some 204)) else d1794 (change p 10000 (some 204))) = d1795 p
  rw [sub12632, sub12631]
  rfl
theorem sub12634 (p : Pattern) : d2011 (change p 10000 (some 204)) = d2011 p := by
  change (if p 225 then d1795 (change p 10000 (some 204)) else d18 (change p 10000 (some 204))) = d2011 p
  rw [sub12633, sub12629]
  rfl
theorem sub12635 (p : Pattern) : d2012 (change p 10000 (some 204)) = d2012 p := by
  change (if p 224 then d1795 (change p 10000 (some 204)) else d2011 (change p 10000 (some 204))) = d2012 p
  rw [sub12633, sub12634]
  rfl
theorem sub12636 (p : Pattern) : d2897 (change p 10000 (some 204)) = d2012 p := by
  change d2012 (change p 10000 (some 204)) = d2012 p
  exact sub12635 p
theorem sub12637 (p : Pattern) : d1697 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12638 (p : Pattern) : d2898 (change p 10000 (some 204)) = d7015 p := by
  change (if p 182 then d1697 (change p 10000 (some 204)) else d2897 (change p 10000 (some 204))) = d7015 p
  rw [sub12637, sub12636]
  rfl
theorem sub12639 (p : Pattern) : d2899 (change p 10000 (some 204)) = d7016 p := by
  change (if p 163 then d2898 (change p 10000 (some 204)) else d2896 (change p 10000 (some 204))) = d7016 p
  rw [sub12638, sub12628]
  rfl
theorem sub12640 (p : Pattern) : d2900 (change p 10000 (some 204)) = d7017 p := by
  change (if p 162 then d2899 (change p 10000 (some 204)) else d2896 (change p 10000 (some 204))) = d7017 p
  rw [sub12639, sub12628]
  rfl
theorem sub12641 (p : Pattern) : d9 (change p 10000 (some 204)) = d9 p := by
  rfl
theorem sub12642 (p : Pattern) : d23 (change p 10000 (some 204)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d9 (change p 10000 (some 204))) = d23 p
  rw [sub12617, sub12641]
  rfl
theorem sub12643 (p : Pattern) : d24 (change p 10000 (some 204)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 204)) else d9 (change p 10000 (some 204))) = d24 p
  rw [sub12642, sub12641]
  rfl
theorem sub12644 (p : Pattern) : d356 (change p 10000 (some 204)) = d356 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d23 (change p 10000 (some 204))) = d356 p
  rw [sub12617, sub12642]
  rfl
theorem sub12645 (p : Pattern) : d1802 (change p 10000 (some 204)) = d1802 p := by
  change (if p 225 then d356 (change p 10000 (some 204)) else d24 (change p 10000 (some 204))) = d1802 p
  rw [sub12644, sub12643]
  rfl
theorem sub12646 (p : Pattern) : d1803 (change p 10000 (some 204)) = d1803 p := by
  change (if p 224 then d356 (change p 10000 (some 204)) else d1802 (change p 10000 (some 204))) = d1803 p
  rw [sub12644, sub12645]
  rfl
theorem sub12647 (p : Pattern) : d2901 (change p 10000 (some 204)) = d1803 p := by
  change d1803 (change p 10000 (some 204)) = d1803 p
  exact sub12646 p
theorem sub12648 (p : Pattern) : d1705 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12649 (p : Pattern) : d2902 (change p 10000 (some 204)) = d7018 p := by
  change (if p 182 then d1705 (change p 10000 (some 204)) else d2901 (change p 10000 (some 204))) = d7018 p
  rw [sub12648, sub12647]
  rfl
theorem sub12650 (p : Pattern) : d2903 (change p 10000 (some 204)) = d7019 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2902 (change p 10000 (some 204))) = d7019 p
  rw [sub12617, sub12649]
  rfl
theorem sub12651 (p : Pattern) : d2904 (change p 10000 (some 204)) = d7020 p := by
  change (if p 162 then d2903 (change p 10000 (some 204)) else d2899 (change p 10000 (some 204))) = d7020 p
  rw [sub12650, sub12639]
  rfl
theorem sub12652 (p : Pattern) : d2905 (change p 10000 (some 204)) = d7021 p := by
  change (if p 161 then d2904 (change p 10000 (some 204)) else d2900 (change p 10000 (some 204))) = d7021 p
  rw [sub12651, sub12640]
  rfl
theorem sub12653 (p : Pattern) : d6 (change p 10000 (some 204)) = d6 p := by
  rfl
theorem sub12654 (p : Pattern) : d1775 (change p 10000 (some 204)) = d1775 p := by
  change (if p 247 then d6 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d1775 p
  rw [sub12653, sub12616]
  rfl
theorem sub12655 (p : Pattern) : d34 (change p 10000 (some 204)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d6 (change p 10000 (some 204))) = d34 p
  rw [sub12617, sub12653]
  rfl
theorem sub12656 (p : Pattern) : d1776 (change p 10000 (some 204)) = d1776 p := by
  change (if p 246 then d34 (change p 10000 (some 204)) else d1775 (change p 10000 (some 204))) = d1776 p
  rw [sub12655, sub12654]
  rfl
theorem sub12657 (p : Pattern) : d1777 (change p 10000 (some 204)) = d1777 p := by
  change (if p 225 then d1776 (change p 10000 (some 204)) else d14 (change p 10000 (some 204))) = d1777 p
  rw [sub12656, sub12619]
  rfl
theorem sub12658 (p : Pattern) : d11 (change p 10000 (some 204)) = d11 p := by
  rfl
theorem sub12659 (p : Pattern) : d1785 (change p 10000 (some 204)) = d1785 p := by
  change (if p 247 then d11 (change p 10000 (some 204)) else d0 (change p 10000 (some 204))) = d1785 p
  rw [sub12658, sub12616]
  rfl
theorem sub12660 (p : Pattern) : d1786 (change p 10000 (some 204)) = d1786 p := by
  change (if p 246 then d23 (change p 10000 (some 204)) else d1785 (change p 10000 (some 204))) = d1786 p
  rw [sub12642, sub12659]
  rfl
theorem sub12661 (p : Pattern) : d1787 (change p 10000 (some 204)) = d1787 p := by
  change (if p 225 then d1786 (change p 10000 (some 204)) else d1770 (change p 10000 (some 204))) = d1787 p
  rw [sub12660, sub12623]
  rfl
theorem sub12662 (p : Pattern) : d1788 (change p 10000 (some 204)) = d1788 p := by
  change (if p 224 then d1787 (change p 10000 (some 204)) else d1777 (change p 10000 (some 204))) = d1788 p
  rw [sub12661, sub12657]
  rfl
theorem sub12663 (p : Pattern) : d2906 (change p 10000 (some 204)) = d1788 p := by
  change d1788 (change p 10000 (some 204)) = d1788 p
  exact sub12662 p
theorem sub12664 (p : Pattern) : d1718 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12665 (p : Pattern) : d2907 (change p 10000 (some 204)) = d7022 p := by
  change (if p 182 then d1718 (change p 10000 (some 204)) else d2906 (change p 10000 (some 204))) = d7022 p
  rw [sub12664, sub12663]
  rfl
theorem sub12666 (p : Pattern) : d1725 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12667 (p : Pattern) : d2908 (change p 10000 (some 204)) = d7022 p := by
  change (if p 182 then d1725 (change p 10000 (some 204)) else d2906 (change p 10000 (some 204))) = d7022 p
  rw [sub12666, sub12663]
  rfl
theorem sub12668 (p : Pattern) : d2909 (change p 10000 (some 204)) = d7022 p := by
  change (if p 163 then d2908 (change p 10000 (some 204)) else d2907 (change p 10000 (some 204))) = d7022 p
  rw [sub12667, sub12665]
  simp only [ite_self]
theorem sub12669 (p : Pattern) : d1730 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12670 (p : Pattern) : d2910 (change p 10000 (some 204)) = d7022 p := by
  change (if p 182 then d1730 (change p 10000 (some 204)) else d2906 (change p 10000 (some 204))) = d7022 p
  rw [sub12669, sub12663]
  rfl
theorem sub12671 (p : Pattern) : d10 (change p 10000 (some 204)) = d10 p := by
  rfl
theorem sub12672 (p : Pattern) : d1791 (change p 10000 (some 204)) = d1791 p := by
  change (if p 247 then d10 (change p 10000 (some 204)) else d4 (change p 10000 (some 204))) = d1791 p
  rw [sub12671, sub12620]
  rfl
theorem sub12673 (p : Pattern) : d57 (change p 10000 (some 204)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d10 (change p 10000 (some 204))) = d57 p
  rw [sub12617, sub12671]
  rfl
theorem sub12674 (p : Pattern) : d1792 (change p 10000 (some 204)) = d1792 p := by
  change (if p 246 then d57 (change p 10000 (some 204)) else d1791 (change p 10000 (some 204))) = d1792 p
  rw [sub12673, sub12672]
  rfl
theorem sub12675 (p : Pattern) : d1793 (change p 10000 (some 204)) = d1793 p := by
  change (if p 225 then d1792 (change p 10000 (some 204)) else d18 (change p 10000 (some 204))) = d1793 p
  rw [sub12674, sub12629]
  rfl
theorem sub12676 (p : Pattern) : d339 (change p 10000 (some 204)) = d339 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d17 (change p 10000 (some 204))) = d339 p
  rw [sub12617, sub12622]
  rfl
theorem sub12677 (p : Pattern) : d1796 (change p 10000 (some 204)) = d1796 p := by
  change (if p 225 then d339 (change p 10000 (some 204)) else d1795 (change p 10000 (some 204))) = d1796 p
  rw [sub12676, sub12633]
  rfl
theorem sub12678 (p : Pattern) : d1797 (change p 10000 (some 204)) = d1797 p := by
  change (if p 224 then d1796 (change p 10000 (some 204)) else d1793 (change p 10000 (some 204))) = d1797 p
  rw [sub12677, sub12675]
  rfl
theorem sub12679 (p : Pattern) : d2911 (change p 10000 (some 204)) = d1797 p := by
  change d1797 (change p 10000 (some 204)) = d1797 p
  exact sub12678 p
theorem sub12680 (p : Pattern) : d2912 (change p 10000 (some 204)) = d7023 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2911 (change p 10000 (some 204))) = d7023 p
  rw [sub12617, sub12679]
  rfl
theorem sub12681 (p : Pattern) : d2913 (change p 10000 (some 204)) = d7024 p := by
  change (if p 163 then d2912 (change p 10000 (some 204)) else d2910 (change p 10000 (some 204))) = d7024 p
  rw [sub12680, sub12670]
  rfl
theorem sub12682 (p : Pattern) : d2914 (change p 10000 (some 204)) = d7025 p := by
  change (if p 162 then d2913 (change p 10000 (some 204)) else d2909 (change p 10000 (some 204))) = d7025 p
  rw [sub12681, sub12668]
  rfl
theorem sub12683 (p : Pattern) : d2915 (change p 10000 (some 204)) = d7022 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2906 (change p 10000 (some 204))) = d7022 p
  rw [sub12617, sub12663]
  rfl
theorem sub12684 (p : Pattern) : d2916 (change p 10000 (some 204)) = d7024 p := by
  change (if p 163 then d2912 (change p 10000 (some 204)) else d2915 (change p 10000 (some 204))) = d7024 p
  rw [sub12680, sub12683]
  rfl
theorem sub12685 (p : Pattern) : d2917 (change p 10000 (some 204)) = d7018 p := by
  change (if p 182 then d12 (change p 10000 (some 204)) else d2901 (change p 10000 (some 204))) = d7018 p
  rw [sub12617, sub12647]
  rfl
theorem sub12686 (p : Pattern) : d2918 (change p 10000 (some 204)) = d7019 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2917 (change p 10000 (some 204))) = d7019 p
  rw [sub12617, sub12685]
  rfl
theorem sub12687 (p : Pattern) : d2919 (change p 10000 (some 204)) = d7026 p := by
  change (if p 162 then d2918 (change p 10000 (some 204)) else d2916 (change p 10000 (some 204))) = d7026 p
  rw [sub12686, sub12684]
  rfl
theorem sub12688 (p : Pattern) : d2920 (change p 10000 (some 204)) = d7027 p := by
  change (if p 161 then d2919 (change p 10000 (some 204)) else d2914 (change p 10000 (some 204))) = d7027 p
  rw [sub12687, sub12682]
  rfl
theorem sub12689 (p : Pattern) : d2921 (change p 10000 (some 204)) = d7028 p := by
  change (if p 160 then d2920 (change p 10000 (some 204)) else d2905 (change p 10000 (some 204))) = d7028 p
  rw [sub12688, sub12652]
  rfl
theorem sub12690 (p : Pattern) : d2 (change p 10000 (some 204)) = d2 p := by
  rfl
theorem sub12691 (p : Pattern) : d30 (change p 10000 (some 204)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d2 (change p 10000 (some 204))) = d30 p
  rw [sub12617, sub12690]
  rfl
theorem sub12692 (p : Pattern) : d31 (change p 10000 (some 204)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 204)) else d2 (change p 10000 (some 204))) = d31 p
  rw [sub12691, sub12690]
  rfl
theorem sub12693 (p : Pattern) : d1713 (change p 10000 (some 204)) = d1713 p := by
  change (if p 247 then d6 (change p 10000 (some 204)) else d2 (change p 10000 (some 204))) = d1713 p
  rw [sub12653, sub12690]
  rfl
theorem sub12694 (p : Pattern) : d1714 (change p 10000 (some 204)) = d1714 p := by
  change (if p 246 then d34 (change p 10000 (some 204)) else d1713 (change p 10000 (some 204))) = d1714 p
  rw [sub12655, sub12693]
  rfl
theorem sub12695 (p : Pattern) : d2029 (change p 10000 (some 204)) = d2029 p := by
  change (if p 225 then d1714 (change p 10000 (some 204)) else d31 (change p 10000 (some 204))) = d2029 p
  rw [sub12694, sub12692]
  rfl
theorem sub12696 (p : Pattern) : d2030 (change p 10000 (some 204)) = d2030 p := by
  change (if p 224 then d1714 (change p 10000 (some 204)) else d2029 (change p 10000 (some 204))) = d2030 p
  rw [sub12694, sub12695]
  rfl
theorem sub12697 (p : Pattern) : d2922 (change p 10000 (some 204)) = d2030 p := by
  change d2030 (change p 10000 (some 204)) = d2030 p
  exact sub12696 p
theorem sub12698 (p : Pattern) : d1746 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12699 (p : Pattern) : d2923 (change p 10000 (some 204)) = d7029 p := by
  change (if p 182 then d1746 (change p 10000 (some 204)) else d2922 (change p 10000 (some 204))) = d7029 p
  rw [sub12698, sub12697]
  rfl
theorem sub12700 (p : Pattern) : d2924 (change p 10000 (some 204)) = d7030 p := by
  change (if p 163 then d2923 (change p 10000 (some 204)) else d2896 (change p 10000 (some 204))) = d7030 p
  rw [sub12699, sub12628]
  rfl
theorem sub12701 (p : Pattern) : d2925 (change p 10000 (some 204)) = d7031 p := by
  change (if p 163 then d2902 (change p 10000 (some 204)) else d2898 (change p 10000 (some 204))) = d7031 p
  rw [sub12649, sub12638]
  rfl
theorem sub12702 (p : Pattern) : d2926 (change p 10000 (some 204)) = d7032 p := by
  change (if p 162 then d2925 (change p 10000 (some 204)) else d2924 (change p 10000 (some 204))) = d7032 p
  rw [sub12701, sub12700]
  rfl
theorem sub12703 (p : Pattern) : d58 (change p 10000 (some 204)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 204)) else d10 (change p 10000 (some 204))) = d58 p
  rw [sub12673, sub12671]
  rfl
theorem sub12704 (p : Pattern) : d329 (change p 10000 (some 204)) = d329 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d57 (change p 10000 (some 204))) = d329 p
  rw [sub12617, sub12673]
  rfl
theorem sub12705 (p : Pattern) : d1751 (change p 10000 (some 204)) = d1751 p := by
  change (if p 225 then d329 (change p 10000 (some 204)) else d58 (change p 10000 (some 204))) = d1751 p
  rw [sub12704, sub12703]
  rfl
theorem sub12706 (p : Pattern) : d1752 (change p 10000 (some 204)) = d1752 p := by
  change (if p 224 then d329 (change p 10000 (some 204)) else d1751 (change p 10000 (some 204))) = d1752 p
  rw [sub12704, sub12705]
  rfl
theorem sub12707 (p : Pattern) : d2927 (change p 10000 (some 204)) = d1752 p := by
  change d1752 (change p 10000 (some 204)) = d1752 p
  exact sub12706 p
theorem sub12708 (p : Pattern) : d1753 (change p 10000 (some 204)) = d12 p := by
  change d12 (change p 10000 (some 204)) = d12 p
  exact sub12617 p
theorem sub12709 (p : Pattern) : d2928 (change p 10000 (some 204)) = d7033 p := by
  change (if p 182 then d1753 (change p 10000 (some 204)) else d2927 (change p 10000 (some 204))) = d7033 p
  rw [sub12708, sub12707]
  rfl
theorem sub12710 (p : Pattern) : d2929 (change p 10000 (some 204)) = d7034 p := by
  change (if p 163 then d2928 (change p 10000 (some 204)) else d2898 (change p 10000 (some 204))) = d7034 p
  rw [sub12709, sub12638]
  rfl
theorem sub12711 (p : Pattern) : d39 (change p 10000 (some 204)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 204)) else d11 (change p 10000 (some 204))) = d39 p
  rw [sub12617, sub12658]
  rfl
theorem sub12712 (p : Pattern) : d40 (change p 10000 (some 204)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 204)) else d11 (change p 10000 (some 204))) = d40 p
  rw [sub12711, sub12658]
  rfl
theorem sub12713 (p : Pattern) : d327 (change p 10000 (some 204)) = d327 p := by
  change (if p 246 then d12 (change p 10000 (some 204)) else d39 (change p 10000 (some 204))) = d327 p
  rw [sub12617, sub12711]
  rfl
theorem sub12714 (p : Pattern) : d1728 (change p 10000 (some 204)) = d1728 p := by
  change (if p 225 then d327 (change p 10000 (some 204)) else d40 (change p 10000 (some 204))) = d1728 p
  rw [sub12713, sub12712]
  rfl
theorem sub12715 (p : Pattern) : d1729 (change p 10000 (some 204)) = d1729 p := by
  change (if p 224 then d327 (change p 10000 (some 204)) else d1728 (change p 10000 (some 204))) = d1729 p
  rw [sub12713, sub12714]
  rfl
theorem sub12716 (p : Pattern) : d2930 (change p 10000 (some 204)) = d1729 p := by
  change d1729 (change p 10000 (some 204)) = d1729 p
  exact sub12715 p
theorem sub12717 (p : Pattern) : d2931 (change p 10000 (some 204)) = d7035 p := by
  change (if p 182 then d1730 (change p 10000 (some 204)) else d2930 (change p 10000 (some 204))) = d7035 p
  rw [sub12669, sub12716]
  rfl
theorem sub12718 (p : Pattern) : d2932 (change p 10000 (some 204)) = d7036 p := by
  change (if p 163 then d12 (change p 10000 (some 204)) else d2931 (change p 10000 (some 204))) = d7036 p
  rw [sub12617, sub12717]
  rfl
theorem sub12719 (p : Pattern) : d2933 (change p 10000 (some 204)) = d7037 p := by
  change (if p 162 then d2932 (change p 10000 (some 204)) else d2929 (change p 10000 (some 204))) = d7037 p
  rw [sub12718, sub12710]
  rfl
end NetHack.Sokoban22Refined85
