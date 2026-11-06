/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions45
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub5520 (p : Pattern) : d115 (change p 160 none) = d115 p := by
  change (if p 247 then d12 (change p 160 none) else d3 (change p 160 none)) = d115 p
  rw [sub5423, sub5519]
  rfl
theorem sub5521 (p : Pattern) : d116 (change p 160 none) = d116 p := by
  change (if p 246 then d115 (change p 160 none) else d3 (change p 160 none)) = d116 p
  rw [sub5520, sub5519]
  rfl
theorem sub5522 (p : Pattern) : d117 (change p 160 none) = d117 p := by
  change (if p 204 then d12 (change p 160 none) else d116 (change p 160 none)) = d117 p
  rw [sub5423, sub5521]
  rfl
theorem sub5523 (p : Pattern) : d132 (change p 160 none) = d132 p := by
  change (if p 182 then d117 (change p 160 none) else d116 (change p 160 none)) = d132 p
  rw [sub5522, sub5521]
  rfl
theorem sub5524 (p : Pattern) : d133 (change p 160 none) = d133 p := by
  change (if p 163 then d132 (change p 160 none) else d105 (change p 160 none)) = d133 p
  rw [sub5523, sub5507]
  rfl
theorem sub5525 (p : Pattern) : d134 (change p 160 none) = d134 p := by
  change (if p 163 then d60 (change p 160 none) else d109 (change p 160 none)) = d134 p
  rw [sub5456, sub5512]
  rfl
theorem sub5526 (p : Pattern) : d135 (change p 160 none) = d135 p := by
  change (if p 162 then d134 (change p 160 none) else d133 (change p 160 none)) = d135 p
  rw [sub5525, sub5524]
  rfl
theorem sub5527 (p : Pattern) : d136 (change p 160 none) = d136 p := by
  change (if p 163 then d62 (change p 160 none) else d109 (change p 160 none)) = d136 p
  rw [sub5462, sub5512]
  rfl
theorem sub5528 (p : Pattern) : d137 (change p 160 none) = d137 p := by
  change (if p 162 then d12 (change p 160 none) else d136 (change p 160 none)) = d137 p
  rw [sub5423, sub5527]
  rfl
theorem sub5529 (p : Pattern) : d138 (change p 160 none) = d138 p := by
  change (if p 161 then d137 (change p 160 none) else d135 (change p 160 none)) = d138 p
  rw [sub5528, sub5526]
  rfl
theorem sub5530 (p : Pattern) : d743 (change p 160 none) = d138 p := by
  change d138 (change p 160 none) = d138 p
  exact sub5529 p
theorem sub5531 (p : Pattern) : d744 (change p 160 none) = d4736 p := by
  change (if p 141 then d743 (change p 160 none) else d742 (change p 160 none)) = d4736 p
  rw [sub5530, sub5518]
  rfl
theorem sub5532 (p : Pattern) : d745 (change p 160 none) = d114 p := by
  change d114 (change p 160 none) = d114 p
  exact sub5517 p
theorem sub5533 (p : Pattern) : d746 (change p 160 none) = d138 p := by
  change d138 (change p 160 none) = d138 p
  exact sub5529 p
theorem sub5534 (p : Pattern) : d747 (change p 160 none) = d4736 p := by
  change (if p 141 then d746 (change p 160 none) else d745 (change p 160 none)) = d4736 p
  rw [sub5533, sub5532]
  rfl
theorem sub5535 (p : Pattern) : d748 (change p 160 none) = d4736 p := by
  change (if p 138 then d747 (change p 160 none) else d744 (change p 160 none)) = d4736 p
  rw [sub5534, sub5531]
  simp only [ite_self]
theorem sub5536 (p : Pattern) : d749 (change p 160 none) = d114 p := by
  change d114 (change p 160 none) = d114 p
  exact sub5517 p
theorem sub5537 (p : Pattern) : d750 (change p 160 none) = d4736 p := by
  change (if p 141 then d746 (change p 160 none) else d749 (change p 160 none)) = d4736 p
  rw [sub5533, sub5536]
  rfl
theorem sub5538 (p : Pattern) : d159 (change p 160 none) = d159 p := by
  change (if p 162 then d12 (change p 160 none) else d112 (change p 160 none)) = d159 p
  rw [sub5423, sub5515]
  rfl
theorem sub5539 (p : Pattern) : d160 (change p 160 none) = d160 p := by
  change (if p 161 then d12 (change p 160 none) else d159 (change p 160 none)) = d160 p
  rw [sub5423, sub5538]
  rfl
theorem sub5540 (p : Pattern) : d161 (change p 160 none) = d160 p := by
  change d160 (change p 160 none) = d160 p
  exact sub5539 p
theorem sub5541 (p : Pattern) : d162 (change p 160 none) = d4737 p := by
  change (if p 141 then d12 (change p 160 none) else d161 (change p 160 none)) = d4737 p
  rw [sub5423, sub5540]
  rfl
theorem sub5542 (p : Pattern) : d751 (change p 160 none) = d4738 p := by
  change (if p 138 then d162 (change p 160 none) else d750 (change p 160 none)) = d4738 p
  rw [sub5541, sub5537]
  rfl
theorem sub5543 (p : Pattern) : d752 (change p 160 none) = d4739 p := by
  change (if p 116 then d751 (change p 160 none) else d748 (change p 160 none)) = d4739 p
  rw [sub5542, sub5535]
  rfl
theorem sub5544 (p : Pattern) : d753 (change p 160 none) = d114 p := by
  change d114 (change p 160 none) = d114 p
  exact sub5517 p
theorem sub5545 (p : Pattern) : d754 (change p 160 none) = d4736 p := by
  change (if p 141 then d746 (change p 160 none) else d753 (change p 160 none)) = d4736 p
  rw [sub5533, sub5544]
  rfl
theorem sub5546 (p : Pattern) : d755 (change p 160 none) = d4736 p := by
  change (if p 138 then d747 (change p 160 none) else d754 (change p 160 none)) = d4736 p
  rw [sub5534, sub5545]
  simp only [ite_self]
theorem sub5547 (p : Pattern) : d756 (change p 160 none) = d4740 p := by
  change (if p 138 then d12 (change p 160 none) else d747 (change p 160 none)) = d4740 p
  rw [sub5423, sub5534]
  rfl
theorem sub5548 (p : Pattern) : d757 (change p 160 none) = d4741 p := by
  change (if p 116 then d756 (change p 160 none) else d755 (change p 160 none)) = d4741 p
  rw [sub5547, sub5546]
  rfl
theorem sub5549 (p : Pattern) : d758 (change p 160 none) = d4742 p := by
  change (if p 115 then d757 (change p 160 none) else d752 (change p 160 none)) = d4742 p
  rw [sub5548, sub5543]
  rfl
theorem sub5550 (p : Pattern) : d759 (change p 160 none) = d4743 p := by
  change (if p 71 then d758 (change p 160 none) else d731 (change p 160 none)) = d4743 p
  rw [sub5549, sub5492]
  rfl
theorem sub5551 (p : Pattern) : d760 (change p 160 none) = d4744 p := by
  change (if p 49 then d759 (change p 160 none) else d741 (change p 160 none)) = d4744 p
  rw [sub5550, sub5502]
  rfl
theorem sub5552 (p : Pattern) : d6 (change p 160 none) = d6 p := by
  rfl
theorem sub5553 (p : Pattern) : d34 (change p 160 none) = d34 p := by
  change (if p 247 then d12 (change p 160 none) else d6 (change p 160 none)) = d34 p
  rw [sub5423, sub5552]
  rfl
theorem sub5554 (p : Pattern) : d35 (change p 160 none) = d35 p := by
  change (if p 246 then d34 (change p 160 none) else d6 (change p 160 none)) = d35 p
  rw [sub5553, sub5552]
  rfl
theorem sub5555 (p : Pattern) : d36 (change p 160 none) = d36 p := by
  change (if p 204 then d12 (change p 160 none) else d35 (change p 160 none)) = d36 p
  rw [sub5423, sub5554]
  rfl
theorem sub5556 (p : Pattern) : d78 (change p 160 none) = d78 p := by
  change (if p 182 then d36 (change p 160 none) else d35 (change p 160 none)) = d78 p
  rw [sub5555, sub5554]
  rfl
theorem sub5557 (p : Pattern) : d79 (change p 160 none) = d79 p := by
  change (if p 163 then d78 (change p 160 none) else d53 (change p 160 none)) = d79 p
  rw [sub5556, sub5448]
  rfl
theorem sub5558 (p : Pattern) : d188 (change p 160 none) = d188 p := by
  change (if p 162 then d79 (change p 160 none) else d16 (change p 160 none)) = d188 p
  rw [sub5557, sub5427]
  rfl
theorem sub5559 (p : Pattern) : d80 (change p 160 none) = d80 p := by
  change (if p 162 then d63 (change p 160 none) else d79 (change p 160 none)) = d80 p
  rw [sub5463, sub5557]
  rfl
theorem sub5560 (p : Pattern) : d189 (change p 160 none) = d189 p := by
  change (if p 161 then d80 (change p 160 none) else d188 (change p 160 none)) = d189 p
  rw [sub5559, sub5558]
  rfl
theorem sub5561 (p : Pattern) : d761 (change p 160 none) = d189 p := by
  change d189 (change p 160 none) = d189 p
  exact sub5560 p
theorem sub5562 (p : Pattern) : d198 (change p 160 none) = d198 p := by
  change (if p 163 then d62 (change p 160 none) else d20 (change p 160 none)) = d198 p
  rw [sub5462, sub5432]
  rfl
theorem sub5563 (p : Pattern) : d199 (change p 160 none) = d199 p := by
  change (if p 162 then d198 (change p 160 none) else d53 (change p 160 none)) = d199 p
  rw [sub5562, sub5448]
  rfl
theorem sub5564 (p : Pattern) : d83 (change p 160 none) = d83 p := by
  change (if p 163 then d12 (change p 160 none) else d78 (change p 160 none)) = d83 p
  rw [sub5423, sub5556]
  rfl
theorem sub5565 (p : Pattern) : d84 (change p 160 none) = d84 p := by
  change (if p 162 then d12 (change p 160 none) else d83 (change p 160 none)) = d84 p
  rw [sub5423, sub5564]
  rfl
theorem sub5566 (p : Pattern) : d200 (change p 160 none) = d200 p := by
  change (if p 161 then d84 (change p 160 none) else d199 (change p 160 none)) = d200 p
  rw [sub5565, sub5563]
  rfl
theorem sub5567 (p : Pattern) : d762 (change p 160 none) = d200 p := by
  change d200 (change p 160 none) = d200 p
  exact sub5566 p
theorem sub5568 (p : Pattern) : d763 (change p 160 none) = d4745 p := by
  change (if p 141 then d762 (change p 160 none) else d761 (change p 160 none)) = d4745 p
  rw [sub5567, sub5561]
  rfl
theorem sub5569 (p : Pattern) : d764 (change p 160 none) = d4746 p := by
  change (if p 138 then d763 (change p 160 none) else d718 (change p 160 none)) = d4746 p
  rw [sub5568, sub5473]
  rfl
theorem sub5570 (p : Pattern) : d765 (change p 160 none) = d4747 p := by
  change (if p 138 then d12 (change p 160 none) else d763 (change p 160 none)) = d4747 p
  rw [sub5423, sub5568]
  rfl
theorem sub5571 (p : Pattern) : d766 (change p 160 none) = d4748 p := by
  change (if p 116 then d765 (change p 160 none) else d764 (change p 160 none)) = d4748 p
  rw [sub5570, sub5569]
  rfl
theorem sub5572 (p : Pattern) : d767 (change p 160 none) = d4749 p := by
  change (if p 115 then d766 (change p 160 none) else d737 (change p 160 none)) = d4749 p
  rw [sub5571, sub5498]
  rfl
theorem sub5573 (p : Pattern) : d768 (change p 160 none) = d4750 p := by
  change (if p 71 then d767 (change p 160 none) else d731 (change p 160 none)) = d4750 p
  rw [sub5572, sub5492]
  rfl
theorem sub5574 (p : Pattern) : d211 (change p 160 none) = d211 p := by
  change (if p 163 then d12 (change p 160 none) else d109 (change p 160 none)) = d211 p
  rw [sub5423, sub5512]
  rfl
theorem sub5575 (p : Pattern) : d212 (change p 160 none) = d212 p := by
  change (if p 162 then d211 (change p 160 none) else d133 (change p 160 none)) = d212 p
  rw [sub5574, sub5524]
  rfl
theorem sub5576 (p : Pattern) : d213 (change p 160 none) = d213 p := by
  change (if p 162 then d12 (change p 160 none) else d211 (change p 160 none)) = d213 p
  rw [sub5423, sub5574]
  rfl
theorem sub5577 (p : Pattern) : d214 (change p 160 none) = d214 p := by
  change (if p 161 then d213 (change p 160 none) else d212 (change p 160 none)) = d214 p
  rw [sub5576, sub5575]
  rfl
theorem sub5578 (p : Pattern) : d769 (change p 160 none) = d214 p := by
  change d214 (change p 160 none) = d214 p
  exact sub5577 p
theorem sub5579 (p : Pattern) : d770 (change p 160 none) = d4751 p := by
  change (if p 141 then d769 (change p 160 none) else d742 (change p 160 none)) = d4751 p
  rw [sub5578, sub5518]
  rfl
theorem sub5580 (p : Pattern) : d771 (change p 160 none) = d214 p := by
  change d214 (change p 160 none) = d214 p
  exact sub5577 p
theorem sub5581 (p : Pattern) : d772 (change p 160 none) = d4751 p := by
  change (if p 141 then d771 (change p 160 none) else d745 (change p 160 none)) = d4751 p
  rw [sub5580, sub5532]
  rfl
theorem sub5582 (p : Pattern) : d773 (change p 160 none) = d4751 p := by
  change (if p 138 then d772 (change p 160 none) else d770 (change p 160 none)) = d4751 p
  rw [sub5581, sub5579]
  simp only [ite_self]
theorem sub5583 (p : Pattern) : d774 (change p 160 none) = d4751 p := by
  change (if p 141 then d771 (change p 160 none) else d749 (change p 160 none)) = d4751 p
  rw [sub5580, sub5536]
  rfl
theorem sub5584 (p : Pattern) : d775 (change p 160 none) = d4752 p := by
  change (if p 138 then d162 (change p 160 none) else d774 (change p 160 none)) = d4752 p
  rw [sub5541, sub5583]
  rfl
theorem sub5585 (p : Pattern) : d776 (change p 160 none) = d4753 p := by
  change (if p 116 then d775 (change p 160 none) else d773 (change p 160 none)) = d4753 p
  rw [sub5584, sub5582]
  rfl
theorem sub5586 (p : Pattern) : d777 (change p 160 none) = d4751 p := by
  change (if p 141 then d771 (change p 160 none) else d753 (change p 160 none)) = d4751 p
  rw [sub5580, sub5544]
  rfl
theorem sub5587 (p : Pattern) : d241 (change p 160 none) = d241 p := by
  change (if p 163 then d62 (change p 160 none) else d132 (change p 160 none)) = d241 p
  rw [sub5462, sub5523]
  rfl
theorem sub5588 (p : Pattern) : d242 (change p 160 none) = d242 p := by
  change (if p 162 then d241 (change p 160 none) else d105 (change p 160 none)) = d242 p
  rw [sub5587, sub5507]
  rfl
theorem sub5589 (p : Pattern) : d243 (change p 160 none) = d243 p := by
  change (if p 161 then d137 (change p 160 none) else d242 (change p 160 none)) = d243 p
  rw [sub5528, sub5588]
  rfl
theorem sub5590 (p : Pattern) : d778 (change p 160 none) = d243 p := by
  change d243 (change p 160 none) = d243 p
  exact sub5589 p
theorem sub5591 (p : Pattern) : d245 (change p 160 none) = d245 p := by
  change (if p 162 then d211 (change p 160 none) else d132 (change p 160 none)) = d245 p
  rw [sub5574, sub5523]
  rfl
theorem sub5592 (p : Pattern) : d7 (change p 160 none) = d7 p := by
  rfl
theorem sub5593 (p : Pattern) : d119 (change p 160 none) = d119 p := by
  change (if p 247 then d12 (change p 160 none) else d7 (change p 160 none)) = d119 p
  rw [sub5423, sub5592]
  rfl
theorem sub5594 (p : Pattern) : d120 (change p 160 none) = d120 p := by
  change (if p 246 then d119 (change p 160 none) else d7 (change p 160 none)) = d120 p
  rw [sub5593, sub5592]
  rfl
theorem sub5595 (p : Pattern) : d121 (change p 160 none) = d121 p := by
  change (if p 204 then d12 (change p 160 none) else d120 (change p 160 none)) = d121 p
  rw [sub5423, sub5594]
  rfl
theorem sub5596 (p : Pattern) : d148 (change p 160 none) = d148 p := by
  change (if p 182 then d121 (change p 160 none) else d120 (change p 160 none)) = d148 p
  rw [sub5595, sub5594]
  rfl
theorem sub5597 (p : Pattern) : d153 (change p 160 none) = d153 p := by
  change (if p 163 then d12 (change p 160 none) else d148 (change p 160 none)) = d153 p
  rw [sub5423, sub5596]
  rfl
theorem sub5598 (p : Pattern) : d154 (change p 160 none) = d154 p := by
  change (if p 162 then d12 (change p 160 none) else d153 (change p 160 none)) = d154 p
  rw [sub5423, sub5597]
  rfl
theorem sub5599 (p : Pattern) : d246 (change p 160 none) = d246 p := by
  change (if p 161 then d154 (change p 160 none) else d245 (change p 160 none)) = d246 p
  rw [sub5598, sub5591]
  rfl
theorem sub5600 (p : Pattern) : d779 (change p 160 none) = d246 p := by
  change d246 (change p 160 none) = d246 p
  exact sub5599 p
theorem sub5601 (p : Pattern) : d780 (change p 160 none) = d4754 p := by
  change (if p 141 then d779 (change p 160 none) else d778 (change p 160 none)) = d4754 p
  rw [sub5600, sub5590]
  rfl
theorem sub5602 (p : Pattern) : d781 (change p 160 none) = d4755 p := by
  change (if p 138 then d780 (change p 160 none) else d777 (change p 160 none)) = d4755 p
  rw [sub5601, sub5586]
  rfl
theorem sub5603 (p : Pattern) : d252 (change p 160 none) = d252 p := by
  change (if p 163 then d26 (change p 160 none) else d132 (change p 160 none)) = d252 p
  rw [sub5439, sub5523]
  rfl
theorem sub5604 (p : Pattern) : d253 (change p 160 none) = d253 p := by
  change (if p 162 then d252 (change p 160 none) else d105 (change p 160 none)) = d253 p
  rw [sub5603, sub5507]
  rfl
theorem sub5605 (p : Pattern) : d254 (change p 160 none) = d254 p := by
  change (if p 163 then d26 (change p 160 none) else d109 (change p 160 none)) = d254 p
  rw [sub5439, sub5512]
  rfl
theorem sub5606 (p : Pattern) : d255 (change p 160 none) = d255 p := by
  change (if p 162 then d12 (change p 160 none) else d254 (change p 160 none)) = d255 p
  rw [sub5423, sub5605]
  rfl
theorem sub5607 (p : Pattern) : d256 (change p 160 none) = d256 p := by
  change (if p 161 then d255 (change p 160 none) else d253 (change p 160 none)) = d256 p
  rw [sub5606, sub5604]
  rfl
theorem sub5608 (p : Pattern) : d782 (change p 160 none) = d256 p := by
  change d256 (change p 160 none) = d256 p
  exact sub5607 p
theorem sub5609 (p : Pattern) : d783 (change p 160 none) = d4756 p := by
  change (if p 141 then d779 (change p 160 none) else d782 (change p 160 none)) = d4756 p
  rw [sub5600, sub5608]
  rfl
theorem sub5610 (p : Pattern) : d784 (change p 160 none) = d4757 p := by
  change (if p 138 then d12 (change p 160 none) else d783 (change p 160 none)) = d4757 p
  rw [sub5423, sub5609]
  rfl
theorem sub5611 (p : Pattern) : d785 (change p 160 none) = d4758 p := by
  change (if p 116 then d784 (change p 160 none) else d781 (change p 160 none)) = d4758 p
  rw [sub5610, sub5602]
  rfl
theorem sub5612 (p : Pattern) : d786 (change p 160 none) = d4759 p := by
  change (if p 115 then d785 (change p 160 none) else d776 (change p 160 none)) = d4759 p
  rw [sub5611, sub5585]
  rfl
theorem sub5613 (p : Pattern) : d787 (change p 160 none) = d4760 p := by
  change (if p 71 then d786 (change p 160 none) else d731 (change p 160 none)) = d4760 p
  rw [sub5612, sub5492]
  rfl
theorem sub5614 (p : Pattern) : d788 (change p 160 none) = d4761 p := by
  change (if p 49 then d787 (change p 160 none) else d768 (change p 160 none)) = d4761 p
  rw [sub5613, sub5573]
  rfl
theorem sub5615 (p : Pattern) : d789 (change p 160 none) = d4762 p := by
  change (if p 48 then d788 (change p 160 none) else d760 (change p 160 none)) = d4762 p
  rw [sub5614, sub5551]
  rfl
theorem sub5616 (p : Pattern) : d0 (change p 161 (some 160)) = d0 p := by
  rfl
theorem sub5617 (p : Pattern) : d12 (change p 161 (some 160)) = d12 p := by
  rfl
theorem sub5618 (p : Pattern) : d13 (change p 161 (some 160)) = d13 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d0 (change p 161 (some 160))) = d13 p
  rw [sub5617, sub5616]
  rfl
theorem sub5619 (p : Pattern) : d14 (change p 161 (some 160)) = d14 p := by
  change (if p 246 then d13 (change p 161 (some 160)) else d0 (change p 161 (some 160))) = d14 p
  rw [sub5618, sub5616]
  rfl
theorem sub5620 (p : Pattern) : d2 (change p 161 (some 160)) = d2 p := by
  rfl
theorem sub5621 (p : Pattern) : d30 (change p 161 (some 160)) = d30 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d2 (change p 161 (some 160))) = d30 p
  rw [sub5617, sub5620]
  rfl
theorem sub5622 (p : Pattern) : d31 (change p 161 (some 160)) = d31 p := by
  change (if p 246 then d30 (change p 161 (some 160)) else d2 (change p 161 (some 160))) = d31 p
  rw [sub5621, sub5620]
  rfl
theorem sub5623 (p : Pattern) : d32 (change p 161 (some 160)) = d32 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d31 (change p 161 (some 160))) = d32 p
  rw [sub5617, sub5622]
  rfl
theorem sub5624 (p : Pattern) : d33 (change p 161 (some 160)) = d33 p := by
  change (if p 182 then d32 (change p 161 (some 160)) else d14 (change p 161 (some 160))) = d33 p
  rw [sub5623, sub5619]
  rfl
theorem sub5625 (p : Pattern) : d53 (change p 161 (some 160)) = d53 p := by
  change (if p 182 then d32 (change p 161 (some 160)) else d31 (change p 161 (some 160))) = d53 p
  rw [sub5623, sub5622]
  rfl
theorem sub5626 (p : Pattern) : d6 (change p 161 (some 160)) = d6 p := by
  rfl
theorem sub5627 (p : Pattern) : d34 (change p 161 (some 160)) = d34 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d6 (change p 161 (some 160))) = d34 p
  rw [sub5617, sub5626]
  rfl
theorem sub5628 (p : Pattern) : d35 (change p 161 (some 160)) = d35 p := by
  change (if p 246 then d34 (change p 161 (some 160)) else d6 (change p 161 (some 160))) = d35 p
  rw [sub5627, sub5626]
  rfl
theorem sub5629 (p : Pattern) : d36 (change p 161 (some 160)) = d36 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d35 (change p 161 (some 160))) = d36 p
  rw [sub5617, sub5628]
  rfl
theorem sub5630 (p : Pattern) : d78 (change p 161 (some 160)) = d78 p := by
  change (if p 182 then d36 (change p 161 (some 160)) else d35 (change p 161 (some 160))) = d78 p
  rw [sub5629, sub5628]
  rfl
theorem sub5631 (p : Pattern) : d79 (change p 161 (some 160)) = d79 p := by
  change (if p 163 then d78 (change p 161 (some 160)) else d53 (change p 161 (some 160))) = d79 p
  rw [sub5630, sub5625]
  rfl
theorem sub5632 (p : Pattern) : d791 (change p 161 (some 160)) = d791 p := by
  change (if p 162 then d79 (change p 161 (some 160)) else d33 (change p 161 (some 160))) = d791 p
  rw [sub5631, sub5624]
  rfl
theorem sub5633 (p : Pattern) : d792 (change p 161 (some 160)) = d791 p := by
  change d791 (change p 161 (some 160)) = d791 p
  exact sub5632 p
theorem sub5634 (p : Pattern) : d793 (change p 161 (some 160)) = d791 p := by
  change d792 (change p 161 (some 160)) = d791 p
  exact sub5633 p
theorem sub5635 (p : Pattern) : d4 (change p 161 (some 160)) = d4 p := by
  rfl
theorem sub5636 (p : Pattern) : d17 (change p 161 (some 160)) = d17 p := by
  change (if p 247 then d12 (change p 161 (some 160)) else d4 (change p 161 (some 160))) = d17 p
  rw [sub5617, sub5635]
  rfl
theorem sub5637 (p : Pattern) : d18 (change p 161 (some 160)) = d18 p := by
  change (if p 246 then d17 (change p 161 (some 160)) else d4 (change p 161 (some 160))) = d18 p
  rw [sub5636, sub5635]
  rfl
theorem sub5638 (p : Pattern) : d19 (change p 161 (some 160)) = d19 p := by
  change (if p 204 then d12 (change p 161 (some 160)) else d18 (change p 161 (some 160))) = d19 p
  rw [sub5617, sub5637]
  rfl
theorem sub5639 (p : Pattern) : d795 (change p 161 (some 160)) = d795 p := by
  change (if p 182 then d19 (change p 161 (some 160)) else d31 (change p 161 (some 160))) = d795 p
  rw [sub5638, sub5622]
  rfl
end NetHack.Sokoban22Refined85
