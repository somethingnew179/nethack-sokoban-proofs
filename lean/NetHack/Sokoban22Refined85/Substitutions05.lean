/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub600 (p : Pattern) : d148 (change p 10000 (some 48)) = d148 p := by
  change (if p 182 then d121 (change p 10000 (some 48)) else d120 (change p 10000 (some 48))) = d148 p
  rw [sub575, sub574]
  rfl
theorem sub601 (p : Pattern) : d149 (change p 10000 (some 48)) = d149 p := by
  change (if p 163 then d148 (change p 10000 (some 48)) else d132 (change p 10000 (some 48))) = d149 p
  rw [sub600, sub586]
  rfl
theorem sub602 (p : Pattern) : d150 (change p 10000 (some 48)) = d150 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d149 (change p 10000 (some 48))) = d150 p
  rw [sub414, sub601]
  rfl
theorem sub603 (p : Pattern) : d151 (change p 10000 (some 48)) = d151 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d150 (change p 10000 (some 48))) = d151 p
  rw [sub414, sub602]
  rfl
theorem sub604 (p : Pattern) : d152 (change p 10000 (some 48)) = d152 p := by
  change (if p 160 then d151 (change p 10000 (some 48)) else d114 (change p 10000 (some 48))) = d152 p
  rw [sub603, sub566]
  rfl
theorem sub605 (p : Pattern) : d153 (change p 10000 (some 48)) = d153 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d148 (change p 10000 (some 48))) = d153 p
  rw [sub414, sub600]
  rfl
theorem sub606 (p : Pattern) : d154 (change p 10000 (some 48)) = d154 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d153 (change p 10000 (some 48))) = d154 p
  rw [sub414, sub605]
  rfl
theorem sub607 (p : Pattern) : d155 (change p 10000 (some 48)) = d155 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d154 (change p 10000 (some 48))) = d155 p
  rw [sub414, sub606]
  rfl
theorem sub608 (p : Pattern) : d221 (change p 10000 (some 48)) = d221 p := by
  change (if p 160 then d155 (change p 10000 (some 48)) else d214 (change p 10000 (some 48))) = d221 p
  rw [sub607, sub591]
  rfl
theorem sub609 (p : Pattern) : d222 (change p 10000 (some 48)) = d222 p := by
  change (if p 141 then d221 (change p 10000 (some 48)) else d152 (change p 10000 (some 48))) = d222 p
  rw [sub608, sub604]
  rfl
theorem sub610 (p : Pattern) : d223 (change p 10000 (some 48)) = d223 p := by
  change (if p 138 then d222 (change p 10000 (some 48)) else d220 (change p 10000 (some 48))) = d223 p
  rw [sub609, sub599]
  rfl
theorem sub611 (p : Pattern) : d159 (change p 10000 (some 48)) = d159 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d112 (change p 10000 (some 48))) = d159 p
  rw [sub414, sub564]
  rfl
theorem sub612 (p : Pattern) : d160 (change p 10000 (some 48)) = d160 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d159 (change p 10000 (some 48))) = d160 p
  rw [sub414, sub611]
  rfl
theorem sub613 (p : Pattern) : d161 (change p 10000 (some 48)) = d161 p := by
  change (if p 160 then d12 (change p 10000 (some 48)) else d160 (change p 10000 (some 48))) = d161 p
  rw [sub414, sub612]
  rfl
theorem sub614 (p : Pattern) : d162 (change p 10000 (some 48)) = d162 p := by
  change (if p 141 then d12 (change p 10000 (some 48)) else d161 (change p 10000 (some 48))) = d162 p
  rw [sub414, sub613]
  rfl
theorem sub615 (p : Pattern) : d224 (change p 10000 (some 48)) = d224 p := by
  change (if p 138 then d162 (change p 10000 (some 48)) else d222 (change p 10000 (some 48))) = d224 p
  rw [sub614, sub609]
  rfl
theorem sub616 (p : Pattern) : d225 (change p 10000 (some 48)) = d225 p := by
  change (if p 116 then d224 (change p 10000 (some 48)) else d223 (change p 10000 (some 48))) = d225 p
  rw [sub615, sub610]
  rfl
theorem sub617 (p : Pattern) : d226 (change p 10000 (some 48)) = d226 p := by
  change (if p 182 then d121 (change p 10000 (some 48)) else d116 (change p 10000 (some 48))) = d226 p
  rw [sub575, sub569]
  rfl
theorem sub618 (p : Pattern) : d227 (change p 10000 (some 48)) = d227 p := by
  change (if p 163 then d226 (change p 10000 (some 48)) else d132 (change p 10000 (some 48))) = d227 p
  rw [sub617, sub586]
  rfl
theorem sub619 (p : Pattern) : d228 (change p 10000 (some 48)) = d228 p := by
  change (if p 162 then d215 (change p 10000 (some 48)) else d227 (change p 10000 (some 48))) = d228 p
  rw [sub594, sub618]
  rfl
theorem sub620 (p : Pattern) : d229 (change p 10000 (some 48)) = d229 p := by
  change (if p 182 then d12 (change p 10000 (some 48)) else d120 (change p 10000 (some 48))) = d229 p
  rw [sub414, sub574]
  rfl
theorem sub621 (p : Pattern) : d230 (change p 10000 (some 48)) = d230 p := by
  change (if p 163 then d12 (change p 10000 (some 48)) else d229 (change p 10000 (some 48))) = d230 p
  rw [sub414, sub620]
  rfl
theorem sub622 (p : Pattern) : d231 (change p 10000 (some 48)) = d231 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d230 (change p 10000 (some 48))) = d231 p
  rw [sub414, sub621]
  rfl
theorem sub623 (p : Pattern) : d232 (change p 10000 (some 48)) = d232 p := by
  change (if p 161 then d231 (change p 10000 (some 48)) else d228 (change p 10000 (some 48))) = d232 p
  rw [sub622, sub619]
  rfl
theorem sub624 (p : Pattern) : d233 (change p 10000 (some 48)) = d233 p := by
  change (if p 160 then d232 (change p 10000 (some 48)) else d114 (change p 10000 (some 48))) = d233 p
  rw [sub623, sub566]
  rfl
theorem sub625 (p : Pattern) : d234 (change p 10000 (some 48)) = d234 p := by
  change (if p 182 then d121 (change p 10000 (some 48)) else d107 (change p 10000 (some 48))) = d234 p
  rw [sub575, sub559]
  rfl
theorem sub626 (p : Pattern) : d235 (change p 10000 (some 48)) = d235 p := by
  change (if p 163 then d125 (change p 10000 (some 48)) else d234 (change p 10000 (some 48))) = d235 p
  rw [sub579, sub625]
  rfl
theorem sub627 (p : Pattern) : d236 (change p 10000 (some 48)) = d236 p := by
  change (if p 162 then d230 (change p 10000 (some 48)) else d235 (change p 10000 (some 48))) = d236 p
  rw [sub621, sub626]
  rfl
theorem sub628 (p : Pattern) : d237 (change p 10000 (some 48)) = d237 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d49 (change p 10000 (some 48))) = d237 p
  rw [sub414, sub456]
  rfl
theorem sub629 (p : Pattern) : d238 (change p 10000 (some 48)) = d238 p := by
  change (if p 161 then d237 (change p 10000 (some 48)) else d236 (change p 10000 (some 48))) = d238 p
  rw [sub628, sub627]
  rfl
theorem sub630 (p : Pattern) : d239 (change p 10000 (some 48)) = d239 p := by
  change (if p 160 then d238 (change p 10000 (some 48)) else d214 (change p 10000 (some 48))) = d239 p
  rw [sub629, sub591]
  rfl
theorem sub631 (p : Pattern) : d240 (change p 10000 (some 48)) = d240 p := by
  change (if p 141 then d239 (change p 10000 (some 48)) else d233 (change p 10000 (some 48))) = d240 p
  rw [sub630, sub624]
  rfl
theorem sub632 (p : Pattern) : d241 (change p 10000 (some 48)) = d241 p := by
  change (if p 163 then d62 (change p 10000 (some 48)) else d132 (change p 10000 (some 48))) = d241 p
  rw [sub470, sub586]
  rfl
theorem sub633 (p : Pattern) : d242 (change p 10000 (some 48)) = d242 p := by
  change (if p 162 then d241 (change p 10000 (some 48)) else d105 (change p 10000 (some 48))) = d242 p
  rw [sub632, sub556]
  rfl
theorem sub634 (p : Pattern) : d136 (change p 10000 (some 48)) = d136 p := by
  change (if p 163 then d62 (change p 10000 (some 48)) else d109 (change p 10000 (some 48))) = d136 p
  rw [sub470, sub561]
  rfl
theorem sub635 (p : Pattern) : d137 (change p 10000 (some 48)) = d137 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d136 (change p 10000 (some 48))) = d137 p
  rw [sub414, sub634]
  rfl
theorem sub636 (p : Pattern) : d243 (change p 10000 (some 48)) = d243 p := by
  change (if p 161 then d137 (change p 10000 (some 48)) else d242 (change p 10000 (some 48))) = d243 p
  rw [sub635, sub633]
  rfl
theorem sub637 (p : Pattern) : d244 (change p 10000 (some 48)) = d244 p := by
  change (if p 160 then d155 (change p 10000 (some 48)) else d243 (change p 10000 (some 48))) = d244 p
  rw [sub607, sub636]
  rfl
theorem sub638 (p : Pattern) : d245 (change p 10000 (some 48)) = d245 p := by
  change (if p 162 then d211 (change p 10000 (some 48)) else d132 (change p 10000 (some 48))) = d245 p
  rw [sub588, sub586]
  rfl
theorem sub639 (p : Pattern) : d246 (change p 10000 (some 48)) = d246 p := by
  change (if p 161 then d154 (change p 10000 (some 48)) else d245 (change p 10000 (some 48))) = d246 p
  rw [sub606, sub638]
  rfl
theorem sub640 (p : Pattern) : d247 (change p 10000 (some 48)) = d247 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d27 (change p 10000 (some 48))) = d247 p
  rw [sub414, sub431]
  rfl
theorem sub641 (p : Pattern) : d248 (change p 10000 (some 48)) = d248 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d247 (change p 10000 (some 48))) = d248 p
  rw [sub414, sub640]
  rfl
theorem sub642 (p : Pattern) : d249 (change p 10000 (some 48)) = d249 p := by
  change (if p 160 then d248 (change p 10000 (some 48)) else d246 (change p 10000 (some 48))) = d249 p
  rw [sub641, sub639]
  rfl
theorem sub643 (p : Pattern) : d250 (change p 10000 (some 48)) = d250 p := by
  change (if p 141 then d249 (change p 10000 (some 48)) else d244 (change p 10000 (some 48))) = d250 p
  rw [sub642, sub637]
  rfl
theorem sub644 (p : Pattern) : d251 (change p 10000 (some 48)) = d251 p := by
  change (if p 138 then d250 (change p 10000 (some 48)) else d240 (change p 10000 (some 48))) = d251 p
  rw [sub643, sub631]
  rfl
theorem sub645 (p : Pattern) : d252 (change p 10000 (some 48)) = d252 p := by
  change (if p 163 then d26 (change p 10000 (some 48)) else d132 (change p 10000 (some 48))) = d252 p
  rw [sub430, sub586]
  rfl
theorem sub646 (p : Pattern) : d253 (change p 10000 (some 48)) = d253 p := by
  change (if p 162 then d252 (change p 10000 (some 48)) else d105 (change p 10000 (some 48))) = d253 p
  rw [sub645, sub556]
  rfl
theorem sub647 (p : Pattern) : d254 (change p 10000 (some 48)) = d254 p := by
  change (if p 163 then d26 (change p 10000 (some 48)) else d109 (change p 10000 (some 48))) = d254 p
  rw [sub430, sub561]
  rfl
theorem sub648 (p : Pattern) : d255 (change p 10000 (some 48)) = d255 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d254 (change p 10000 (some 48))) = d255 p
  rw [sub414, sub647]
  rfl
theorem sub649 (p : Pattern) : d256 (change p 10000 (some 48)) = d256 p := by
  change (if p 161 then d255 (change p 10000 (some 48)) else d253 (change p 10000 (some 48))) = d256 p
  rw [sub648, sub646]
  rfl
theorem sub650 (p : Pattern) : d257 (change p 10000 (some 48)) = d257 p := by
  change (if p 163 then d62 (change p 10000 (some 48)) else d148 (change p 10000 (some 48))) = d257 p
  rw [sub470, sub600]
  rfl
theorem sub651 (p : Pattern) : d258 (change p 10000 (some 48)) = d258 p := by
  change (if p 162 then d12 (change p 10000 (some 48)) else d257 (change p 10000 (some 48))) = d258 p
  rw [sub414, sub650]
  rfl
theorem sub652 (p : Pattern) : d259 (change p 10000 (some 48)) = d259 p := by
  change (if p 161 then d12 (change p 10000 (some 48)) else d258 (change p 10000 (some 48))) = d259 p
  rw [sub414, sub651]
  rfl
theorem sub653 (p : Pattern) : d260 (change p 10000 (some 48)) = d260 p := by
  change (if p 160 then d259 (change p 10000 (some 48)) else d256 (change p 10000 (some 48))) = d260 p
  rw [sub652, sub649]
  rfl
theorem sub654 (p : Pattern) : d261 (change p 10000 (some 48)) = d261 p := by
  change (if p 141 then d249 (change p 10000 (some 48)) else d260 (change p 10000 (some 48))) = d261 p
  rw [sub642, sub653]
  rfl
theorem sub655 (p : Pattern) : d262 (change p 10000 (some 48)) = d262 p := by
  change (if p 138 then d12 (change p 10000 (some 48)) else d261 (change p 10000 (some 48))) = d262 p
  rw [sub414, sub654]
  rfl
theorem sub656 (p : Pattern) : d263 (change p 10000 (some 48)) = d263 p := by
  change (if p 116 then d262 (change p 10000 (some 48)) else d251 (change p 10000 (some 48))) = d263 p
  rw [sub655, sub644]
  rfl
theorem sub657 (p : Pattern) : d264 (change p 10000 (some 48)) = d264 p := by
  change (if p 115 then d263 (change p 10000 (some 48)) else d225 (change p 10000 (some 48))) = d264 p
  rw [sub656, sub616]
  rfl
theorem sub658 (p : Pattern) : d265 (change p 10000 (some 48)) = d265 p := by
  change (if p 71 then d264 (change p 10000 (some 48)) else d101 (change p 10000 (some 48))) = d265 p
  rw [sub657, sub509]
  rfl
theorem sub659 (p : Pattern) : d266 (change p 10000 (some 48)) = d266 p := by
  change (if p 49 then d265 (change p 10000 (some 48)) else d210 (change p 10000 (some 48))) = d266 p
  rw [sub658, sub551]
  rfl
theorem sub660 (p : Pattern) : d267 (change p 10000 (some 48)) = d266 p := by
  change d266 (change p 10000 (some 48)) = d266 p
  exact sub659 p
theorem sub661 (p : Pattern) : d0 (change p 48 (some 49)) = d0 p := by
  rfl
theorem sub662 (p : Pattern) : d12 (change p 48 (some 49)) = d12 p := by
  rfl
theorem sub663 (p : Pattern) : d13 (change p 48 (some 49)) = d13 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d0 (change p 48 (some 49))) = d13 p
  rw [sub662, sub661]
  rfl
theorem sub664 (p : Pattern) : d14 (change p 48 (some 49)) = d14 p := by
  change (if p 246 then d13 (change p 48 (some 49)) else d0 (change p 48 (some 49))) = d14 p
  rw [sub663, sub661]
  rfl
theorem sub665 (p : Pattern) : d15 (change p 48 (some 49)) = d15 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d15 p
  rw [sub662, sub664]
  rfl
theorem sub666 (p : Pattern) : d16 (change p 48 (some 49)) = d16 p := by
  change (if p 182 then d15 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d16 p
  rw [sub665, sub664]
  rfl
theorem sub667 (p : Pattern) : d4 (change p 48 (some 49)) = d4 p := by
  rfl
theorem sub668 (p : Pattern) : d17 (change p 48 (some 49)) = d17 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d4 (change p 48 (some 49))) = d17 p
  rw [sub662, sub667]
  rfl
theorem sub669 (p : Pattern) : d18 (change p 48 (some 49)) = d18 p := by
  change (if p 246 then d17 (change p 48 (some 49)) else d4 (change p 48 (some 49))) = d18 p
  rw [sub668, sub667]
  rfl
theorem sub670 (p : Pattern) : d19 (change p 48 (some 49)) = d19 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d18 (change p 48 (some 49))) = d19 p
  rw [sub662, sub669]
  rfl
theorem sub671 (p : Pattern) : d20 (change p 48 (some 49)) = d20 p := by
  change (if p 182 then d19 (change p 48 (some 49)) else d18 (change p 48 (some 49))) = d20 p
  rw [sub670, sub669]
  rfl
theorem sub672 (p : Pattern) : d21 (change p 48 (some 49)) = d21 p := by
  change (if p 163 then d20 (change p 48 (some 49)) else d16 (change p 48 (some 49))) = d21 p
  rw [sub671, sub666]
  rfl
theorem sub673 (p : Pattern) : d22 (change p 48 (some 49)) = d22 p := by
  change (if p 162 then d21 (change p 48 (some 49)) else d16 (change p 48 (some 49))) = d22 p
  rw [sub672, sub666]
  rfl
theorem sub674 (p : Pattern) : d9 (change p 48 (some 49)) = d9 p := by
  rfl
theorem sub675 (p : Pattern) : d23 (change p 48 (some 49)) = d23 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d9 (change p 48 (some 49))) = d23 p
  rw [sub662, sub674]
  rfl
theorem sub676 (p : Pattern) : d24 (change p 48 (some 49)) = d24 p := by
  change (if p 246 then d23 (change p 48 (some 49)) else d9 (change p 48 (some 49))) = d24 p
  rw [sub675, sub674]
  rfl
theorem sub677 (p : Pattern) : d25 (change p 48 (some 49)) = d25 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d24 (change p 48 (some 49))) = d25 p
  rw [sub662, sub676]
  rfl
theorem sub678 (p : Pattern) : d26 (change p 48 (some 49)) = d26 p := by
  change (if p 182 then d25 (change p 48 (some 49)) else d24 (change p 48 (some 49))) = d26 p
  rw [sub677, sub676]
  rfl
theorem sub679 (p : Pattern) : d27 (change p 48 (some 49)) = d27 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d26 (change p 48 (some 49))) = d27 p
  rw [sub662, sub678]
  rfl
theorem sub680 (p : Pattern) : d28 (change p 48 (some 49)) = d28 p := by
  change (if p 162 then d27 (change p 48 (some 49)) else d21 (change p 48 (some 49))) = d28 p
  rw [sub679, sub672]
  rfl
theorem sub681 (p : Pattern) : d29 (change p 48 (some 49)) = d29 p := by
  change (if p 161 then d28 (change p 48 (some 49)) else d22 (change p 48 (some 49))) = d29 p
  rw [sub680, sub673]
  rfl
theorem sub682 (p : Pattern) : d2 (change p 48 (some 49)) = d2 p := by
  rfl
theorem sub683 (p : Pattern) : d30 (change p 48 (some 49)) = d30 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d2 (change p 48 (some 49))) = d30 p
  rw [sub662, sub682]
  rfl
theorem sub684 (p : Pattern) : d31 (change p 48 (some 49)) = d31 p := by
  change (if p 246 then d30 (change p 48 (some 49)) else d2 (change p 48 (some 49))) = d31 p
  rw [sub683, sub682]
  rfl
theorem sub685 (p : Pattern) : d32 (change p 48 (some 49)) = d32 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d31 (change p 48 (some 49))) = d32 p
  rw [sub662, sub684]
  rfl
theorem sub686 (p : Pattern) : d33 (change p 48 (some 49)) = d33 p := by
  change (if p 182 then d32 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d33 p
  rw [sub685, sub664]
  rfl
theorem sub687 (p : Pattern) : d6 (change p 48 (some 49)) = d6 p := by
  rfl
theorem sub688 (p : Pattern) : d34 (change p 48 (some 49)) = d34 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d6 (change p 48 (some 49))) = d34 p
  rw [sub662, sub687]
  rfl
theorem sub689 (p : Pattern) : d35 (change p 48 (some 49)) = d35 p := by
  change (if p 246 then d34 (change p 48 (some 49)) else d6 (change p 48 (some 49))) = d35 p
  rw [sub688, sub687]
  rfl
theorem sub690 (p : Pattern) : d36 (change p 48 (some 49)) = d36 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d35 (change p 48 (some 49))) = d36 p
  rw [sub662, sub689]
  rfl
theorem sub691 (p : Pattern) : d37 (change p 48 (some 49)) = d37 p := by
  change (if p 182 then d36 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d37 p
  rw [sub690, sub664]
  rfl
theorem sub692 (p : Pattern) : d38 (change p 48 (some 49)) = d38 p := by
  change (if p 163 then d37 (change p 48 (some 49)) else d33 (change p 48 (some 49))) = d38 p
  rw [sub691, sub686]
  rfl
theorem sub693 (p : Pattern) : d11 (change p 48 (some 49)) = d11 p := by
  rfl
theorem sub694 (p : Pattern) : d39 (change p 48 (some 49)) = d39 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d11 (change p 48 (some 49))) = d39 p
  rw [sub662, sub693]
  rfl
theorem sub695 (p : Pattern) : d40 (change p 48 (some 49)) = d40 p := by
  change (if p 246 then d39 (change p 48 (some 49)) else d11 (change p 48 (some 49))) = d40 p
  rw [sub694, sub693]
  rfl
theorem sub696 (p : Pattern) : d41 (change p 48 (some 49)) = d41 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d40 (change p 48 (some 49))) = d41 p
  rw [sub662, sub695]
  rfl
theorem sub697 (p : Pattern) : d42 (change p 48 (some 49)) = d42 p := by
  change (if p 182 then d41 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d42 p
  rw [sub696, sub664]
  rfl
theorem sub698 (p : Pattern) : d43 (change p 48 (some 49)) = d43 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d18 (change p 48 (some 49))) = d43 p
  rw [sub662, sub669]
  rfl
theorem sub699 (p : Pattern) : d44 (change p 48 (some 49)) = d44 p := by
  change (if p 163 then d43 (change p 48 (some 49)) else d42 (change p 48 (some 49))) = d44 p
  rw [sub698, sub697]
  rfl
theorem sub700 (p : Pattern) : d45 (change p 48 (some 49)) = d45 p := by
  change (if p 162 then d44 (change p 48 (some 49)) else d38 (change p 48 (some 49))) = d45 p
  rw [sub699, sub692]
  rfl
theorem sub701 (p : Pattern) : d46 (change p 48 (some 49)) = d46 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d14 (change p 48 (some 49))) = d46 p
  rw [sub662, sub664]
  rfl
theorem sub702 (p : Pattern) : d47 (change p 48 (some 49)) = d47 p := by
  change (if p 163 then d43 (change p 48 (some 49)) else d46 (change p 48 (some 49))) = d47 p
  rw [sub698, sub701]
  rfl
theorem sub703 (p : Pattern) : d48 (change p 48 (some 49)) = d48 p := by
  change (if p 182 then d12 (change p 48 (some 49)) else d24 (change p 48 (some 49))) = d48 p
  rw [sub662, sub676]
  rfl
theorem sub704 (p : Pattern) : d49 (change p 48 (some 49)) = d49 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d48 (change p 48 (some 49))) = d49 p
  rw [sub662, sub703]
  rfl
theorem sub705 (p : Pattern) : d50 (change p 48 (some 49)) = d50 p := by
  change (if p 162 then d49 (change p 48 (some 49)) else d47 (change p 48 (some 49))) = d50 p
  rw [sub704, sub702]
  rfl
theorem sub706 (p : Pattern) : d51 (change p 48 (some 49)) = d51 p := by
  change (if p 161 then d50 (change p 48 (some 49)) else d45 (change p 48 (some 49))) = d51 p
  rw [sub705, sub700]
  rfl
theorem sub707 (p : Pattern) : d52 (change p 48 (some 49)) = d52 p := by
  change (if p 160 then d51 (change p 48 (some 49)) else d29 (change p 48 (some 49))) = d52 p
  rw [sub706, sub681]
  rfl
theorem sub708 (p : Pattern) : d53 (change p 48 (some 49)) = d53 p := by
  change (if p 182 then d32 (change p 48 (some 49)) else d31 (change p 48 (some 49))) = d53 p
  rw [sub685, sub684]
  rfl
theorem sub709 (p : Pattern) : d54 (change p 48 (some 49)) = d54 p := by
  change (if p 163 then d53 (change p 48 (some 49)) else d16 (change p 48 (some 49))) = d54 p
  rw [sub708, sub666]
  rfl
theorem sub710 (p : Pattern) : d55 (change p 48 (some 49)) = d55 p := by
  change (if p 163 then d26 (change p 48 (some 49)) else d20 (change p 48 (some 49))) = d55 p
  rw [sub678, sub671]
  rfl
theorem sub711 (p : Pattern) : d56 (change p 48 (some 49)) = d56 p := by
  change (if p 162 then d55 (change p 48 (some 49)) else d54 (change p 48 (some 49))) = d56 p
  rw [sub710, sub709]
  rfl
theorem sub712 (p : Pattern) : d10 (change p 48 (some 49)) = d10 p := by
  rfl
theorem sub713 (p : Pattern) : d57 (change p 48 (some 49)) = d57 p := by
  change (if p 247 then d12 (change p 48 (some 49)) else d10 (change p 48 (some 49))) = d57 p
  rw [sub662, sub712]
  rfl
theorem sub714 (p : Pattern) : d58 (change p 48 (some 49)) = d58 p := by
  change (if p 246 then d57 (change p 48 (some 49)) else d10 (change p 48 (some 49))) = d58 p
  rw [sub713, sub712]
  rfl
theorem sub715 (p : Pattern) : d59 (change p 48 (some 49)) = d59 p := by
  change (if p 204 then d12 (change p 48 (some 49)) else d58 (change p 48 (some 49))) = d59 p
  rw [sub662, sub714]
  rfl
theorem sub716 (p : Pattern) : d60 (change p 48 (some 49)) = d60 p := by
  change (if p 182 then d59 (change p 48 (some 49)) else d58 (change p 48 (some 49))) = d60 p
  rw [sub715, sub714]
  rfl
theorem sub717 (p : Pattern) : d61 (change p 48 (some 49)) = d61 p := by
  change (if p 163 then d60 (change p 48 (some 49)) else d20 (change p 48 (some 49))) = d61 p
  rw [sub716, sub671]
  rfl
theorem sub718 (p : Pattern) : d62 (change p 48 (some 49)) = d62 p := by
  change (if p 182 then d41 (change p 48 (some 49)) else d40 (change p 48 (some 49))) = d62 p
  rw [sub696, sub695]
  rfl
theorem sub719 (p : Pattern) : d63 (change p 48 (some 49)) = d63 p := by
  change (if p 163 then d12 (change p 48 (some 49)) else d62 (change p 48 (some 49))) = d63 p
  rw [sub662, sub718]
  rfl
end NetHack.Sokoban22Refined85
