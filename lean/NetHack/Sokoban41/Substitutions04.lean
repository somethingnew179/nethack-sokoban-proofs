/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions03
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s600 (pattern : Ten) : d11 (change pattern 10 1) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 1) else d9 (change pattern 10 1)) = d11 pattern
  rw [s594, s599]
  rfl
theorem s601 (pattern : Ten) : d13 (change pattern 10 1) = d13 pattern := by
  change (if pattern.j then d11 (change pattern 10 1) else d0 (change pattern 10 1)) = d13 pattern
  rw [s600, s593]
  rfl
theorem s602 (pattern : Ten) : d14 (change pattern 10 1) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 10 1) else d11 (change pattern 10 1)) = d14 pattern
  rw [s594, s600]
  rfl
theorem s603 (pattern : Ten) : d19 (change pattern 10 1) = d19 pattern := by
  change (if pattern.i then d14 (change pattern 10 1) else d13 (change pattern 10 1)) = d19 pattern
  rw [s602, s601]
  rfl
theorem s604 (pattern : Ten) : d20 (change pattern 10 1) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 10 1) else d14 (change pattern 10 1)) = d20 pattern
  rw [s594, s602]
  rfl
theorem s605 (pattern : Ten) : d24 (change pattern 10 1) = d24 pattern := by
  change (if pattern.h then d20 (change pattern 10 1) else d19 (change pattern 10 1)) = d24 pattern
  rw [s604, s603]
  rfl
theorem s606 (pattern : Ten) : d29 (change pattern 10 1) = d29 pattern := by
  change (if pattern.g then d24 (change pattern 10 1) else d23 (change pattern 10 1)) = d29 pattern
  rw [s605, s598]
  rfl
theorem s607 (pattern : Ten) : d2 (change pattern 10 1) = d2 pattern := by
  rfl
theorem s608 (pattern : Ten) : d15 (change pattern 10 1) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 10 1) else d0 (change pattern 10 1)) = d15 pattern
  rw [s607, s593]
  rfl
theorem s609 (pattern : Ten) : d16 (change pattern 10 1) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 10 1) else d2 (change pattern 10 1)) = d16 pattern
  rw [s594, s607]
  rfl
theorem s610 (pattern : Ten) : d21 (change pattern 10 1) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 10 1) else d15 (change pattern 10 1)) = d21 pattern
  rw [s609, s608]
  rfl
theorem s611 (pattern : Ten) : d22 (change pattern 10 1) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 10 1) else d16 (change pattern 10 1)) = d22 pattern
  rw [s594, s609]
  rfl
theorem s612 (pattern : Ten) : d25 (change pattern 10 1) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 10 1) else d21 (change pattern 10 1)) = d25 pattern
  rw [s611, s610]
  rfl
theorem s613 (pattern : Ten) : d30 (change pattern 10 1) = d30 pattern := by
  change (if pattern.g then d24 (change pattern 10 1) else d25 (change pattern 10 1)) = d30 pattern
  rw [s605, s612]
  rfl
theorem s614 (pattern : Ten) : d33 (change pattern 10 1) = d33 pattern := by
  change (if pattern.c then d30 (change pattern 10 1) else d29 (change pattern 10 1)) = d33 pattern
  rw [s613, s606]
  rfl
theorem s615 (pattern : Ten) : d26 (change pattern 10 1) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 10 1) else d18 (change pattern 10 1)) = d26 pattern
  rw [s594, s597]
  rfl
theorem s616 (pattern : Ten) : d27 (change pattern 10 1) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 10 1) else d20 (change pattern 10 1)) = d27 pattern
  rw [s594, s604]
  rfl
theorem s617 (pattern : Ten) : d31 (change pattern 10 1) = d31 pattern := by
  change (if pattern.g then d27 (change pattern 10 1) else d26 (change pattern 10 1)) = d31 pattern
  rw [s616, s615]
  rfl
theorem s618 (pattern : Ten) : d28 (change pattern 10 1) = d28 pattern := by
  change (if pattern.h then d10 (change pattern 10 1) else d22 (change pattern 10 1)) = d28 pattern
  rw [s594, s611]
  rfl
theorem s619 (pattern : Ten) : d32 (change pattern 10 1) = d32 pattern := by
  change (if pattern.g then d27 (change pattern 10 1) else d28 (change pattern 10 1)) = d32 pattern
  rw [s616, s618]
  rfl
theorem s620 (pattern : Ten) : d34 (change pattern 10 1) = d34 pattern := by
  change (if pattern.c then d32 (change pattern 10 1) else d31 (change pattern 10 1)) = d34 pattern
  rw [s619, s617]
  rfl
theorem s621 (pattern : Ten) : d35 (change pattern 10 1) = d35 pattern := by
  change (if pattern.e then d34 (change pattern 10 1) else d33 (change pattern 10 1)) = d35 pattern
  rw [s620, s614]
  rfl
theorem s622 (pattern : Ten) : d36 (change pattern 10 1) = d36 pattern := by
  change (if pattern.e then d10 (change pattern 10 1) else d34 (change pattern 10 1)) = d36 pattern
  rw [s594, s620]
  rfl
theorem s623 (pattern : Ten) : d37 (change pattern 10 1) = d37 pattern := by
  change (if pattern.d then d36 (change pattern 10 1) else d35 (change pattern 10 1)) = d37 pattern
  rw [s622, s621]
  rfl
theorem s624 (pattern : Ten) : d1 (change pattern 10 1) = d1 pattern := by
  rfl
theorem s625 (pattern : Ten) : d171 (change pattern 10 1) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 10 1) else d0 (change pattern 10 1)) = d171 pattern
  rw [s624, s593]
  rfl
theorem s626 (pattern : Ten) : d173 (change pattern 10 1) = d173 pattern := by
  change (if pattern.j then d10 (change pattern 10 1) else d171 (change pattern 10 1)) = d173 pattern
  rw [s594, s625]
  rfl
theorem s627 (pattern : Ten) : d176 (change pattern 10 1) = d176 pattern := by
  change (if pattern.i then d173 (change pattern 10 1) else d171 (change pattern 10 1)) = d176 pattern
  rw [s626, s625]
  rfl
theorem s628 (pattern : Ten) : d177 (change pattern 10 1) = d177 pattern := by
  change (if pattern.i then d10 (change pattern 10 1) else d173 (change pattern 10 1)) = d177 pattern
  rw [s594, s626]
  rfl
theorem s629 (pattern : Ten) : d180 (change pattern 10 1) = d180 pattern := by
  change (if pattern.h then d177 (change pattern 10 1) else d176 (change pattern 10 1)) = d180 pattern
  rw [s628, s627]
  rfl
theorem s630 (pattern : Ten) : d181 (change pattern 10 1) = d181 pattern := by
  change (if pattern.h then d10 (change pattern 10 1) else d177 (change pattern 10 1)) = d181 pattern
  rw [s594, s628]
  rfl
theorem s631 (pattern : Ten) : d184 (change pattern 10 1) = d184 pattern := by
  change (if pattern.g then d181 (change pattern 10 1) else d180 (change pattern 10 1)) = d184 pattern
  rw [s630, s629]
  rfl
theorem s632 (pattern : Ten) : d3 (change pattern 10 1) = d3 pattern := by
  rfl
theorem s633 (pattern : Ten) : d172 (change pattern 10 1) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 10 1) else d2 (change pattern 10 1)) = d172 pattern
  rw [s632, s607]
  rfl
theorem s634 (pattern : Ten) : d174 (change pattern 10 1) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 10 1) else d171 (change pattern 10 1)) = d174 pattern
  rw [s633, s625]
  rfl
theorem s635 (pattern : Ten) : d175 (change pattern 10 1) = d175 pattern := by
  change (if pattern.j then d10 (change pattern 10 1) else d172 (change pattern 10 1)) = d175 pattern
  rw [s594, s633]
  rfl
theorem s636 (pattern : Ten) : d178 (change pattern 10 1) = d178 pattern := by
  change (if pattern.i then d175 (change pattern 10 1) else d174 (change pattern 10 1)) = d178 pattern
  rw [s635, s634]
  rfl
theorem s637 (pattern : Ten) : d179 (change pattern 10 1) = d179 pattern := by
  change (if pattern.i then d10 (change pattern 10 1) else d175 (change pattern 10 1)) = d179 pattern
  rw [s594, s635]
  rfl
theorem s638 (pattern : Ten) : d182 (change pattern 10 1) = d182 pattern := by
  change (if pattern.h then d179 (change pattern 10 1) else d178 (change pattern 10 1)) = d182 pattern
  rw [s637, s636]
  rfl
theorem s639 (pattern : Ten) : d185 (change pattern 10 1) = d185 pattern := by
  change (if pattern.g then d181 (change pattern 10 1) else d182 (change pattern 10 1)) = d185 pattern
  rw [s630, s638]
  rfl
theorem s640 (pattern : Ten) : d188 (change pattern 10 1) = d188 pattern := by
  change (if pattern.c then d185 (change pattern 10 1) else d184 (change pattern 10 1)) = d188 pattern
  rw [s639, s631]
  rfl
theorem s641 (pattern : Ten) : d186 (change pattern 10 1) = d186 pattern := by
  change (if pattern.g then d10 (change pattern 10 1) else d181 (change pattern 10 1)) = d186 pattern
  rw [s594, s630]
  rfl
theorem s642 (pattern : Ten) : d183 (change pattern 10 1) = d183 pattern := by
  change (if pattern.h then d10 (change pattern 10 1) else d179 (change pattern 10 1)) = d183 pattern
  rw [s594, s637]
  rfl
theorem s643 (pattern : Ten) : d187 (change pattern 10 1) = d187 pattern := by
  change (if pattern.g then d10 (change pattern 10 1) else d183 (change pattern 10 1)) = d187 pattern
  rw [s594, s642]
  rfl
theorem s644 (pattern : Ten) : d189 (change pattern 10 1) = d189 pattern := by
  change (if pattern.c then d187 (change pattern 10 1) else d186 (change pattern 10 1)) = d189 pattern
  rw [s643, s641]
  rfl
theorem s645 (pattern : Ten) : d190 (change pattern 10 1) = d190 pattern := by
  change (if pattern.e then d189 (change pattern 10 1) else d188 (change pattern 10 1)) = d190 pattern
  rw [s644, s640]
  rfl
theorem s646 (pattern : Ten) : d191 (change pattern 10 1) = d191 pattern := by
  change (if pattern.e then d10 (change pattern 10 1) else d189 (change pattern 10 1)) = d191 pattern
  rw [s594, s644]
  rfl
theorem s647 (pattern : Ten) : d192 (change pattern 10 1) = d192 pattern := by
  change (if pattern.d then d191 (change pattern 10 1) else d190 (change pattern 10 1)) = d192 pattern
  rw [s646, s645]
  rfl
theorem s648 (pattern : Ten) : d0 (change pattern 10 9) = d0 pattern := by
  rfl
theorem s649 (pattern : Ten) : d10 (change pattern 10 9) = d10 pattern := by
  rfl
theorem s650 (pattern : Ten) : d12 (change pattern 10 9) = d10 pattern := by
  change d10 (change pattern 10 9) = d10 pattern
  exact s649 pattern
theorem s651 (pattern : Ten) : d17 (change pattern 10 9) = d88 pattern := by
  change (if pattern.i then d12 (change pattern 10 9) else d0 (change pattern 10 9)) = d88 pattern
  rw [s650, s648]
  rfl
theorem s652 (pattern : Ten) : d18 (change pattern 10 9) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 9) else d12 (change pattern 10 9)) = d10 pattern
  rw [s649, s650]
  simp only [ite_self]
theorem s653 (pattern : Ten) : d23 (change pattern 10 9) = d96 pattern := by
  change (if pattern.h then d18 (change pattern 10 9) else d17 (change pattern 10 9)) = d96 pattern
  rw [s652, s651]
  rfl
theorem s654 (pattern : Ten) : d9 (change pattern 10 9) = d9 pattern := by
  rfl
theorem s655 (pattern : Ten) : d11 (change pattern 10 9) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 9) else d9 (change pattern 10 9)) = d11 pattern
  rw [s649, s654]
  rfl
theorem s656 (pattern : Ten) : d13 (change pattern 10 9) = d11 pattern := by
  change d11 (change pattern 10 9) = d11 pattern
  exact s655 pattern
theorem s657 (pattern : Ten) : d14 (change pattern 10 9) = d10 pattern := by
  change d10 (change pattern 10 9) = d10 pattern
  exact s649 pattern
theorem s658 (pattern : Ten) : d19 (change pattern 10 9) = d90 pattern := by
  change (if pattern.i then d14 (change pattern 10 9) else d13 (change pattern 10 9)) = d90 pattern
  rw [s657, s656]
  rfl
theorem s659 (pattern : Ten) : d20 (change pattern 10 9) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 9) else d14 (change pattern 10 9)) = d10 pattern
  rw [s649, s657]
  simp only [ite_self]
theorem s660 (pattern : Ten) : d24 (change pattern 10 9) = d97 pattern := by
  change (if pattern.h then d20 (change pattern 10 9) else d19 (change pattern 10 9)) = d97 pattern
  rw [s659, s658]
  rfl
theorem s661 (pattern : Ten) : d29 (change pattern 10 9) = d101 pattern := by
  change (if pattern.g then d24 (change pattern 10 9) else d23 (change pattern 10 9)) = d101 pattern
  rw [s660, s653]
  rfl
theorem s662 (pattern : Ten) : d2 (change pattern 10 9) = d2 pattern := by
  rfl
theorem s663 (pattern : Ten) : d15 (change pattern 10 9) = d2 pattern := by
  change d2 (change pattern 10 9) = d2 pattern
  exact s662 pattern
theorem s664 (pattern : Ten) : d16 (change pattern 10 9) = d10 pattern := by
  change d10 (change pattern 10 9) = d10 pattern
  exact s649 pattern
theorem s665 (pattern : Ten) : d21 (change pattern 10 9) = d92 pattern := by
  change (if pattern.i then d16 (change pattern 10 9) else d15 (change pattern 10 9)) = d92 pattern
  rw [s664, s663]
  rfl
theorem s666 (pattern : Ten) : d22 (change pattern 10 9) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 9) else d16 (change pattern 10 9)) = d10 pattern
  rw [s649, s664]
  simp only [ite_self]
theorem s667 (pattern : Ten) : d25 (change pattern 10 9) = d98 pattern := by
  change (if pattern.h then d22 (change pattern 10 9) else d21 (change pattern 10 9)) = d98 pattern
  rw [s666, s665]
  rfl
theorem s668 (pattern : Ten) : d30 (change pattern 10 9) = d102 pattern := by
  change (if pattern.g then d24 (change pattern 10 9) else d25 (change pattern 10 9)) = d102 pattern
  rw [s660, s667]
  rfl
theorem s669 (pattern : Ten) : d33 (change pattern 10 9) = d104 pattern := by
  change (if pattern.c then d30 (change pattern 10 9) else d29 (change pattern 10 9)) = d104 pattern
  rw [s668, s661]
  rfl
theorem s670 (pattern : Ten) : d26 (change pattern 10 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 9) else d18 (change pattern 10 9)) = d10 pattern
  rw [s649, s652]
  simp only [ite_self]
theorem s671 (pattern : Ten) : d27 (change pattern 10 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 9) else d20 (change pattern 10 9)) = d10 pattern
  rw [s649, s659]
  simp only [ite_self]
theorem s672 (pattern : Ten) : d31 (change pattern 10 9) = d10 pattern := by
  change (if pattern.g then d27 (change pattern 10 9) else d26 (change pattern 10 9)) = d10 pattern
  rw [s671, s670]
  simp only [ite_self]
theorem s673 (pattern : Ten) : d28 (change pattern 10 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 9) else d22 (change pattern 10 9)) = d10 pattern
  rw [s649, s666]
  simp only [ite_self]
theorem s674 (pattern : Ten) : d32 (change pattern 10 9) = d10 pattern := by
  change (if pattern.g then d27 (change pattern 10 9) else d28 (change pattern 10 9)) = d10 pattern
  rw [s671, s673]
  simp only [ite_self]
theorem s675 (pattern : Ten) : d34 (change pattern 10 9) = d10 pattern := by
  change (if pattern.c then d32 (change pattern 10 9) else d31 (change pattern 10 9)) = d10 pattern
  rw [s674, s672]
  simp only [ite_self]
theorem s676 (pattern : Ten) : d35 (change pattern 10 9) = d106 pattern := by
  change (if pattern.e then d34 (change pattern 10 9) else d33 (change pattern 10 9)) = d106 pattern
  rw [s675, s669]
  rfl
theorem s677 (pattern : Ten) : d36 (change pattern 10 9) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 10 9) else d34 (change pattern 10 9)) = d10 pattern
  rw [s649, s675]
  simp only [ite_self]
theorem s678 (pattern : Ten) : d37 (change pattern 10 9) = d448 pattern := by
  change (if pattern.d then d36 (change pattern 10 9) else d35 (change pattern 10 9)) = d448 pattern
  rw [s677, s676]
  rfl
theorem s679 (pattern : Ten) : d1 (change pattern 10 9) = d1 pattern := by
  rfl
theorem s680 (pattern : Ten) : d171 (change pattern 10 9) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 10 9) else d0 (change pattern 10 9)) = d171 pattern
  rw [s679, s648]
  rfl
theorem s681 (pattern : Ten) : d173 (change pattern 10 9) = d10 pattern := by
  change d10 (change pattern 10 9) = d10 pattern
  exact s649 pattern
theorem s682 (pattern : Ten) : d176 (change pattern 10 9) = d250 pattern := by
  change (if pattern.i then d173 (change pattern 10 9) else d171 (change pattern 10 9)) = d250 pattern
  rw [s681, s680]
  rfl
theorem s683 (pattern : Ten) : d177 (change pattern 10 9) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 9) else d173 (change pattern 10 9)) = d10 pattern
  rw [s649, s681]
  simp only [ite_self]
theorem s684 (pattern : Ten) : d180 (change pattern 10 9) = d254 pattern := by
  change (if pattern.h then d177 (change pattern 10 9) else d176 (change pattern 10 9)) = d254 pattern
  rw [s683, s682]
  rfl
theorem s685 (pattern : Ten) : d181 (change pattern 10 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 9) else d177 (change pattern 10 9)) = d10 pattern
  rw [s649, s683]
  simp only [ite_self]
theorem s686 (pattern : Ten) : d184 (change pattern 10 9) = d259 pattern := by
  change (if pattern.g then d181 (change pattern 10 9) else d180 (change pattern 10 9)) = d259 pattern
  rw [s685, s684]
  rfl
theorem s687 (pattern : Ten) : d3 (change pattern 10 9) = d3 pattern := by
  rfl
theorem s688 (pattern : Ten) : d172 (change pattern 10 9) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 10 9) else d2 (change pattern 10 9)) = d172 pattern
  rw [s687, s662]
  rfl
theorem s689 (pattern : Ten) : d174 (change pattern 10 9) = d172 pattern := by
  change d172 (change pattern 10 9) = d172 pattern
  exact s688 pattern
theorem s690 (pattern : Ten) : d175 (change pattern 10 9) = d10 pattern := by
  change d10 (change pattern 10 9) = d10 pattern
  exact s649 pattern
theorem s691 (pattern : Ten) : d178 (change pattern 10 9) = d252 pattern := by
  change (if pattern.i then d175 (change pattern 10 9) else d174 (change pattern 10 9)) = d252 pattern
  rw [s690, s689]
  rfl
theorem s692 (pattern : Ten) : d179 (change pattern 10 9) = d10 pattern := by
  change (if pattern.i then d10 (change pattern 10 9) else d175 (change pattern 10 9)) = d10 pattern
  rw [s649, s690]
  simp only [ite_self]
theorem s693 (pattern : Ten) : d182 (change pattern 10 9) = d256 pattern := by
  change (if pattern.h then d179 (change pattern 10 9) else d178 (change pattern 10 9)) = d256 pattern
  rw [s692, s691]
  rfl
theorem s694 (pattern : Ten) : d185 (change pattern 10 9) = d260 pattern := by
  change (if pattern.g then d181 (change pattern 10 9) else d182 (change pattern 10 9)) = d260 pattern
  rw [s685, s693]
  rfl
theorem s695 (pattern : Ten) : d188 (change pattern 10 9) = d262 pattern := by
  change (if pattern.c then d185 (change pattern 10 9) else d184 (change pattern 10 9)) = d262 pattern
  rw [s694, s686]
  rfl
theorem s696 (pattern : Ten) : d186 (change pattern 10 9) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 10 9) else d181 (change pattern 10 9)) = d10 pattern
  rw [s649, s685]
  simp only [ite_self]
theorem s697 (pattern : Ten) : d183 (change pattern 10 9) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 10 9) else d179 (change pattern 10 9)) = d10 pattern
  rw [s649, s692]
  simp only [ite_self]
theorem s698 (pattern : Ten) : d187 (change pattern 10 9) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 10 9) else d183 (change pattern 10 9)) = d10 pattern
  rw [s649, s697]
  simp only [ite_self]
theorem s699 (pattern : Ten) : d189 (change pattern 10 9) = d10 pattern := by
  change (if pattern.c then d187 (change pattern 10 9) else d186 (change pattern 10 9)) = d10 pattern
  rw [s698, s696]
  simp only [ite_self]
theorem s700 (pattern : Ten) : d190 (change pattern 10 9) = d264 pattern := by
  change (if pattern.e then d189 (change pattern 10 9) else d188 (change pattern 10 9)) = d264 pattern
  rw [s699, s695]
  rfl
theorem s701 (pattern : Ten) : d191 (change pattern 10 9) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 10 9) else d189 (change pattern 10 9)) = d10 pattern
  rw [s649, s699]
  simp only [ite_self]
theorem s702 (pattern : Ten) : d192 (change pattern 10 9) = d449 pattern := by
  change (if pattern.d then d191 (change pattern 10 9) else d190 (change pattern 10 9)) = d449 pattern
  rw [s701, s700]
  rfl
theorem s703 (pattern : Ten) : d0 (change pattern 9 8) = d0 pattern := by
  rfl
theorem s704 (pattern : Ten) : d87 (change pattern 9 8) = d0 pattern := by
  change d0 (change pattern 9 8) = d0 pattern
  exact s703 pattern
theorem s705 (pattern : Ten) : d10 (change pattern 9 8) = d10 pattern := by
  rfl
theorem s706 (pattern : Ten) : d88 (change pattern 9 8) = d10 pattern := by
  change d10 (change pattern 9 8) = d10 pattern
  exact s705 pattern
theorem s707 (pattern : Ten) : d93 (change pattern 9 8) = d452 pattern := by
  change (if pattern.h then d88 (change pattern 9 8) else d87 (change pattern 9 8)) = d452 pattern
  rw [s706, s704]
  rfl
theorem s708 (pattern : Ten) : d9 (change pattern 9 8) = d9 pattern := by
  rfl
theorem s709 (pattern : Ten) : d11 (change pattern 9 8) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 9 8) else d9 (change pattern 9 8)) = d11 pattern
  rw [s705, s708]
  rfl
theorem s710 (pattern : Ten) : d89 (change pattern 9 8) = d11 pattern := by
  change d11 (change pattern 9 8) = d11 pattern
  exact s709 pattern
theorem s711 (pattern : Ten) : d90 (change pattern 9 8) = d10 pattern := by
  change d10 (change pattern 9 8) = d10 pattern
  exact s705 pattern
theorem s712 (pattern : Ten) : d94 (change pattern 9 8) = d453 pattern := by
  change (if pattern.h then d90 (change pattern 9 8) else d89 (change pattern 9 8)) = d453 pattern
  rw [s711, s710]
  rfl
theorem s713 (pattern : Ten) : d99 (change pattern 9 8) = d454 pattern := by
  change (if pattern.g then d94 (change pattern 9 8) else d93 (change pattern 9 8)) = d454 pattern
  rw [s712, s707]
  rfl
theorem s714 (pattern : Ten) : d2 (change pattern 9 8) = d2 pattern := by
  rfl
theorem s715 (pattern : Ten) : d91 (change pattern 9 8) = d2 pattern := by
  change d2 (change pattern 9 8) = d2 pattern
  exact s714 pattern
theorem s716 (pattern : Ten) : d92 (change pattern 9 8) = d10 pattern := by
  change d10 (change pattern 9 8) = d10 pattern
  exact s705 pattern
theorem s717 (pattern : Ten) : d95 (change pattern 9 8) = d455 pattern := by
  change (if pattern.h then d92 (change pattern 9 8) else d91 (change pattern 9 8)) = d455 pattern
  rw [s716, s715]
  rfl
theorem s718 (pattern : Ten) : d100 (change pattern 9 8) = d456 pattern := by
  change (if pattern.g then d94 (change pattern 9 8) else d95 (change pattern 9 8)) = d456 pattern
  rw [s712, s717]
  rfl
theorem s719 (pattern : Ten) : d103 (change pattern 9 8) = d457 pattern := by
  change (if pattern.c then d100 (change pattern 9 8) else d99 (change pattern 9 8)) = d457 pattern
  rw [s718, s713]
  rfl
theorem s720 (pattern : Ten) : d96 (change pattern 9 8) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 9 8) else d88 (change pattern 9 8)) = d10 pattern
  rw [s705, s706]
  simp only [ite_self]
theorem s721 (pattern : Ten) : d97 (change pattern 9 8) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 9 8) else d90 (change pattern 9 8)) = d10 pattern
  rw [s705, s711]
  simp only [ite_self]
theorem s722 (pattern : Ten) : d101 (change pattern 9 8) = d10 pattern := by
  change (if pattern.g then d97 (change pattern 9 8) else d96 (change pattern 9 8)) = d10 pattern
  rw [s721, s720]
  simp only [ite_self]
theorem s723 (pattern : Ten) : d98 (change pattern 9 8) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 9 8) else d92 (change pattern 9 8)) = d10 pattern
  rw [s705, s716]
  simp only [ite_self]
theorem s724 (pattern : Ten) : d102 (change pattern 9 8) = d10 pattern := by
  change (if pattern.g then d97 (change pattern 9 8) else d98 (change pattern 9 8)) = d10 pattern
  rw [s721, s723]
  simp only [ite_self]
theorem s725 (pattern : Ten) : d104 (change pattern 9 8) = d10 pattern := by
  change (if pattern.c then d102 (change pattern 9 8) else d101 (change pattern 9 8)) = d10 pattern
  rw [s724, s722]
  simp only [ite_self]
theorem s726 (pattern : Ten) : d105 (change pattern 9 8) = d458 pattern := by
  change (if pattern.e then d104 (change pattern 9 8) else d103 (change pattern 9 8)) = d458 pattern
  rw [s725, s719]
  rfl
theorem s727 (pattern : Ten) : d106 (change pattern 9 8) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 9 8) else d104 (change pattern 9 8)) = d10 pattern
  rw [s705, s725]
  simp only [ite_self]
theorem s728 (pattern : Ten) : d107 (change pattern 9 8) = d459 pattern := by
  change (if pattern.d then d106 (change pattern 9 8) else d105 (change pattern 9 8)) = d459 pattern
  rw [s727, s726]
  rfl
theorem s729 (pattern : Ten) : d1 (change pattern 9 8) = d1 pattern := by
  rfl
theorem s730 (pattern : Ten) : d171 (change pattern 9 8) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 9 8) else d0 (change pattern 9 8)) = d171 pattern
  rw [s729, s703]
  rfl
theorem s731 (pattern : Ten) : d249 (change pattern 9 8) = d171 pattern := by
  change d171 (change pattern 9 8) = d171 pattern
  exact s730 pattern
theorem s732 (pattern : Ten) : d250 (change pattern 9 8) = d10 pattern := by
  change d10 (change pattern 9 8) = d10 pattern
  exact s705 pattern
theorem s733 (pattern : Ten) : d253 (change pattern 9 8) = d461 pattern := by
  change (if pattern.h then d250 (change pattern 9 8) else d249 (change pattern 9 8)) = d461 pattern
  rw [s732, s731]
  rfl
theorem s734 (pattern : Ten) : d254 (change pattern 9 8) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 9 8) else d250 (change pattern 9 8)) = d10 pattern
  rw [s705, s732]
  simp only [ite_self]
theorem s735 (pattern : Ten) : d257 (change pattern 9 8) = d462 pattern := by
  change (if pattern.g then d254 (change pattern 9 8) else d253 (change pattern 9 8)) = d462 pattern
  rw [s734, s733]
  rfl
theorem s736 (pattern : Ten) : d3 (change pattern 9 8) = d3 pattern := by
  rfl
theorem s737 (pattern : Ten) : d172 (change pattern 9 8) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 9 8) else d2 (change pattern 9 8)) = d172 pattern
  rw [s736, s714]
  rfl
theorem s738 (pattern : Ten) : d251 (change pattern 9 8) = d172 pattern := by
  change d172 (change pattern 9 8) = d172 pattern
  exact s737 pattern
theorem s739 (pattern : Ten) : d252 (change pattern 9 8) = d10 pattern := by
  change d10 (change pattern 9 8) = d10 pattern
  exact s705 pattern
theorem s740 (pattern : Ten) : d255 (change pattern 9 8) = d463 pattern := by
  change (if pattern.h then d252 (change pattern 9 8) else d251 (change pattern 9 8)) = d463 pattern
  rw [s739, s738]
  rfl
theorem s741 (pattern : Ten) : d258 (change pattern 9 8) = d464 pattern := by
  change (if pattern.g then d254 (change pattern 9 8) else d255 (change pattern 9 8)) = d464 pattern
  rw [s734, s740]
  rfl
theorem s742 (pattern : Ten) : d261 (change pattern 9 8) = d465 pattern := by
  change (if pattern.c then d258 (change pattern 9 8) else d257 (change pattern 9 8)) = d465 pattern
  rw [s741, s735]
  rfl
theorem s743 (pattern : Ten) : d259 (change pattern 9 8) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 9 8) else d254 (change pattern 9 8)) = d10 pattern
  rw [s705, s734]
  simp only [ite_self]
theorem s744 (pattern : Ten) : d256 (change pattern 9 8) = d10 pattern := by
  change (if pattern.h then d10 (change pattern 9 8) else d252 (change pattern 9 8)) = d10 pattern
  rw [s705, s739]
  simp only [ite_self]
theorem s745 (pattern : Ten) : d260 (change pattern 9 8) = d10 pattern := by
  change (if pattern.g then d10 (change pattern 9 8) else d256 (change pattern 9 8)) = d10 pattern
  rw [s705, s744]
  simp only [ite_self]
theorem s746 (pattern : Ten) : d262 (change pattern 9 8) = d10 pattern := by
  change (if pattern.c then d260 (change pattern 9 8) else d259 (change pattern 9 8)) = d10 pattern
  rw [s745, s743]
  simp only [ite_self]
theorem s747 (pattern : Ten) : d263 (change pattern 9 8) = d466 pattern := by
  change (if pattern.e then d262 (change pattern 9 8) else d261 (change pattern 9 8)) = d466 pattern
  rw [s746, s742]
  rfl
theorem s748 (pattern : Ten) : d264 (change pattern 9 8) = d10 pattern := by
  change (if pattern.e then d10 (change pattern 9 8) else d262 (change pattern 9 8)) = d10 pattern
  rw [s705, s746]
  simp only [ite_self]
theorem s749 (pattern : Ten) : d265 (change pattern 9 8) = d467 pattern := by
  change (if pattern.d then d264 (change pattern 9 8) else d263 (change pattern 9 8)) = d467 pattern
  rw [s748, s747]
  rfl
end NetHack.Sokoban41.Diagram
