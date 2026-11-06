/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions03
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s600 (pattern : Twelve) : d820 (change pattern 3 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d815 (change pattern 3 12)) = d820 pattern
  rw [s568, s599]
  rfl
theorem s601 (pattern : Twelve) : d829 (change pattern 3 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 3 12) else d41 (change pattern 3 12)) = d829 pattern
  rw [s600, s598]
  rfl
theorem s602 (pattern : Twelve) : d844 (change pattern 3 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 3 12) else d59 (change pattern 3 12)) = d844 pattern
  rw [s601, s595]
  rfl
theorem s603 (pattern : Twelve) : d40 (change pattern 3 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d23 (change pattern 3 12)) = d40 pattern
  rw [s568, s577]
  rfl
theorem s604 (pattern : Twelve) : d830 (change pattern 3 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 3 12) else d41 (change pattern 3 12)) = d830 pattern
  rw [s603, s598]
  rfl
theorem s605 (pattern : Twelve) : d13 (change pattern 3 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 3 12) else d4 (change pattern 3 12)) = d13 pattern
  rw [s568, s562]
  rfl
theorem s606 (pattern : Twelve) : d14 (change pattern 3 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 3 12) else d5 (change pattern 3 12)) = d14 pattern
  rw [s568, s564]
  rfl
theorem s607 (pattern : Twelve) : d21 (change pattern 3 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 3 12) else d13 (change pattern 3 12)) = d21 pattern
  rw [s606, s605]
  rfl
theorem s608 (pattern : Twelve) : d821 (change pattern 3 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 3 12) else d25 (change pattern 3 12)) = d821 pattern
  rw [s607, s566]
  rfl
theorem s609 (pattern : Twelve) : d822 (change pattern 3 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d21 (change pattern 3 12)) = d822 pattern
  rw [s568, s607]
  rfl
theorem s610 (pattern : Twelve) : d831 (change pattern 3 12) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 3 12) else d821 (change pattern 3 12)) = d831 pattern
  rw [s609, s608]
  rfl
theorem s611 (pattern : Twelve) : d845 (change pattern 3 12) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 3 12) else d830 (change pattern 3 12)) = d845 pattern
  rw [s610, s604]
  rfl
theorem s612 (pattern : Twelve) : d856 (change pattern 3 12) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 3 12) else d844 (change pattern 3 12)) = d856 pattern
  rw [s611, s602]
  rfl
theorem s613 (pattern : Twelve) : d862 (change pattern 3 12) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 3 12) else d855 (change pattern 3 12)) = d862 pattern
  rw [s612, s592]
  rfl
theorem s614 (pattern : Twelve) : d928 (change pattern 3 12) = d862 pattern := by
  change d862 (change pattern 3 12) = d862 pattern
  exact s613 pattern
theorem s615 (pattern : Twelve) : d933 (change pattern 3 12) = d1891 pattern := by
  change (if pattern.c then d928 (change pattern 3 12) else d927 (change pattern 3 12)) = d1891 pattern
  rw [s614, s587]
  rfl
theorem s616 (pattern : Twelve) : d823 (change pattern 3 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 3 12) else d17 (change pattern 3 12)) = d823 pattern
  rw [s557, s551]
  rfl
theorem s617 (pattern : Twelve) : d846 (change pattern 3 12) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d823 (change pattern 3 12)) = d846 pattern
  rw [s570, s616]
  rfl
theorem s618 (pattern : Twelve) : d857 (change pattern 3 12) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 3 12) else d838 (change pattern 3 12)) = d857 pattern
  rw [s617, s556]
  rfl
theorem s619 (pattern : Twelve) : d45 (change pattern 3 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d1 (change pattern 3 12)) = d45 pattern
  rw [s568, s549]
  rfl
theorem s620 (pattern : Twelve) : d832 (change pattern 3 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 3 12) else d34 (change pattern 3 12)) = d832 pattern
  rw [s619, s578]
  rfl
theorem s621 (pattern : Twelve) : d847 (change pattern 3 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 3 12) else d56 (change pattern 3 12)) = d847 pattern
  rw [s620, s575]
  rfl
theorem s622 (pattern : Twelve) : d833 (change pattern 3 12) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 3 12) else d34 (change pattern 3 12)) = d833 pattern
  rw [s594, s578]
  rfl
theorem s623 (pattern : Twelve) : d848 (change pattern 3 12) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d833 (change pattern 3 12)) = d848 pattern
  rw [s570, s622]
  rfl
theorem s624 (pattern : Twelve) : d858 (change pattern 3 12) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 3 12) else d847 (change pattern 3 12)) = d858 pattern
  rw [s623, s621]
  rfl
theorem s625 (pattern : Twelve) : d864 (change pattern 3 12) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 3 12) else d857 (change pattern 3 12)) = d864 pattern
  rw [s624, s618]
  rfl
theorem s626 (pattern : Twelve) : d929 (change pattern 3 12) = d864 pattern := by
  change d864 (change pattern 3 12) = d864 pattern
  exact s625 pattern
theorem s627 (pattern : Twelve) : d46 (change pattern 3 12) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 3 12) else d1 (change pattern 3 12)) = d46 pattern
  rw [s559, s549]
  rfl
theorem s628 (pattern : Twelve) : d834 (change pattern 3 12) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 3 12) else d34 (change pattern 3 12)) = d834 pattern
  rw [s627, s578]
  rfl
theorem s629 (pattern : Twelve) : d849 (change pattern 3 12) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 3 12) else d30 (change pattern 3 12)) = d849 pattern
  rw [s628, s573]
  rfl
theorem s630 (pattern : Twelve) : d835 (change pattern 3 12) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 3 12) else d34 (change pattern 3 12)) = d835 pattern
  rw [s593, s578]
  rfl
theorem s631 (pattern : Twelve) : d850 (change pattern 3 12) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 3 12) else d835 (change pattern 3 12)) = d850 pattern
  rw [s570, s630]
  rfl
theorem s632 (pattern : Twelve) : d859 (change pattern 3 12) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 3 12) else d849 (change pattern 3 12)) = d859 pattern
  rw [s631, s629]
  rfl
theorem s633 (pattern : Twelve) : d47 (change pattern 3 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d3 (change pattern 3 12)) = d47 pattern
  rw [s568, s559]
  rfl
theorem s634 (pattern : Twelve) : d836 (change pattern 3 12) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 3 12) else d41 (change pattern 3 12)) = d836 pattern
  rw [s633, s598]
  rfl
theorem s635 (pattern : Twelve) : d851 (change pattern 3 12) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 3 12) else d59 (change pattern 3 12)) = d851 pattern
  rw [s634, s595]
  rfl
theorem s636 (pattern : Twelve) : d48 (change pattern 3 12) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d4 (change pattern 3 12)) = d48 pattern
  rw [s568, s562]
  rfl
theorem s637 (pattern : Twelve) : d837 (change pattern 3 12) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 3 12) else d41 (change pattern 3 12)) = d837 pattern
  rw [s636, s598]
  rfl
theorem s638 (pattern : Twelve) : d852 (change pattern 3 12) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 3 12) else d837 (change pattern 3 12)) = d852 pattern
  rw [s610, s637]
  rfl
theorem s639 (pattern : Twelve) : d860 (change pattern 3 12) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 3 12) else d851 (change pattern 3 12)) = d860 pattern
  rw [s638, s635]
  rfl
theorem s640 (pattern : Twelve) : d865 (change pattern 3 12) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 3 12) else d859 (change pattern 3 12)) = d865 pattern
  rw [s639, s632]
  rfl
theorem s641 (pattern : Twelve) : d930 (change pattern 3 12) = d865 pattern := by
  change d865 (change pattern 3 12) = d865 pattern
  exact s640 pattern
theorem s642 (pattern : Twelve) : d934 (change pattern 3 12) = d1892 pattern := by
  change (if pattern.c then d930 (change pattern 3 12) else d929 (change pattern 3 12)) = d1892 pattern
  rw [s641, s626]
  rfl
theorem s643 (pattern : Twelve) : d936 (change pattern 3 12) = d1893 pattern := by
  change (if pattern.g then d934 (change pattern 3 12) else d933 (change pattern 3 12)) = d1893 pattern
  rw [s642, s615]
  rfl
theorem s644 (pattern : Twelve) : d931 (change pattern 3 12) = d861 pattern := by
  change d861 (change pattern 3 12) = d861 pattern
  exact s586 pattern
theorem s645 (pattern : Twelve) : d932 (change pattern 3 12) = d862 pattern := by
  change d862 (change pattern 3 12) = d862 pattern
  exact s613 pattern
theorem s646 (pattern : Twelve) : d935 (change pattern 3 12) = d1891 pattern := by
  change (if pattern.c then d932 (change pattern 3 12) else d931 (change pattern 3 12)) = d1891 pattern
  rw [s645, s644]
  rfl
theorem s647 (pattern : Twelve) : d937 (change pattern 3 12) = d1893 pattern := by
  change (if pattern.g then d934 (change pattern 3 12) else d935 (change pattern 3 12)) = d1893 pattern
  rw [s642, s646]
  rfl
theorem s648 (pattern : Twelve) : d938 (change pattern 3 12) = d1893 pattern := by
  change (if pattern.b then d937 (change pattern 3 12) else d936 (change pattern 3 12)) = d1893 pattern
  rw [s647, s643]
  simp only [ite_self]
theorem s649 (pattern : Twelve) : d939 (change pattern 3 12) = d1893 pattern := by
  change (if pattern.a then d937 (change pattern 3 12) else d938 (change pattern 3 12)) = d1893 pattern
  rw [s647, s648]
  simp only [ite_self]
theorem s650 (pattern : Twelve) : d8 (change pattern 3 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 3 12) else d1 (change pattern 3 12)) = d8 pattern
  rw [s557, s549]
  rfl
theorem s651 (pattern : Twelve) : d1275 (change pattern 3 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 3 12) else d7 (change pattern 3 12)) = d1275 pattern
  rw [s650, s550]
  rfl
theorem s652 (pattern : Twelve) : d872 (change pattern 3 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 3 12) else d1 (change pattern 3 12)) = d872 pattern
  rw [s650, s549]
  rfl
theorem s653 (pattern : Twelve) : d1278 (change pattern 3 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 3 12) else d1275 (change pattern 3 12)) = d1278 pattern
  rw [s652, s651]
  rfl
theorem s654 (pattern : Twelve) : d1284 (change pattern 3 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 3 12) else d1278 (change pattern 3 12)) = d1284 pattern
  rw [s652, s653]
  rfl
theorem s655 (pattern : Twelve) : d1293 (change pattern 3 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 3 12) else d17 (change pattern 3 12)) = d1293 pattern
  rw [s654, s551]
  rfl
theorem s656 (pattern : Twelve) : d1294 (change pattern 3 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d19 (change pattern 3 12)) = d1294 pattern
  rw [s568, s561]
  rfl
theorem s657 (pattern : Twelve) : d1305 (change pattern 3 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 3 12) else d1293 (change pattern 3 12)) = d1305 pattern
  rw [s656, s655]
  rfl
theorem s658 (pattern : Twelve) : d117 (change pattern 3 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 3 12) else d3 (change pattern 3 12)) = d117 pattern
  rw [s562, s559]
  rfl
theorem s659 (pattern : Twelve) : d1276 (change pattern 3 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 3 12) else d9 (change pattern 3 12)) = d1276 pattern
  rw [s658, s576]
  rfl
theorem s660 (pattern : Twelve) : d1279 (change pattern 3 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 3 12) else d1275 (change pattern 3 12)) = d1279 pattern
  rw [s659, s651]
  rfl
theorem s661 (pattern : Twelve) : d1280 (change pattern 3 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d872 (change pattern 3 12)) = d1280 pattern
  rw [s568, s652]
  rfl
theorem s662 (pattern : Twelve) : d1285 (change pattern 3 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 3 12) else d1279 (change pattern 3 12)) = d1285 pattern
  rw [s661, s660]
  rfl
theorem s663 (pattern : Twelve) : d1295 (change pattern 3 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 3 12) else d827 (change pattern 3 12)) = d1295 pattern
  rw [s662, s583]
  rfl
theorem s664 (pattern : Twelve) : d29 (change pattern 3 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d19 (change pattern 3 12)) = d29 pattern
  rw [s568, s561]
  rfl
theorem s665 (pattern : Twelve) : d1286 (change pattern 3 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 3 12) else d817 (change pattern 3 12)) = d1286 pattern
  rw [s664, s567]
  rfl
theorem s666 (pattern : Twelve) : d1296 (change pattern 3 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1286 (change pattern 3 12)) = d1296 pattern
  rw [s568, s665]
  rfl
theorem s667 (pattern : Twelve) : d1306 (change pattern 3 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 3 12) else d1295 (change pattern 3 12)) = d1306 pattern
  rw [s666, s663]
  rfl
theorem s668 (pattern : Twelve) : d1313 (change pattern 3 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 3 12) else d1305 (change pattern 3 12)) = d1313 pattern
  rw [s667, s657]
  rfl
theorem s669 (pattern : Twelve) : d1368 (change pattern 3 12) = d1313 pattern := by
  change d1313 (change pattern 3 12) = d1313 pattern
  exact s668 pattern
theorem s670 (pattern : Twelve) : d119 (change pattern 3 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 3 12) else d3 (change pattern 3 12)) = d119 pattern
  rw [s658, s559]
  rfl
theorem s671 (pattern : Twelve) : d1281 (change pattern 3 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 3 12) else d872 (change pattern 3 12)) = d1281 pattern
  rw [s670, s652]
  rfl
theorem s672 (pattern : Twelve) : d1287 (change pattern 3 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 3 12) else d1279 (change pattern 3 12)) = d1287 pattern
  rw [s671, s660]
  rfl
theorem s673 (pattern : Twelve) : d1297 (change pattern 3 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 3 12) else d34 (change pattern 3 12)) = d1297 pattern
  rw [s672, s578]
  rfl
theorem s674 (pattern : Twelve) : d1298 (change pattern 3 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d817 (change pattern 3 12)) = d1298 pattern
  rw [s568, s567]
  rfl
theorem s675 (pattern : Twelve) : d1307 (change pattern 3 12) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 3 12) else d1297 (change pattern 3 12)) = d1307 pattern
  rw [s674, s673]
  rfl
theorem s676 (pattern : Twelve) : d1277 (change pattern 3 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 3 12) else d15 (change pattern 3 12)) = d1277 pattern
  rw [s606, s596]
  rfl
theorem s677 (pattern : Twelve) : d1282 (change pattern 3 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 3 12) else d1276 (change pattern 3 12)) = d1282 pattern
  rw [s676, s659]
  rfl
theorem s678 (pattern : Twelve) : d125 (change pattern 3 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d119 (change pattern 3 12)) = d125 pattern
  rw [s568, s670]
  rfl
theorem s679 (pattern : Twelve) : d1288 (change pattern 3 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 3 12) else d1282 (change pattern 3 12)) = d1288 pattern
  rw [s678, s677]
  rfl
theorem s680 (pattern : Twelve) : d1299 (change pattern 3 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 3 12) else d830 (change pattern 3 12)) = d1299 pattern
  rw [s679, s604]
  rfl
theorem s681 (pattern : Twelve) : d1289 (change pattern 3 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 3 12) else d821 (change pattern 3 12)) = d1289 pattern
  rw [s569, s608]
  rfl
theorem s682 (pattern : Twelve) : d1300 (change pattern 3 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1289 (change pattern 3 12)) = d1300 pattern
  rw [s568, s681]
  rfl
theorem s683 (pattern : Twelve) : d1308 (change pattern 3 12) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 3 12) else d1299 (change pattern 3 12)) = d1308 pattern
  rw [s682, s680]
  rfl
theorem s684 (pattern : Twelve) : d1314 (change pattern 3 12) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 3 12) else d1307 (change pattern 3 12)) = d1314 pattern
  rw [s683, s675]
  rfl
theorem s685 (pattern : Twelve) : d1369 (change pattern 3 12) = d1314 pattern := by
  change d1314 (change pattern 3 12) = d1314 pattern
  exact s684 pattern
theorem s686 (pattern : Twelve) : d1373 (change pattern 3 12) = d1894 pattern := by
  change (if pattern.c then d1369 (change pattern 3 12) else d1368 (change pattern 3 12)) = d1894 pattern
  rw [s685, s669]
  rfl
theorem s687 (pattern : Twelve) : d1283 (change pattern 3 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 3 12) else d19 (change pattern 3 12)) = d1283 pattern
  rw [s577, s561]
  rfl
theorem s688 (pattern : Twelve) : d1301 (change pattern 3 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1283 (change pattern 3 12)) = d1301 pattern
  rw [s568, s687]
  rfl
theorem s689 (pattern : Twelve) : d1309 (change pattern 3 12) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 3 12) else d1293 (change pattern 3 12)) = d1309 pattern
  rw [s688, s655]
  rfl
theorem s690 (pattern : Twelve) : d1290 (change pattern 3 12) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 3 12) else d817 (change pattern 3 12)) = d1290 pattern
  rw [s603, s567]
  rfl
theorem s691 (pattern : Twelve) : d1302 (change pattern 3 12) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1290 (change pattern 3 12)) = d1302 pattern
  rw [s568, s690]
  rfl
theorem s692 (pattern : Twelve) : d1310 (change pattern 3 12) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 3 12) else d1295 (change pattern 3 12)) = d1310 pattern
  rw [s691, s663]
  rfl
theorem s693 (pattern : Twelve) : d1316 (change pattern 3 12) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 3 12) else d1309 (change pattern 3 12)) = d1316 pattern
  rw [s692, s689]
  rfl
theorem s694 (pattern : Twelve) : d1370 (change pattern 3 12) = d1316 pattern := by
  change d1316 (change pattern 3 12) = d1316 pattern
  exact s693 pattern
theorem s695 (pattern : Twelve) : d1291 (change pattern 3 12) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 3 12) else d817 (change pattern 3 12)) = d1291 pattern
  rw [s598, s567]
  rfl
theorem s696 (pattern : Twelve) : d1303 (change pattern 3 12) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1291 (change pattern 3 12)) = d1303 pattern
  rw [s568, s695]
  rfl
theorem s697 (pattern : Twelve) : d1311 (change pattern 3 12) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 3 12) else d1297 (change pattern 3 12)) = d1311 pattern
  rw [s696, s673]
  rfl
theorem s698 (pattern : Twelve) : d49 (change pattern 3 12) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d24 (change pattern 3 12)) = d49 pattern
  rw [s568, s597]
  rfl
theorem s699 (pattern : Twelve) : d1292 (change pattern 3 12) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 3 12) else d821 (change pattern 3 12)) = d1292 pattern
  rw [s698, s608]
  rfl
theorem s700 (pattern : Twelve) : d1304 (change pattern 3 12) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d1292 (change pattern 3 12)) = d1304 pattern
  rw [s568, s699]
  rfl
theorem s701 (pattern : Twelve) : d1312 (change pattern 3 12) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 3 12) else d1299 (change pattern 3 12)) = d1312 pattern
  rw [s700, s680]
  rfl
theorem s702 (pattern : Twelve) : d1317 (change pattern 3 12) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 3 12) else d1311 (change pattern 3 12)) = d1317 pattern
  rw [s701, s697]
  rfl
theorem s703 (pattern : Twelve) : d1371 (change pattern 3 12) = d1317 pattern := by
  change d1317 (change pattern 3 12) = d1317 pattern
  exact s702 pattern
theorem s704 (pattern : Twelve) : d1374 (change pattern 3 12) = d1895 pattern := by
  change (if pattern.c then d1371 (change pattern 3 12) else d1370 (change pattern 3 12)) = d1895 pattern
  rw [s703, s694]
  rfl
theorem s705 (pattern : Twelve) : d1376 (change pattern 3 12) = d1896 pattern := by
  change (if pattern.g then d1374 (change pattern 3 12) else d1373 (change pattern 3 12)) = d1896 pattern
  rw [s704, s686]
  rfl
theorem s706 (pattern : Twelve) : d1372 (change pattern 3 12) = d1313 pattern := by
  change d1313 (change pattern 3 12) = d1313 pattern
  exact s668 pattern
theorem s707 (pattern : Twelve) : d1375 (change pattern 3 12) = d1894 pattern := by
  change (if pattern.c then d1369 (change pattern 3 12) else d1372 (change pattern 3 12)) = d1894 pattern
  rw [s685, s706]
  rfl
theorem s708 (pattern : Twelve) : d1377 (change pattern 3 12) = d1896 pattern := by
  change (if pattern.g then d1374 (change pattern 3 12) else d1375 (change pattern 3 12)) = d1896 pattern
  rw [s704, s707]
  rfl
theorem s709 (pattern : Twelve) : d1378 (change pattern 3 12) = d1896 pattern := by
  change (if pattern.b then d1377 (change pattern 3 12) else d1376 (change pattern 3 12)) = d1896 pattern
  rw [s708, s705]
  simp only [ite_self]
theorem s710 (pattern : Twelve) : d1379 (change pattern 3 12) = d1896 pattern := by
  change (if pattern.a then d1377 (change pattern 3 12) else d1378 (change pattern 3 12)) = d1896 pattern
  rw [s708, s709]
  simp only [ite_self]
theorem s711 (pattern : Twelve) : d1324 (change pattern 3 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 3 12) else d11 (change pattern 3 12)) = d1324 pattern
  rw [s563, s560]
  rfl
theorem s712 (pattern : Twelve) : d1649 (change pattern 3 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 3 12) else d19 (change pattern 3 12)) = d1649 pattern
  rw [s711, s561]
  rfl
theorem s713 (pattern : Twelve) : d1650 (change pattern 3 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d25 (change pattern 3 12)) = d1650 pattern
  rw [s568, s566]
  rfl
theorem s714 (pattern : Twelve) : d1656 (change pattern 3 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 3 12) else d1649 (change pattern 3 12)) = d1656 pattern
  rw [s713, s712]
  rfl
theorem s715 (pattern : Twelve) : d20 (change pattern 3 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 3 12) else d12 (change pattern 3 12)) = d20 pattern
  rw [s605, s565]
  rfl
theorem s716 (pattern : Twelve) : d1644 (change pattern 3 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 3 12) else d1324 (change pattern 3 12)) = d1644 pattern
  rw [s715, s711]
  rfl
theorem s717 (pattern : Twelve) : d1645 (change pattern 3 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d1324 (change pattern 3 12)) = d1645 pattern
  rw [s568, s711]
  rfl
theorem s718 (pattern : Twelve) : d1647 (change pattern 3 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 3 12) else d1644 (change pattern 3 12)) = d1647 pattern
  rw [s717, s716]
  rfl
theorem s719 (pattern : Twelve) : d1651 (change pattern 3 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 3 12) else d1286 (change pattern 3 12)) = d1651 pattern
  rw [s718, s665]
  rfl
theorem s720 (pattern : Twelve) : d1657 (change pattern 3 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 3 12) else d1651 (change pattern 3 12)) = d1657 pattern
  rw [s682, s719]
  rfl
theorem s721 (pattern : Twelve) : d1660 (change pattern 3 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 3 12) else d1656 (change pattern 3 12)) = d1660 pattern
  rw [s720, s714]
  rfl
theorem s722 (pattern : Twelve) : d1686 (change pattern 3 12) = d1660 pattern := by
  change d1660 (change pattern 3 12) = d1660 pattern
  exact s721 pattern
theorem s723 (pattern : Twelve) : d1652 (change pattern 3 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 3 12) else d817 (change pattern 3 12)) = d1652 pattern
  rw [s716, s567]
  rfl
theorem s724 (pattern : Twelve) : d1653 (change pattern 3 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d821 (change pattern 3 12)) = d1653 pattern
  rw [s568, s608]
  rfl
theorem s725 (pattern : Twelve) : d1658 (change pattern 3 12) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 3 12) else d1652 (change pattern 3 12)) = d1658 pattern
  rw [s724, s723]
  rfl
theorem s726 (pattern : Twelve) : d22 (change pattern 3 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 3 12) else d14 (change pattern 3 12)) = d22 pattern
  rw [s568, s606]
  rfl
theorem s727 (pattern : Twelve) : d1646 (change pattern 3 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 3 12) else d20 (change pattern 3 12)) = d1646 pattern
  rw [s726, s715]
  rfl
theorem s728 (pattern : Twelve) : d128 (change pattern 3 12) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 3 12) else d20 (change pattern 3 12)) = d128 pattern
  rw [s568, s715]
  rfl
theorem s729 (pattern : Twelve) : d1648 (change pattern 3 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 3 12) else d1646 (change pattern 3 12)) = d1648 pattern
  rw [s728, s727]
  rfl
theorem s730 (pattern : Twelve) : d1654 (change pattern 3 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 3 12) else d1289 (change pattern 3 12)) = d1654 pattern
  rw [s729, s681]
  rfl
theorem s731 (pattern : Twelve) : d1655 (change pattern 3 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 3 12) else d822 (change pattern 3 12)) = d1655 pattern
  rw [s568, s609]
  rfl
theorem s732 (pattern : Twelve) : d1659 (change pattern 3 12) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 3 12) else d1654 (change pattern 3 12)) = d1659 pattern
  rw [s731, s730]
  rfl
theorem s733 (pattern : Twelve) : d1661 (change pattern 3 12) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 3 12) else d1658 (change pattern 3 12)) = d1661 pattern
  rw [s732, s725]
  rfl
theorem s734 (pattern : Twelve) : d1687 (change pattern 3 12) = d1661 pattern := by
  change d1661 (change pattern 3 12) = d1661 pattern
  exact s733 pattern
theorem s735 (pattern : Twelve) : d1688 (change pattern 3 12) = d1897 pattern := by
  change (if pattern.c then d1687 (change pattern 3 12) else d1686 (change pattern 3 12)) = d1897 pattern
  rw [s734, s722]
  rfl
theorem s736 (pattern : Twelve) : d0 (change pattern 3 2) = d0 pattern := by
  rfl
theorem s737 (pattern : Twelve) : d2 (change pattern 3 2) = d2 pattern := by
  rfl
theorem s738 (pattern : Twelve) : d30 (change pattern 3 2) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 3 2) else d0 (change pattern 3 2)) = d30 pattern
  rw [s737, s736]
  rfl
theorem s739 (pattern : Twelve) : d1 (change pattern 3 2) = d1 pattern := by
  rfl
theorem s740 (pattern : Twelve) : d7 (change pattern 3 2) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 3 2) else d0 (change pattern 3 2)) = d7 pattern
  rw [s739, s736]
  rfl
theorem s741 (pattern : Twelve) : d17 (change pattern 3 2) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 3 2) else d0 (change pattern 3 2)) = d17 pattern
  rw [s740, s736]
  rfl
theorem s742 (pattern : Twelve) : d3 (change pattern 3 2) = d3 pattern := by
  rfl
theorem s743 (pattern : Twelve) : d37 (change pattern 3 2) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 3 2) else d17 (change pattern 3 2)) = d37 pattern
  rw [s742, s741]
  rfl
theorem s744 (pattern : Twelve) : d58 (change pattern 3 2) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 3 2) else d30 (change pattern 3 2)) = d58 pattern
  rw [s743, s738]
  rfl
theorem s745 (pattern : Twelve) : d79 (change pattern 3 2) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 3 2) else d30 (change pattern 3 2)) = d79 pattern
  rw [s744, s738]
  rfl
theorem s746 (pattern : Twelve) : d9 (change pattern 3 2) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 3 2) else d2 (change pattern 3 2)) = d9 pattern
  rw [s742, s737]
  rfl
theorem s747 (pattern : Twelve) : d23 (change pattern 3 2) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 3 2) else d2 (change pattern 3 2)) = d23 pattern
  rw [s746, s737]
  rfl
theorem s748 (pattern : Twelve) : d34 (change pattern 3 2) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 3 2) else d17 (change pattern 3 2)) = d34 pattern
  rw [s747, s741]
  rfl
theorem s749 (pattern : Twelve) : d10 (change pattern 3 2) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 3 2) else d0 (change pattern 3 2)) = d10 pattern
  rw [s737, s736]
  rfl
end NetHack.Sokoban21.Diagram
