/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Diagram
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s0 (pattern : Twelve) : d0 (change pattern 12 12) = d0 pattern := by
  rfl
theorem s1 (pattern : Twelve) : d1 (change pattern 12 12) = d1 pattern := by
  rfl
theorem s2 (pattern : Twelve) : d7 (change pattern 12 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 12) else d0 (change pattern 12 12)) = d7 pattern
  rw [s1, s0]
  rfl
theorem s3 (pattern : Twelve) : d17 (change pattern 12 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 12) else d0 (change pattern 12 12)) = d17 pattern
  rw [s2, s0]
  rfl
theorem s4 (pattern : Twelve) : d27 (change pattern 12 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 12) else d17 (change pattern 12 12)) = d27 pattern
  rw [s1, s3]
  rfl
theorem s5 (pattern : Twelve) : d814 (change pattern 12 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 12) else d7 (change pattern 12 12)) = d814 pattern
  rw [s1, s2]
  rfl
theorem s6 (pattern : Twelve) : d816 (change pattern 12 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 12) else d814 (change pattern 12 12)) = d816 pattern
  rw [s1, s5]
  rfl
theorem s7 (pattern : Twelve) : d824 (change pattern 12 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 12) else d27 (change pattern 12 12)) = d824 pattern
  rw [s6, s4]
  rfl
theorem s8 (pattern : Twelve) : d838 (change pattern 12 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 12 12) else d0 (change pattern 12 12)) = d838 pattern
  rw [s7, s0]
  rfl
theorem s9 (pattern : Twelve) : d2 (change pattern 12 12) = d2 pattern := by
  rfl
theorem s10 (pattern : Twelve) : d10 (change pattern 12 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 12) else d0 (change pattern 12 12)) = d10 pattern
  rw [s9, s0]
  rfl
theorem s11 (pattern : Twelve) : d3 (change pattern 12 12) = d3 pattern := by
  rfl
theorem s12 (pattern : Twelve) : d11 (change pattern 12 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 12) else d1 (change pattern 12 12)) = d11 pattern
  rw [s11, s1]
  rfl
theorem s13 (pattern : Twelve) : d19 (change pattern 12 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 12) else d10 (change pattern 12 12)) = d19 pattern
  rw [s12, s10]
  rfl
theorem s14 (pattern : Twelve) : d4 (change pattern 12 12) = d4 pattern := by
  rfl
theorem s15 (pattern : Twelve) : d16 (change pattern 12 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 12) else d2 (change pattern 12 12)) = d16 pattern
  rw [s14, s9]
  rfl
theorem s16 (pattern : Twelve) : d5 (change pattern 12 12) = d5 pattern := by
  rfl
theorem s17 (pattern : Twelve) : d12 (change pattern 12 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 12) else d3 (change pattern 12 12)) = d12 pattern
  rw [s16, s11]
  rfl
theorem s18 (pattern : Twelve) : d25 (change pattern 12 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 12) else d16 (change pattern 12 12)) = d25 pattern
  rw [s17, s15]
  rfl
theorem s19 (pattern : Twelve) : d817 (change pattern 12 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 12) else d19 (change pattern 12 12)) = d817 pattern
  rw [s18, s13]
  rfl
theorem s20 (pattern : Twelve) : d6 (change pattern 12 12) = d6 pattern := by
  rfl
theorem s21 (pattern : Twelve) : d42 (change pattern 12 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d25 (change pattern 12 12)) = d42 pattern
  rw [s20, s18]
  rfl
theorem s22 (pattern : Twelve) : d825 (change pattern 12 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 12) else d817 (change pattern 12 12)) = d825 pattern
  rw [s21, s19]
  rfl
theorem s23 (pattern : Twelve) : d839 (change pattern 12 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d17 (change pattern 12 12)) = d839 pattern
  rw [s22, s3]
  rfl
theorem s24 (pattern : Twelve) : d853 (change pattern 12 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 12 12) else d838 (change pattern 12 12)) = d853 pattern
  rw [s23, s8]
  rfl
theorem s25 (pattern : Twelve) : d30 (change pattern 12 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 12) else d0 (change pattern 12 12)) = d30 pattern
  rw [s9, s0]
  rfl
theorem s26 (pattern : Twelve) : d35 (change pattern 12 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d0 (change pattern 12 12)) = d35 pattern
  rw [s20, s0]
  rfl
theorem s27 (pattern : Twelve) : d56 (change pattern 12 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 12) else d30 (change pattern 12 12)) = d56 pattern
  rw [s26, s25]
  rfl
theorem s28 (pattern : Twelve) : d9 (change pattern 12 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 12) else d2 (change pattern 12 12)) = d9 pattern
  rw [s11, s9]
  rfl
theorem s29 (pattern : Twelve) : d23 (change pattern 12 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 12) else d2 (change pattern 12 12)) = d23 pattern
  rw [s28, s9]
  rfl
theorem s30 (pattern : Twelve) : d34 (change pattern 12 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 12) else d17 (change pattern 12 12)) = d34 pattern
  rw [s29, s3]
  rfl
theorem s31 (pattern : Twelve) : d818 (change pattern 12 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d814 (change pattern 12 12)) = d818 pattern
  rw [s20, s5]
  rfl
theorem s32 (pattern : Twelve) : d826 (change pattern 12 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 12 12) else d34 (change pattern 12 12)) = d826 pattern
  rw [s31, s30]
  rfl
theorem s33 (pattern : Twelve) : d840 (change pattern 12 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 12 12) else d56 (change pattern 12 12)) = d840 pattern
  rw [s32, s27]
  rfl
theorem s34 (pattern : Twelve) : d36 (change pattern 12 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d17 (change pattern 12 12)) = d36 pattern
  rw [s20, s3]
  rfl
theorem s35 (pattern : Twelve) : d827 (change pattern 12 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 12 12) else d34 (change pattern 12 12)) = d827 pattern
  rw [s34, s30]
  rfl
theorem s36 (pattern : Twelve) : d841 (change pattern 12 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d827 (change pattern 12 12)) = d841 pattern
  rw [s22, s35]
  rfl
theorem s37 (pattern : Twelve) : d854 (change pattern 12 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 12 12) else d840 (change pattern 12 12)) = d854 pattern
  rw [s36, s33]
  rfl
theorem s38 (pattern : Twelve) : d861 (change pattern 12 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 12 12) else d853 (change pattern 12 12)) = d861 pattern
  rw [s37, s24]
  rfl
theorem s39 (pattern : Twelve) : d819 (change pattern 12 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d814 (change pattern 12 12)) = d819 pattern
  rw [s11, s5]
  rfl
theorem s40 (pattern : Twelve) : d828 (change pattern 12 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 12 12) else d34 (change pattern 12 12)) = d828 pattern
  rw [s39, s30]
  rfl
theorem s41 (pattern : Twelve) : d842 (change pattern 12 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 12 12) else d30 (change pattern 12 12)) = d842 pattern
  rw [s40, s25]
  rfl
theorem s42 (pattern : Twelve) : d843 (change pattern 12 12) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d34 (change pattern 12 12)) = d843 pattern
  rw [s22, s30]
  rfl
theorem s43 (pattern : Twelve) : d855 (change pattern 12 12) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 12 12) else d842 (change pattern 12 12)) = d855 pattern
  rw [s42, s41]
  rfl
theorem s44 (pattern : Twelve) : d38 (change pattern 12 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 12) else d2 (change pattern 12 12)) = d38 pattern
  rw [s14, s9]
  rfl
theorem s45 (pattern : Twelve) : d39 (change pattern 12 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d2 (change pattern 12 12)) = d39 pattern
  rw [s20, s9]
  rfl
theorem s46 (pattern : Twelve) : d59 (change pattern 12 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 12 12) else d38 (change pattern 12 12)) = d59 pattern
  rw [s45, s44]
  rfl
theorem s47 (pattern : Twelve) : d15 (change pattern 12 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 12) else d4 (change pattern 12 12)) = d15 pattern
  rw [s16, s14]
  rfl
theorem s48 (pattern : Twelve) : d24 (change pattern 12 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 12) else d4 (change pattern 12 12)) = d24 pattern
  rw [s47, s14]
  rfl
theorem s49 (pattern : Twelve) : d41 (change pattern 12 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 12 12) else d23 (change pattern 12 12)) = d41 pattern
  rw [s48, s29]
  rfl
theorem s50 (pattern : Twelve) : d815 (change pattern 12 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 12) else d9 (change pattern 12 12)) = d815 pattern
  rw [s11, s28]
  rfl
theorem s51 (pattern : Twelve) : d820 (change pattern 12 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d815 (change pattern 12 12)) = d820 pattern
  rw [s20, s50]
  rfl
theorem s52 (pattern : Twelve) : d829 (change pattern 12 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 12 12) else d41 (change pattern 12 12)) = d829 pattern
  rw [s51, s49]
  rfl
theorem s53 (pattern : Twelve) : d844 (change pattern 12 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 12 12) else d59 (change pattern 12 12)) = d844 pattern
  rw [s52, s46]
  rfl
theorem s54 (pattern : Twelve) : d40 (change pattern 12 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d23 (change pattern 12 12)) = d40 pattern
  rw [s20, s29]
  rfl
theorem s55 (pattern : Twelve) : d830 (change pattern 12 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 12 12) else d41 (change pattern 12 12)) = d830 pattern
  rw [s54, s49]
  rfl
theorem s56 (pattern : Twelve) : d13 (change pattern 12 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d4 (change pattern 12 12)) = d13 pattern
  rw [s20, s14]
  rfl
theorem s57 (pattern : Twelve) : d14 (change pattern 12 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 12) else d5 (change pattern 12 12)) = d14 pattern
  rw [s20, s16]
  rfl
theorem s58 (pattern : Twelve) : d21 (change pattern 12 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 12) else d13 (change pattern 12 12)) = d21 pattern
  rw [s57, s56]
  rfl
theorem s59 (pattern : Twelve) : d821 (change pattern 12 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 12) else d25 (change pattern 12 12)) = d821 pattern
  rw [s58, s18]
  rfl
theorem s60 (pattern : Twelve) : d822 (change pattern 12 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d21 (change pattern 12 12)) = d822 pattern
  rw [s20, s58]
  rfl
theorem s61 (pattern : Twelve) : d831 (change pattern 12 12) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 12 12) else d821 (change pattern 12 12)) = d831 pattern
  rw [s60, s59]
  rfl
theorem s62 (pattern : Twelve) : d845 (change pattern 12 12) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 12 12) else d830 (change pattern 12 12)) = d845 pattern
  rw [s61, s55]
  rfl
theorem s63 (pattern : Twelve) : d856 (change pattern 12 12) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 12 12) else d844 (change pattern 12 12)) = d856 pattern
  rw [s62, s53]
  rfl
theorem s64 (pattern : Twelve) : d862 (change pattern 12 12) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 12 12) else d855 (change pattern 12 12)) = d862 pattern
  rw [s63, s43]
  rfl
theorem s65 (pattern : Twelve) : d863 (change pattern 12 12) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d854 (change pattern 12 12)) = d863 pattern
  rw [s20, s37]
  rfl
theorem s66 (pattern : Twelve) : d867 (change pattern 12 12) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 12 12) else d862 (change pattern 12 12)) = d867 pattern
  rw [s65, s64]
  rfl
theorem s67 (pattern : Twelve) : d869 (change pattern 12 12) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 12 12) else d861 (change pattern 12 12)) = d869 pattern
  rw [s66, s38]
  rfl
theorem s68 (pattern : Twelve) : d823 (change pattern 12 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 12 12) else d17 (change pattern 12 12)) = d823 pattern
  rw [s9, s3]
  rfl
theorem s69 (pattern : Twelve) : d846 (change pattern 12 12) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d823 (change pattern 12 12)) = d846 pattern
  rw [s22, s68]
  rfl
theorem s70 (pattern : Twelve) : d857 (change pattern 12 12) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 12 12) else d838 (change pattern 12 12)) = d857 pattern
  rw [s69, s8]
  rfl
theorem s71 (pattern : Twelve) : d45 (change pattern 12 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d1 (change pattern 12 12)) = d45 pattern
  rw [s20, s1]
  rfl
theorem s72 (pattern : Twelve) : d832 (change pattern 12 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 12 12) else d34 (change pattern 12 12)) = d832 pattern
  rw [s71, s30]
  rfl
theorem s73 (pattern : Twelve) : d847 (change pattern 12 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 12 12) else d56 (change pattern 12 12)) = d847 pattern
  rw [s72, s27]
  rfl
theorem s74 (pattern : Twelve) : d833 (change pattern 12 12) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 12 12) else d34 (change pattern 12 12)) = d833 pattern
  rw [s45, s30]
  rfl
theorem s75 (pattern : Twelve) : d848 (change pattern 12 12) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d833 (change pattern 12 12)) = d848 pattern
  rw [s22, s74]
  rfl
theorem s76 (pattern : Twelve) : d858 (change pattern 12 12) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 12 12) else d847 (change pattern 12 12)) = d858 pattern
  rw [s75, s73]
  rfl
theorem s77 (pattern : Twelve) : d864 (change pattern 12 12) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 12 12) else d857 (change pattern 12 12)) = d864 pattern
  rw [s76, s70]
  rfl
theorem s78 (pattern : Twelve) : d46 (change pattern 12 12) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d1 (change pattern 12 12)) = d46 pattern
  rw [s11, s1]
  rfl
theorem s79 (pattern : Twelve) : d834 (change pattern 12 12) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 12 12) else d34 (change pattern 12 12)) = d834 pattern
  rw [s78, s30]
  rfl
theorem s80 (pattern : Twelve) : d849 (change pattern 12 12) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 12 12) else d30 (change pattern 12 12)) = d849 pattern
  rw [s79, s25]
  rfl
theorem s81 (pattern : Twelve) : d835 (change pattern 12 12) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 12 12) else d34 (change pattern 12 12)) = d835 pattern
  rw [s44, s30]
  rfl
theorem s82 (pattern : Twelve) : d850 (change pattern 12 12) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 12 12) else d835 (change pattern 12 12)) = d850 pattern
  rw [s22, s81]
  rfl
theorem s83 (pattern : Twelve) : d859 (change pattern 12 12) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 12 12) else d849 (change pattern 12 12)) = d859 pattern
  rw [s82, s80]
  rfl
theorem s84 (pattern : Twelve) : d47 (change pattern 12 12) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d3 (change pattern 12 12)) = d47 pattern
  rw [s20, s11]
  rfl
theorem s85 (pattern : Twelve) : d836 (change pattern 12 12) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 12 12) else d41 (change pattern 12 12)) = d836 pattern
  rw [s84, s49]
  rfl
theorem s86 (pattern : Twelve) : d851 (change pattern 12 12) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 12 12) else d59 (change pattern 12 12)) = d851 pattern
  rw [s85, s46]
  rfl
theorem s87 (pattern : Twelve) : d48 (change pattern 12 12) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d4 (change pattern 12 12)) = d48 pattern
  rw [s20, s14]
  rfl
theorem s88 (pattern : Twelve) : d837 (change pattern 12 12) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 12 12) else d41 (change pattern 12 12)) = d837 pattern
  rw [s87, s49]
  rfl
theorem s89 (pattern : Twelve) : d852 (change pattern 12 12) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 12 12) else d837 (change pattern 12 12)) = d852 pattern
  rw [s61, s88]
  rfl
theorem s90 (pattern : Twelve) : d860 (change pattern 12 12) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 12 12) else d851 (change pattern 12 12)) = d860 pattern
  rw [s89, s86]
  rfl
theorem s91 (pattern : Twelve) : d865 (change pattern 12 12) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 12 12) else d859 (change pattern 12 12)) = d865 pattern
  rw [s90, s83]
  rfl
theorem s92 (pattern : Twelve) : d866 (change pattern 12 12) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d858 (change pattern 12 12)) = d866 pattern
  rw [s20, s76]
  rfl
theorem s93 (pattern : Twelve) : d868 (change pattern 12 12) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 12 12) else d865 (change pattern 12 12)) = d868 pattern
  rw [s92, s91]
  rfl
theorem s94 (pattern : Twelve) : d870 (change pattern 12 12) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 12 12) else d864 (change pattern 12 12)) = d870 pattern
  rw [s93, s77]
  rfl
theorem s95 (pattern : Twelve) : d871 (change pattern 12 12) = d871 pattern := by
  change (if pattern.g then d870 (change pattern 12 12) else d869 (change pattern 12 12)) = d871 pattern
  rw [s94, s67]
  rfl
theorem s96 (pattern : Twelve) : d8 (change pattern 12 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 12) else d1 (change pattern 12 12)) = d8 pattern
  rw [s9, s1]
  rfl
theorem s97 (pattern : Twelve) : d1275 (change pattern 12 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 12) else d7 (change pattern 12 12)) = d1275 pattern
  rw [s96, s2]
  rfl
theorem s98 (pattern : Twelve) : d872 (change pattern 12 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 12) else d1 (change pattern 12 12)) = d872 pattern
  rw [s96, s1]
  rfl
theorem s99 (pattern : Twelve) : d1278 (change pattern 12 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 12) else d1275 (change pattern 12 12)) = d1278 pattern
  rw [s98, s97]
  rfl
theorem s100 (pattern : Twelve) : d1284 (change pattern 12 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 12) else d1278 (change pattern 12 12)) = d1284 pattern
  rw [s98, s99]
  rfl
theorem s101 (pattern : Twelve) : d1293 (change pattern 12 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 12 12) else d17 (change pattern 12 12)) = d1293 pattern
  rw [s100, s3]
  rfl
theorem s102 (pattern : Twelve) : d1294 (change pattern 12 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d19 (change pattern 12 12)) = d1294 pattern
  rw [s20, s13]
  rfl
theorem s103 (pattern : Twelve) : d1305 (change pattern 12 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 12 12) else d1293 (change pattern 12 12)) = d1305 pattern
  rw [s102, s101]
  rfl
theorem s104 (pattern : Twelve) : d117 (change pattern 12 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 12) else d3 (change pattern 12 12)) = d117 pattern
  rw [s14, s11]
  rfl
theorem s105 (pattern : Twelve) : d1276 (change pattern 12 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 12) else d9 (change pattern 12 12)) = d1276 pattern
  rw [s104, s28]
  rfl
theorem s106 (pattern : Twelve) : d1279 (change pattern 12 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 12) else d1275 (change pattern 12 12)) = d1279 pattern
  rw [s105, s97]
  rfl
theorem s107 (pattern : Twelve) : d1280 (change pattern 12 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d872 (change pattern 12 12)) = d1280 pattern
  rw [s20, s98]
  rfl
theorem s108 (pattern : Twelve) : d1285 (change pattern 12 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 12) else d1279 (change pattern 12 12)) = d1285 pattern
  rw [s107, s106]
  rfl
theorem s109 (pattern : Twelve) : d1295 (change pattern 12 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 12 12) else d827 (change pattern 12 12)) = d1295 pattern
  rw [s108, s35]
  rfl
theorem s110 (pattern : Twelve) : d29 (change pattern 12 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d19 (change pattern 12 12)) = d29 pattern
  rw [s20, s13]
  rfl
theorem s111 (pattern : Twelve) : d1286 (change pattern 12 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 12 12) else d817 (change pattern 12 12)) = d1286 pattern
  rw [s110, s19]
  rfl
theorem s112 (pattern : Twelve) : d1296 (change pattern 12 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1286 (change pattern 12 12)) = d1296 pattern
  rw [s20, s111]
  rfl
theorem s113 (pattern : Twelve) : d1306 (change pattern 12 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 12 12) else d1295 (change pattern 12 12)) = d1306 pattern
  rw [s112, s109]
  rfl
theorem s114 (pattern : Twelve) : d1313 (change pattern 12 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 12 12) else d1305 (change pattern 12 12)) = d1313 pattern
  rw [s113, s103]
  rfl
theorem s115 (pattern : Twelve) : d119 (change pattern 12 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 12 12) else d3 (change pattern 12 12)) = d119 pattern
  rw [s104, s11]
  rfl
theorem s116 (pattern : Twelve) : d1281 (change pattern 12 12) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 12 12) else d872 (change pattern 12 12)) = d1281 pattern
  rw [s115, s98]
  rfl
theorem s117 (pattern : Twelve) : d1287 (change pattern 12 12) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 12 12) else d1279 (change pattern 12 12)) = d1287 pattern
  rw [s116, s106]
  rfl
theorem s118 (pattern : Twelve) : d1297 (change pattern 12 12) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 12 12) else d34 (change pattern 12 12)) = d1297 pattern
  rw [s117, s30]
  rfl
theorem s119 (pattern : Twelve) : d1298 (change pattern 12 12) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d817 (change pattern 12 12)) = d1298 pattern
  rw [s20, s19]
  rfl
theorem s120 (pattern : Twelve) : d1307 (change pattern 12 12) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 12 12) else d1297 (change pattern 12 12)) = d1307 pattern
  rw [s119, s118]
  rfl
theorem s121 (pattern : Twelve) : d1277 (change pattern 12 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 12 12) else d15 (change pattern 12 12)) = d1277 pattern
  rw [s57, s47]
  rfl
theorem s122 (pattern : Twelve) : d1282 (change pattern 12 12) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 12 12) else d1276 (change pattern 12 12)) = d1282 pattern
  rw [s121, s105]
  rfl
theorem s123 (pattern : Twelve) : d125 (change pattern 12 12) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d119 (change pattern 12 12)) = d125 pattern
  rw [s20, s115]
  rfl
theorem s124 (pattern : Twelve) : d1288 (change pattern 12 12) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 12 12) else d1282 (change pattern 12 12)) = d1288 pattern
  rw [s123, s122]
  rfl
theorem s125 (pattern : Twelve) : d1299 (change pattern 12 12) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 12 12) else d830 (change pattern 12 12)) = d1299 pattern
  rw [s124, s55]
  rfl
theorem s126 (pattern : Twelve) : d1289 (change pattern 12 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 12 12) else d821 (change pattern 12 12)) = d1289 pattern
  rw [s21, s59]
  rfl
theorem s127 (pattern : Twelve) : d1300 (change pattern 12 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1289 (change pattern 12 12)) = d1300 pattern
  rw [s20, s126]
  rfl
theorem s128 (pattern : Twelve) : d1308 (change pattern 12 12) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 12 12) else d1299 (change pattern 12 12)) = d1308 pattern
  rw [s127, s125]
  rfl
theorem s129 (pattern : Twelve) : d1314 (change pattern 12 12) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 12 12) else d1307 (change pattern 12 12)) = d1314 pattern
  rw [s128, s120]
  rfl
theorem s130 (pattern : Twelve) : d1315 (change pattern 12 12) = d1315 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1306 (change pattern 12 12)) = d1315 pattern
  rw [s20, s113]
  rfl
theorem s131 (pattern : Twelve) : d1319 (change pattern 12 12) = d1319 pattern := by
  change (if pattern.d then d1315 (change pattern 12 12) else d1314 (change pattern 12 12)) = d1319 pattern
  rw [s130, s129]
  rfl
theorem s132 (pattern : Twelve) : d1321 (change pattern 12 12) = d1321 pattern := by
  change (if pattern.c then d1319 (change pattern 12 12) else d1313 (change pattern 12 12)) = d1321 pattern
  rw [s131, s114]
  rfl
theorem s133 (pattern : Twelve) : d1283 (change pattern 12 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 12 12) else d19 (change pattern 12 12)) = d1283 pattern
  rw [s29, s13]
  rfl
theorem s134 (pattern : Twelve) : d1301 (change pattern 12 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1283 (change pattern 12 12)) = d1301 pattern
  rw [s20, s133]
  rfl
theorem s135 (pattern : Twelve) : d1309 (change pattern 12 12) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 12 12) else d1293 (change pattern 12 12)) = d1309 pattern
  rw [s134, s101]
  rfl
theorem s136 (pattern : Twelve) : d1290 (change pattern 12 12) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 12 12) else d817 (change pattern 12 12)) = d1290 pattern
  rw [s54, s19]
  rfl
theorem s137 (pattern : Twelve) : d1302 (change pattern 12 12) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1290 (change pattern 12 12)) = d1302 pattern
  rw [s20, s136]
  rfl
theorem s138 (pattern : Twelve) : d1310 (change pattern 12 12) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 12 12) else d1295 (change pattern 12 12)) = d1310 pattern
  rw [s137, s109]
  rfl
theorem s139 (pattern : Twelve) : d1316 (change pattern 12 12) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 12 12) else d1309 (change pattern 12 12)) = d1316 pattern
  rw [s138, s135]
  rfl
theorem s140 (pattern : Twelve) : d1291 (change pattern 12 12) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 12 12) else d817 (change pattern 12 12)) = d1291 pattern
  rw [s49, s19]
  rfl
theorem s141 (pattern : Twelve) : d1303 (change pattern 12 12) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1291 (change pattern 12 12)) = d1303 pattern
  rw [s20, s140]
  rfl
theorem s142 (pattern : Twelve) : d1311 (change pattern 12 12) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 12 12) else d1297 (change pattern 12 12)) = d1311 pattern
  rw [s141, s118]
  rfl
theorem s143 (pattern : Twelve) : d49 (change pattern 12 12) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d24 (change pattern 12 12)) = d49 pattern
  rw [s20, s48]
  rfl
theorem s144 (pattern : Twelve) : d1292 (change pattern 12 12) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 12 12) else d821 (change pattern 12 12)) = d1292 pattern
  rw [s143, s59]
  rfl
theorem s145 (pattern : Twelve) : d1304 (change pattern 12 12) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1292 (change pattern 12 12)) = d1304 pattern
  rw [s20, s144]
  rfl
theorem s146 (pattern : Twelve) : d1312 (change pattern 12 12) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 12 12) else d1299 (change pattern 12 12)) = d1312 pattern
  rw [s145, s125]
  rfl
theorem s147 (pattern : Twelve) : d1317 (change pattern 12 12) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 12 12) else d1311 (change pattern 12 12)) = d1317 pattern
  rw [s146, s142]
  rfl
theorem s148 (pattern : Twelve) : d1318 (change pattern 12 12) = d1318 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1310 (change pattern 12 12)) = d1318 pattern
  rw [s20, s138]
  rfl
theorem s149 (pattern : Twelve) : d1320 (change pattern 12 12) = d1320 pattern := by
  change (if pattern.d then d1318 (change pattern 12 12) else d1317 (change pattern 12 12)) = d1320 pattern
  rw [s148, s147]
  rfl
end NetHack.Sokoban21.Diagram
