/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions04
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s750 (pattern : Twelve) : d11 (change pattern 3 2) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 3 2) else d1 (change pattern 3 2)) = d11 pattern
  rw [s742, s739]
  rfl
theorem s751 (pattern : Twelve) : d19 (change pattern 3 2) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 3 2) else d10 (change pattern 3 2)) = d19 pattern
  rw [s750, s749]
  rfl
theorem s752 (pattern : Twelve) : d6 (change pattern 3 2) = d6 pattern := by
  rfl
theorem s753 (pattern : Twelve) : d29 (change pattern 3 2) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d19 (change pattern 3 2)) = d29 pattern
  rw [s752, s751]
  rfl
theorem s754 (pattern : Twelve) : d55 (change pattern 3 2) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 3 2) else d34 (change pattern 3 2)) = d55 pattern
  rw [s753, s748]
  rfl
theorem s755 (pattern : Twelve) : d80 (change pattern 3 2) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 3 2) else d30 (change pattern 3 2)) = d80 pattern
  rw [s754, s738]
  rfl
theorem s756 (pattern : Twelve) : d95 (change pattern 3 2) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 3 2) else d79 (change pattern 3 2)) = d95 pattern
  rw [s755, s745]
  rfl
theorem s757 (pattern : Twelve) : d4 (change pattern 3 2) = d4 pattern := by
  rfl
theorem s758 (pattern : Twelve) : d38 (change pattern 3 2) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 3 2) else d2 (change pattern 3 2)) = d38 pattern
  rw [s757, s737]
  rfl
theorem s759 (pattern : Twelve) : d39 (change pattern 3 2) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d2 (change pattern 3 2)) = d39 pattern
  rw [s752, s737]
  rfl
theorem s760 (pattern : Twelve) : d59 (change pattern 3 2) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 3 2) else d38 (change pattern 3 2)) = d59 pattern
  rw [s759, s758]
  rfl
theorem s761 (pattern : Twelve) : d40 (change pattern 3 2) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d23 (change pattern 3 2)) = d40 pattern
  rw [s752, s747]
  rfl
theorem s762 (pattern : Twelve) : d60 (change pattern 3 2) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 3 2) else d38 (change pattern 3 2)) = d60 pattern
  rw [s761, s758]
  rfl
theorem s763 (pattern : Twelve) : d81 (change pattern 3 2) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 3 2) else d59 (change pattern 3 2)) = d81 pattern
  rw [s762, s760]
  rfl
theorem s764 (pattern : Twelve) : d5 (change pattern 3 2) = d5 pattern := by
  rfl
theorem s765 (pattern : Twelve) : d15 (change pattern 3 2) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 3 2) else d4 (change pattern 3 2)) = d15 pattern
  rw [s764, s757]
  rfl
theorem s766 (pattern : Twelve) : d24 (change pattern 3 2) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 3 2) else d4 (change pattern 3 2)) = d24 pattern
  rw [s765, s757]
  rfl
theorem s767 (pattern : Twelve) : d41 (change pattern 3 2) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 3 2) else d23 (change pattern 3 2)) = d41 pattern
  rw [s766, s747]
  rfl
theorem s768 (pattern : Twelve) : d16 (change pattern 3 2) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 3 2) else d2 (change pattern 3 2)) = d16 pattern
  rw [s757, s737]
  rfl
theorem s769 (pattern : Twelve) : d12 (change pattern 3 2) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 3 2) else d3 (change pattern 3 2)) = d12 pattern
  rw [s764, s742]
  rfl
theorem s770 (pattern : Twelve) : d25 (change pattern 3 2) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 3 2) else d16 (change pattern 3 2)) = d25 pattern
  rw [s769, s768]
  rfl
theorem s771 (pattern : Twelve) : d42 (change pattern 3 2) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d25 (change pattern 3 2)) = d42 pattern
  rw [s752, s770]
  rfl
theorem s772 (pattern : Twelve) : d61 (change pattern 3 2) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 3 2) else d41 (change pattern 3 2)) = d61 pattern
  rw [s771, s767]
  rfl
theorem s773 (pattern : Twelve) : d82 (change pattern 3 2) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 3 2) else d59 (change pattern 3 2)) = d82 pattern
  rw [s772, s760]
  rfl
theorem s774 (pattern : Twelve) : d96 (change pattern 3 2) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 3 2) else d81 (change pattern 3 2)) = d96 pattern
  rw [s773, s763]
  rfl
theorem s775 (pattern : Twelve) : d104 (change pattern 3 2) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 3 2) else d95 (change pattern 3 2)) = d104 pattern
  rw [s774, s756]
  rfl
theorem s776 (pattern : Twelve) : d223 (change pattern 3 2) = d104 pattern := by
  change d104 (change pattern 3 2) = d104 pattern
  exact s775 pattern
theorem s777 (pattern : Twelve) : d228 (change pattern 3 2) = d104 pattern := by
  change d223 (change pattern 3 2) = d104 pattern
  exact s776 pattern
theorem s778 (pattern : Twelve) : d46 (change pattern 3 2) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 3 2) else d1 (change pattern 3 2)) = d46 pattern
  rw [s742, s739]
  rfl
theorem s779 (pattern : Twelve) : d67 (change pattern 3 2) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 3 2) else d30 (change pattern 3 2)) = d67 pattern
  rw [s778, s738]
  rfl
theorem s780 (pattern : Twelve) : d87 (change pattern 3 2) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 3 2) else d30 (change pattern 3 2)) = d87 pattern
  rw [s779, s738]
  rfl
theorem s781 (pattern : Twelve) : d68 (change pattern 3 2) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 3 2) else d30 (change pattern 3 2)) = d68 pattern
  rw [s758, s738]
  rfl
theorem s782 (pattern : Twelve) : d64 (change pattern 3 2) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 3 2) else d34 (change pattern 3 2)) = d64 pattern
  rw [s761, s748]
  rfl
theorem s783 (pattern : Twelve) : d88 (change pattern 3 2) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 3 2) else d68 (change pattern 3 2)) = d88 pattern
  rw [s782, s781]
  rfl
theorem s784 (pattern : Twelve) : d100 (change pattern 3 2) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 3 2) else d87 (change pattern 3 2)) = d100 pattern
  rw [s783, s780]
  rfl
theorem s785 (pattern : Twelve) : d47 (change pattern 3 2) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d3 (change pattern 3 2)) = d47 pattern
  rw [s752, s742]
  rfl
theorem s786 (pattern : Twelve) : d69 (change pattern 3 2) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 3 2) else d38 (change pattern 3 2)) = d69 pattern
  rw [s785, s758]
  rfl
theorem s787 (pattern : Twelve) : d89 (change pattern 3 2) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 3 2) else d59 (change pattern 3 2)) = d89 pattern
  rw [s786, s760]
  rfl
theorem s788 (pattern : Twelve) : d48 (change pattern 3 2) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d4 (change pattern 3 2)) = d48 pattern
  rw [s752, s757]
  rfl
theorem s789 (pattern : Twelve) : d70 (change pattern 3 2) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 3 2) else d38 (change pattern 3 2)) = d70 pattern
  rw [s788, s758]
  rfl
theorem s790 (pattern : Twelve) : d49 (change pattern 3 2) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d24 (change pattern 3 2)) = d49 pattern
  rw [s752, s766]
  rfl
theorem s791 (pattern : Twelve) : d71 (change pattern 3 2) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 3 2) else d41 (change pattern 3 2)) = d71 pattern
  rw [s790, s767]
  rfl
theorem s792 (pattern : Twelve) : d90 (change pattern 3 2) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 3 2) else d70 (change pattern 3 2)) = d90 pattern
  rw [s791, s789]
  rfl
theorem s793 (pattern : Twelve) : d101 (change pattern 3 2) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 3 2) else d89 (change pattern 3 2)) = d101 pattern
  rw [s792, s787]
  rfl
theorem s794 (pattern : Twelve) : d108 (change pattern 3 2) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 3 2) else d100 (change pattern 3 2)) = d108 pattern
  rw [s793, s784]
  rfl
theorem s795 (pattern : Twelve) : d225 (change pattern 3 2) = d108 pattern := by
  change d108 (change pattern 3 2) = d108 pattern
  exact s794 pattern
theorem s796 (pattern : Twelve) : d229 (change pattern 3 2) = d108 pattern := by
  change d225 (change pattern 3 2) = d108 pattern
  exact s795 pattern
theorem s797 (pattern : Twelve) : d231 (change pattern 3 2) = d1898 pattern := by
  change (if pattern.g then d229 (change pattern 3 2) else d228 (change pattern 3 2)) = d1898 pattern
  rw [s796, s777]
  rfl
theorem s798 (pattern : Twelve) : d227 (change pattern 3 2) = d104 pattern := by
  change d104 (change pattern 3 2) = d104 pattern
  exact s775 pattern
theorem s799 (pattern : Twelve) : d230 (change pattern 3 2) = d104 pattern := by
  change d227 (change pattern 3 2) = d104 pattern
  exact s798 pattern
theorem s800 (pattern : Twelve) : d232 (change pattern 3 2) = d1898 pattern := by
  change (if pattern.g then d229 (change pattern 3 2) else d230 (change pattern 3 2)) = d1898 pattern
  rw [s796, s799]
  rfl
theorem s801 (pattern : Twelve) : d233 (change pattern 3 2) = d1898 pattern := by
  change (if pattern.b then d232 (change pattern 3 2) else d231 (change pattern 3 2)) = d1898 pattern
  rw [s800, s797]
  simp only [ite_self]
theorem s802 (pattern : Twelve) : d234 (change pattern 3 2) = d1898 pattern := by
  change (if pattern.a then d232 (change pattern 3 2) else d233 (change pattern 3 2)) = d1898 pattern
  rw [s800, s801]
  simp only [ite_self]
theorem s803 (pattern : Twelve) : d814 (change pattern 3 2) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 3 2) else d7 (change pattern 3 2)) = d814 pattern
  rw [s739, s740]
  rfl
theorem s804 (pattern : Twelve) : d819 (change pattern 3 2) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 3 2) else d814 (change pattern 3 2)) = d819 pattern
  rw [s742, s803]
  rfl
theorem s805 (pattern : Twelve) : d828 (change pattern 3 2) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 3 2) else d34 (change pattern 3 2)) = d828 pattern
  rw [s804, s748]
  rfl
theorem s806 (pattern : Twelve) : d842 (change pattern 3 2) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 3 2) else d30 (change pattern 3 2)) = d842 pattern
  rw [s805, s738]
  rfl
theorem s807 (pattern : Twelve) : d817 (change pattern 3 2) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 3 2) else d19 (change pattern 3 2)) = d817 pattern
  rw [s770, s751]
  rfl
theorem s808 (pattern : Twelve) : d825 (change pattern 3 2) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 3 2) else d817 (change pattern 3 2)) = d825 pattern
  rw [s771, s807]
  rfl
theorem s809 (pattern : Twelve) : d843 (change pattern 3 2) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 3 2) else d34 (change pattern 3 2)) = d843 pattern
  rw [s808, s748]
  rfl
theorem s810 (pattern : Twelve) : d855 (change pattern 3 2) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 3 2) else d842 (change pattern 3 2)) = d855 pattern
  rw [s809, s806]
  rfl
theorem s811 (pattern : Twelve) : d815 (change pattern 3 2) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 3 2) else d9 (change pattern 3 2)) = d815 pattern
  rw [s742, s746]
  rfl
theorem s812 (pattern : Twelve) : d820 (change pattern 3 2) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d815 (change pattern 3 2)) = d820 pattern
  rw [s752, s811]
  rfl
theorem s813 (pattern : Twelve) : d829 (change pattern 3 2) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 3 2) else d41 (change pattern 3 2)) = d829 pattern
  rw [s812, s767]
  rfl
theorem s814 (pattern : Twelve) : d844 (change pattern 3 2) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 3 2) else d59 (change pattern 3 2)) = d844 pattern
  rw [s813, s760]
  rfl
theorem s815 (pattern : Twelve) : d830 (change pattern 3 2) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 3 2) else d41 (change pattern 3 2)) = d830 pattern
  rw [s761, s767]
  rfl
theorem s816 (pattern : Twelve) : d13 (change pattern 3 2) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 3 2) else d4 (change pattern 3 2)) = d13 pattern
  rw [s752, s757]
  rfl
theorem s817 (pattern : Twelve) : d14 (change pattern 3 2) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 3 2) else d5 (change pattern 3 2)) = d14 pattern
  rw [s752, s764]
  rfl
theorem s818 (pattern : Twelve) : d21 (change pattern 3 2) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 3 2) else d13 (change pattern 3 2)) = d21 pattern
  rw [s817, s816]
  rfl
theorem s819 (pattern : Twelve) : d821 (change pattern 3 2) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 3 2) else d25 (change pattern 3 2)) = d821 pattern
  rw [s818, s770]
  rfl
theorem s820 (pattern : Twelve) : d822 (change pattern 3 2) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d21 (change pattern 3 2)) = d822 pattern
  rw [s752, s818]
  rfl
theorem s821 (pattern : Twelve) : d831 (change pattern 3 2) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 3 2) else d821 (change pattern 3 2)) = d831 pattern
  rw [s820, s819]
  rfl
theorem s822 (pattern : Twelve) : d845 (change pattern 3 2) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 3 2) else d830 (change pattern 3 2)) = d845 pattern
  rw [s821, s815]
  rfl
theorem s823 (pattern : Twelve) : d856 (change pattern 3 2) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 3 2) else d844 (change pattern 3 2)) = d856 pattern
  rw [s822, s814]
  rfl
theorem s824 (pattern : Twelve) : d862 (change pattern 3 2) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 3 2) else d855 (change pattern 3 2)) = d862 pattern
  rw [s823, s810]
  rfl
theorem s825 (pattern : Twelve) : d928 (change pattern 3 2) = d862 pattern := by
  change d862 (change pattern 3 2) = d862 pattern
  exact s824 pattern
theorem s826 (pattern : Twelve) : d933 (change pattern 3 2) = d862 pattern := by
  change d928 (change pattern 3 2) = d862 pattern
  exact s825 pattern
theorem s827 (pattern : Twelve) : d834 (change pattern 3 2) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 3 2) else d34 (change pattern 3 2)) = d834 pattern
  rw [s778, s748]
  rfl
theorem s828 (pattern : Twelve) : d849 (change pattern 3 2) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 3 2) else d30 (change pattern 3 2)) = d849 pattern
  rw [s827, s738]
  rfl
theorem s829 (pattern : Twelve) : d835 (change pattern 3 2) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 3 2) else d34 (change pattern 3 2)) = d835 pattern
  rw [s758, s748]
  rfl
theorem s830 (pattern : Twelve) : d850 (change pattern 3 2) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 3 2) else d835 (change pattern 3 2)) = d850 pattern
  rw [s808, s829]
  rfl
theorem s831 (pattern : Twelve) : d859 (change pattern 3 2) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 3 2) else d849 (change pattern 3 2)) = d859 pattern
  rw [s830, s828]
  rfl
theorem s832 (pattern : Twelve) : d836 (change pattern 3 2) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 3 2) else d41 (change pattern 3 2)) = d836 pattern
  rw [s785, s767]
  rfl
theorem s833 (pattern : Twelve) : d851 (change pattern 3 2) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 3 2) else d59 (change pattern 3 2)) = d851 pattern
  rw [s832, s760]
  rfl
theorem s834 (pattern : Twelve) : d837 (change pattern 3 2) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 3 2) else d41 (change pattern 3 2)) = d837 pattern
  rw [s788, s767]
  rfl
theorem s835 (pattern : Twelve) : d852 (change pattern 3 2) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 3 2) else d837 (change pattern 3 2)) = d852 pattern
  rw [s821, s834]
  rfl
theorem s836 (pattern : Twelve) : d860 (change pattern 3 2) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 3 2) else d851 (change pattern 3 2)) = d860 pattern
  rw [s835, s833]
  rfl
theorem s837 (pattern : Twelve) : d865 (change pattern 3 2) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 3 2) else d859 (change pattern 3 2)) = d865 pattern
  rw [s836, s831]
  rfl
theorem s838 (pattern : Twelve) : d930 (change pattern 3 2) = d865 pattern := by
  change d865 (change pattern 3 2) = d865 pattern
  exact s837 pattern
theorem s839 (pattern : Twelve) : d934 (change pattern 3 2) = d865 pattern := by
  change d930 (change pattern 3 2) = d865 pattern
  exact s838 pattern
theorem s840 (pattern : Twelve) : d936 (change pattern 3 2) = d1899 pattern := by
  change (if pattern.g then d934 (change pattern 3 2) else d933 (change pattern 3 2)) = d1899 pattern
  rw [s839, s826]
  rfl
theorem s841 (pattern : Twelve) : d932 (change pattern 3 2) = d862 pattern := by
  change d862 (change pattern 3 2) = d862 pattern
  exact s824 pattern
theorem s842 (pattern : Twelve) : d935 (change pattern 3 2) = d862 pattern := by
  change d932 (change pattern 3 2) = d862 pattern
  exact s841 pattern
theorem s843 (pattern : Twelve) : d937 (change pattern 3 2) = d1899 pattern := by
  change (if pattern.g then d934 (change pattern 3 2) else d935 (change pattern 3 2)) = d1899 pattern
  rw [s839, s842]
  rfl
theorem s844 (pattern : Twelve) : d938 (change pattern 3 2) = d1899 pattern := by
  change (if pattern.b then d937 (change pattern 3 2) else d936 (change pattern 3 2)) = d1899 pattern
  rw [s843, s840]
  simp only [ite_self]
theorem s845 (pattern : Twelve) : d939 (change pattern 3 2) = d1899 pattern := by
  change (if pattern.a then d937 (change pattern 3 2) else d938 (change pattern 3 2)) = d1899 pattern
  rw [s843, s844]
  simp only [ite_self]
theorem s846 (pattern : Twelve) : d8 (change pattern 3 2) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 3 2) else d1 (change pattern 3 2)) = d8 pattern
  rw [s737, s739]
  rfl
theorem s847 (pattern : Twelve) : d1275 (change pattern 3 2) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 3 2) else d7 (change pattern 3 2)) = d1275 pattern
  rw [s846, s740]
  rfl
theorem s848 (pattern : Twelve) : d117 (change pattern 3 2) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 3 2) else d3 (change pattern 3 2)) = d117 pattern
  rw [s757, s742]
  rfl
theorem s849 (pattern : Twelve) : d1276 (change pattern 3 2) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 3 2) else d9 (change pattern 3 2)) = d1276 pattern
  rw [s848, s746]
  rfl
theorem s850 (pattern : Twelve) : d1279 (change pattern 3 2) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 3 2) else d1275 (change pattern 3 2)) = d1279 pattern
  rw [s849, s847]
  rfl
theorem s851 (pattern : Twelve) : d872 (change pattern 3 2) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 3 2) else d1 (change pattern 3 2)) = d872 pattern
  rw [s846, s739]
  rfl
theorem s852 (pattern : Twelve) : d119 (change pattern 3 2) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 3 2) else d3 (change pattern 3 2)) = d119 pattern
  rw [s848, s742]
  rfl
theorem s853 (pattern : Twelve) : d1281 (change pattern 3 2) = d1281 pattern := by
  change (if pattern.i then d119 (change pattern 3 2) else d872 (change pattern 3 2)) = d1281 pattern
  rw [s852, s851]
  rfl
theorem s854 (pattern : Twelve) : d1287 (change pattern 3 2) = d1287 pattern := by
  change (if pattern.h then d1281 (change pattern 3 2) else d1279 (change pattern 3 2)) = d1287 pattern
  rw [s853, s850]
  rfl
theorem s855 (pattern : Twelve) : d1297 (change pattern 3 2) = d1297 pattern := by
  change (if pattern.f then d1287 (change pattern 3 2) else d34 (change pattern 3 2)) = d1297 pattern
  rw [s854, s748]
  rfl
theorem s856 (pattern : Twelve) : d1298 (change pattern 3 2) = d1298 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d817 (change pattern 3 2)) = d1298 pattern
  rw [s752, s807]
  rfl
theorem s857 (pattern : Twelve) : d1307 (change pattern 3 2) = d1307 pattern := by
  change (if pattern.e then d1298 (change pattern 3 2) else d1297 (change pattern 3 2)) = d1307 pattern
  rw [s856, s855]
  rfl
theorem s858 (pattern : Twelve) : d1277 (change pattern 3 2) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 3 2) else d15 (change pattern 3 2)) = d1277 pattern
  rw [s817, s765]
  rfl
theorem s859 (pattern : Twelve) : d1282 (change pattern 3 2) = d1282 pattern := by
  change (if pattern.i then d1277 (change pattern 3 2) else d1276 (change pattern 3 2)) = d1282 pattern
  rw [s858, s849]
  rfl
theorem s860 (pattern : Twelve) : d125 (change pattern 3 2) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d119 (change pattern 3 2)) = d125 pattern
  rw [s752, s852]
  rfl
theorem s861 (pattern : Twelve) : d1288 (change pattern 3 2) = d1288 pattern := by
  change (if pattern.h then d125 (change pattern 3 2) else d1282 (change pattern 3 2)) = d1288 pattern
  rw [s860, s859]
  rfl
theorem s862 (pattern : Twelve) : d1299 (change pattern 3 2) = d1299 pattern := by
  change (if pattern.f then d1288 (change pattern 3 2) else d830 (change pattern 3 2)) = d1299 pattern
  rw [s861, s815]
  rfl
theorem s863 (pattern : Twelve) : d1289 (change pattern 3 2) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 3 2) else d821 (change pattern 3 2)) = d1289 pattern
  rw [s771, s819]
  rfl
theorem s864 (pattern : Twelve) : d1300 (change pattern 3 2) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d1289 (change pattern 3 2)) = d1300 pattern
  rw [s752, s863]
  rfl
theorem s865 (pattern : Twelve) : d1308 (change pattern 3 2) = d1308 pattern := by
  change (if pattern.e then d1300 (change pattern 3 2) else d1299 (change pattern 3 2)) = d1308 pattern
  rw [s864, s862]
  rfl
theorem s866 (pattern : Twelve) : d1314 (change pattern 3 2) = d1314 pattern := by
  change (if pattern.j then d1308 (change pattern 3 2) else d1307 (change pattern 3 2)) = d1314 pattern
  rw [s865, s857]
  rfl
theorem s867 (pattern : Twelve) : d1369 (change pattern 3 2) = d1314 pattern := by
  change d1314 (change pattern 3 2) = d1314 pattern
  exact s866 pattern
theorem s868 (pattern : Twelve) : d1373 (change pattern 3 2) = d1314 pattern := by
  change d1369 (change pattern 3 2) = d1314 pattern
  exact s867 pattern
theorem s869 (pattern : Twelve) : d1291 (change pattern 3 2) = d1291 pattern := by
  change (if pattern.h then d41 (change pattern 3 2) else d817 (change pattern 3 2)) = d1291 pattern
  rw [s767, s807]
  rfl
theorem s870 (pattern : Twelve) : d1303 (change pattern 3 2) = d1303 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d1291 (change pattern 3 2)) = d1303 pattern
  rw [s752, s869]
  rfl
theorem s871 (pattern : Twelve) : d1311 (change pattern 3 2) = d1311 pattern := by
  change (if pattern.e then d1303 (change pattern 3 2) else d1297 (change pattern 3 2)) = d1311 pattern
  rw [s870, s855]
  rfl
theorem s872 (pattern : Twelve) : d1292 (change pattern 3 2) = d1292 pattern := by
  change (if pattern.h then d49 (change pattern 3 2) else d821 (change pattern 3 2)) = d1292 pattern
  rw [s790, s819]
  rfl
theorem s873 (pattern : Twelve) : d1304 (change pattern 3 2) = d1304 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d1292 (change pattern 3 2)) = d1304 pattern
  rw [s752, s872]
  rfl
theorem s874 (pattern : Twelve) : d1312 (change pattern 3 2) = d1312 pattern := by
  change (if pattern.e then d1304 (change pattern 3 2) else d1299 (change pattern 3 2)) = d1312 pattern
  rw [s873, s862]
  rfl
theorem s875 (pattern : Twelve) : d1317 (change pattern 3 2) = d1317 pattern := by
  change (if pattern.j then d1312 (change pattern 3 2) else d1311 (change pattern 3 2)) = d1317 pattern
  rw [s874, s871]
  rfl
theorem s876 (pattern : Twelve) : d1371 (change pattern 3 2) = d1317 pattern := by
  change d1317 (change pattern 3 2) = d1317 pattern
  exact s875 pattern
theorem s877 (pattern : Twelve) : d1374 (change pattern 3 2) = d1317 pattern := by
  change d1371 (change pattern 3 2) = d1317 pattern
  exact s876 pattern
theorem s878 (pattern : Twelve) : d1376 (change pattern 3 2) = d1900 pattern := by
  change (if pattern.g then d1374 (change pattern 3 2) else d1373 (change pattern 3 2)) = d1900 pattern
  rw [s877, s868]
  rfl
theorem s879 (pattern : Twelve) : d1375 (change pattern 3 2) = d1314 pattern := by
  change d1369 (change pattern 3 2) = d1314 pattern
  exact s867 pattern
theorem s880 (pattern : Twelve) : d1377 (change pattern 3 2) = d1900 pattern := by
  change (if pattern.g then d1374 (change pattern 3 2) else d1375 (change pattern 3 2)) = d1900 pattern
  rw [s877, s879]
  rfl
theorem s881 (pattern : Twelve) : d1378 (change pattern 3 2) = d1900 pattern := by
  change (if pattern.b then d1377 (change pattern 3 2) else d1376 (change pattern 3 2)) = d1900 pattern
  rw [s880, s878]
  simp only [ite_self]
theorem s882 (pattern : Twelve) : d1379 (change pattern 3 2) = d1900 pattern := by
  change (if pattern.a then d1377 (change pattern 3 2) else d1378 (change pattern 3 2)) = d1900 pattern
  rw [s880, s881]
  simp only [ite_self]
theorem s883 (pattern : Twelve) : d1324 (change pattern 3 2) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 3 2) else d11 (change pattern 3 2)) = d1324 pattern
  rw [s768, s750]
  rfl
theorem s884 (pattern : Twelve) : d20 (change pattern 3 2) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 3 2) else d12 (change pattern 3 2)) = d20 pattern
  rw [s816, s769]
  rfl
theorem s885 (pattern : Twelve) : d1644 (change pattern 3 2) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 3 2) else d1324 (change pattern 3 2)) = d1644 pattern
  rw [s884, s883]
  rfl
theorem s886 (pattern : Twelve) : d1652 (change pattern 3 2) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 3 2) else d817 (change pattern 3 2)) = d1652 pattern
  rw [s885, s807]
  rfl
theorem s887 (pattern : Twelve) : d1653 (change pattern 3 2) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d821 (change pattern 3 2)) = d1653 pattern
  rw [s752, s819]
  rfl
theorem s888 (pattern : Twelve) : d1658 (change pattern 3 2) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 3 2) else d1652 (change pattern 3 2)) = d1658 pattern
  rw [s887, s886]
  rfl
theorem s889 (pattern : Twelve) : d22 (change pattern 3 2) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 3 2) else d14 (change pattern 3 2)) = d22 pattern
  rw [s752, s817]
  rfl
theorem s890 (pattern : Twelve) : d1646 (change pattern 3 2) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 3 2) else d20 (change pattern 3 2)) = d1646 pattern
  rw [s889, s884]
  rfl
theorem s891 (pattern : Twelve) : d128 (change pattern 3 2) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 3 2) else d20 (change pattern 3 2)) = d128 pattern
  rw [s752, s884]
  rfl
theorem s892 (pattern : Twelve) : d1648 (change pattern 3 2) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 3 2) else d1646 (change pattern 3 2)) = d1648 pattern
  rw [s891, s890]
  rfl
theorem s893 (pattern : Twelve) : d1654 (change pattern 3 2) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 3 2) else d1289 (change pattern 3 2)) = d1654 pattern
  rw [s892, s863]
  rfl
theorem s894 (pattern : Twelve) : d1655 (change pattern 3 2) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 3 2) else d822 (change pattern 3 2)) = d1655 pattern
  rw [s752, s820]
  rfl
theorem s895 (pattern : Twelve) : d1659 (change pattern 3 2) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 3 2) else d1654 (change pattern 3 2)) = d1659 pattern
  rw [s894, s893]
  rfl
theorem s896 (pattern : Twelve) : d1661 (change pattern 3 2) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 3 2) else d1658 (change pattern 3 2)) = d1661 pattern
  rw [s895, s888]
  rfl
theorem s897 (pattern : Twelve) : d1687 (change pattern 3 2) = d1661 pattern := by
  change d1661 (change pattern 3 2) = d1661 pattern
  exact s896 pattern
theorem s898 (pattern : Twelve) : d1688 (change pattern 3 2) = d1661 pattern := by
  change d1687 (change pattern 3 2) = d1661 pattern
  exact s897 pattern
theorem s899 (pattern : Twelve) : d0 (change pattern 7 12) = d0 pattern := by
  rfl
end NetHack.Sokoban21.Diagram
