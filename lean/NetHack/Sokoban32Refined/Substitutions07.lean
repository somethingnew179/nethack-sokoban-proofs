/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub840 (p : Pattern) : d338 (change p 134 (some 160)) = d933 p := by
  change (if p 133 then d337 (change p 134 (some 160)) else d336 (change p 134 (some 160))) = d933 p
  rw [sub839, sub836]
  rfl
theorem sub841 (p : Pattern) : d339 (change p 134 (some 160)) = d934 p := by
  change (if p 132 then d338 (change p 134 (some 160)) else d336 (change p 134 (some 160))) = d934 p
  rw [sub840, sub836]
  rfl
theorem sub842 (p : Pattern) : d340 (change p 134 (some 160)) = d935 p := by
  change (if p 113 then d339 (change p 134 (some 160)) else d335 (change p 134 (some 160))) = d935 p
  rw [sub841, sub833]
  rfl
theorem sub843 (p : Pattern) : d341 (change p 134 (some 160)) = d936 p := by
  change (if p 112 then d340 (change p 134 (some 160)) else d331 (change p 134 (some 160))) = d936 p
  rw [sub842, sub829]
  rfl
theorem sub844 (p : Pattern) : d68 (change p 134 (some 160)) = d937 p := by
  change (if p 139 then d2 (change p 134 (some 160)) else d40 (change p 134 (some 160))) = d937 p
  rw [sub804, sub824]
  rfl
theorem sub845 (p : Pattern) : d69 (change p 134 (some 160)) = d938 p := by
  change (if p 138 then d68 (change p 134 (some 160)) else d40 (change p 134 (some 160))) = d938 p
  rw [sub844, sub824]
  rfl
theorem sub846 (p : Pattern) : d342 (change p 134 (some 160)) = d938 p := by
  change d69 (change p 134 (some 160)) = d938 p
  exact sub845 p
theorem sub847 (p : Pattern) : d343 (change p 134 (some 160)) = d939 p := by
  change (if p 133 then d342 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d939 p
  rw [sub846, sub820]
  rfl
theorem sub848 (p : Pattern) : d344 (change p 134 (some 160)) = d940 p := by
  change (if p 132 then d343 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d940 p
  rw [sub847, sub820]
  rfl
theorem sub849 (p : Pattern) : d345 (change p 134 (some 160)) = d937 p := by
  change d68 (change p 134 (some 160)) = d937 p
  exact sub844 p
theorem sub850 (p : Pattern) : d346 (change p 134 (some 160)) = d941 p := by
  change (if p 133 then d345 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d941 p
  rw [sub849, sub820]
  rfl
theorem sub851 (p : Pattern) : d347 (change p 134 (some 160)) = d942 p := by
  change (if p 132 then d346 (change p 134 (some 160)) else d328 (change p 134 (some 160))) = d942 p
  rw [sub850, sub820]
  rfl
theorem sub852 (p : Pattern) : d348 (change p 134 (some 160)) = d943 p := by
  change (if p 113 then d347 (change p 134 (some 160)) else d344 (change p 134 (some 160))) = d943 p
  rw [sub851, sub848]
  rfl
theorem sub853 (p : Pattern) : d349 (change p 134 (some 160)) = d944 p := by
  change (if p 133 then d345 (change p 134 (some 160)) else d332 (change p 134 (some 160))) = d944 p
  rw [sub849, sub830]
  rfl
theorem sub854 (p : Pattern) : d350 (change p 134 (some 160)) = d945 p := by
  change (if p 132 then d349 (change p 134 (some 160)) else d332 (change p 134 (some 160))) = d945 p
  rw [sub853, sub830]
  rfl
theorem sub855 (p : Pattern) : d351 (change p 134 (some 160)) = d946 p := by
  change (if p 133 then d345 (change p 134 (some 160)) else d336 (change p 134 (some 160))) = d946 p
  rw [sub849, sub836]
  rfl
theorem sub856 (p : Pattern) : d352 (change p 134 (some 160)) = d947 p := by
  change (if p 132 then d351 (change p 134 (some 160)) else d336 (change p 134 (some 160))) = d947 p
  rw [sub855, sub836]
  rfl
theorem sub857 (p : Pattern) : d353 (change p 134 (some 160)) = d948 p := by
  change (if p 113 then d352 (change p 134 (some 160)) else d350 (change p 134 (some 160))) = d948 p
  rw [sub856, sub854]
  rfl
theorem sub858 (p : Pattern) : d354 (change p 134 (some 160)) = d949 p := by
  change (if p 112 then d353 (change p 134 (some 160)) else d348 (change p 134 (some 160))) = d949 p
  rw [sub857, sub852]
  rfl
theorem sub859 (p : Pattern) : d355 (change p 134 (some 160)) = d950 p := by
  change (if p 106 then d354 (change p 134 (some 160)) else d341 (change p 134 (some 160))) = d950 p
  rw [sub858, sub843]
  rfl
theorem sub860 (p : Pattern) : d86 (change p 134 (some 160)) = d951 p := by
  change (if p 138 then d52 (change p 134 (some 160)) else d8 (change p 134 (some 160))) = d951 p
  rw [sub834, sub810]
  rfl
theorem sub861 (p : Pattern) : d356 (change p 134 (some 160)) = d951 p := by
  change d86 (change p 134 (some 160)) = d951 p
  exact sub860 p
theorem sub862 (p : Pattern) : d92 (change p 134 (some 160)) = d952 p := by
  change (if p 138 then d61 (change p 134 (some 160)) else d38 (change p 134 (some 160))) = d952 p
  rw [sub837, sub822]
  rfl
theorem sub863 (p : Pattern) : d357 (change p 134 (some 160)) = d952 p := by
  change d92 (change p 134 (some 160)) = d952 p
  exact sub862 p
theorem sub864 (p : Pattern) : d358 (change p 134 (some 160)) = d953 p := by
  change (if p 133 then d357 (change p 134 (some 160)) else d356 (change p 134 (some 160))) = d953 p
  rw [sub863, sub861]
  rfl
theorem sub865 (p : Pattern) : d359 (change p 134 (some 160)) = d954 p := by
  change (if p 132 then d358 (change p 134 (some 160)) else d356 (change p 134 (some 160))) = d954 p
  rw [sub864, sub861]
  rfl
theorem sub866 (p : Pattern) : d360 (change p 134 (some 160)) = d955 p := by
  change (if p 113 then d359 (change p 134 (some 160)) else d331 (change p 134 (some 160))) = d955 p
  rw [sub865, sub829]
  rfl
theorem sub867 (p : Pattern) : d97 (change p 134 (some 160)) = d956 p := by
  change (if p 139 then d2 (change p 134 (some 160)) else d14 (change p 134 (some 160))) = d956 p
  rw [sub804, sub817]
  rfl
theorem sub868 (p : Pattern) : d98 (change p 134 (some 160)) = d957 p := by
  change (if p 138 then d97 (change p 134 (some 160)) else d14 (change p 134 (some 160))) = d957 p
  rw [sub867, sub817]
  rfl
theorem sub869 (p : Pattern) : d361 (change p 134 (some 160)) = d957 p := by
  change d98 (change p 134 (some 160)) = d957 p
  exact sub868 p
theorem sub870 (p : Pattern) : d362 (change p 134 (some 160)) = d958 p := by
  change (if p 133 then d342 (change p 134 (some 160)) else d361 (change p 134 (some 160))) = d958 p
  rw [sub846, sub869]
  rfl
theorem sub871 (p : Pattern) : d363 (change p 134 (some 160)) = d959 p := by
  change (if p 132 then d362 (change p 134 (some 160)) else d361 (change p 134 (some 160))) = d959 p
  rw [sub870, sub869]
  rfl
theorem sub872 (p : Pattern) : d364 (change p 134 (some 160)) = d960 p := by
  change (if p 112 then d363 (change p 134 (some 160)) else d360 (change p 134 (some 160))) = d960 p
  rw [sub871, sub866]
  rfl
theorem sub873 (p : Pattern) : d365 (change p 134 (some 160)) = d961 p := by
  change (if p 133 then d345 (change p 134 (some 160)) else d356 (change p 134 (some 160))) = d961 p
  rw [sub849, sub861]
  rfl
theorem sub874 (p : Pattern) : d366 (change p 134 (some 160)) = d962 p := by
  change (if p 132 then d365 (change p 134 (some 160)) else d356 (change p 134 (some 160))) = d962 p
  rw [sub873, sub861]
  rfl
theorem sub875 (p : Pattern) : d367 (change p 134 (some 160)) = d963 p := by
  change (if p 113 then d366 (change p 134 (some 160)) else d347 (change p 134 (some 160))) = d963 p
  rw [sub874, sub851]
  rfl
theorem sub876 (p : Pattern) : d368 (change p 134 (some 160)) = d964 p := by
  change (if p 133 then d2 (change p 134 (some 160)) else d361 (change p 134 (some 160))) = d964 p
  rw [sub804, sub869]
  rfl
theorem sub877 (p : Pattern) : d369 (change p 134 (some 160)) = d965 p := by
  change (if p 132 then d368 (change p 134 (some 160)) else d361 (change p 134 (some 160))) = d965 p
  rw [sub876, sub869]
  rfl
theorem sub878 (p : Pattern) : d370 (change p 134 (some 160)) = d956 p := by
  change d97 (change p 134 (some 160)) = d956 p
  exact sub867 p
theorem sub879 (p : Pattern) : d371 (change p 134 (some 160)) = d966 p := by
  change (if p 133 then d2 (change p 134 (some 160)) else d370 (change p 134 (some 160))) = d966 p
  rw [sub804, sub878]
  rfl
theorem sub880 (p : Pattern) : d372 (change p 134 (some 160)) = d967 p := by
  change (if p 132 then d371 (change p 134 (some 160)) else d370 (change p 134 (some 160))) = d967 p
  rw [sub879, sub878]
  rfl
theorem sub881 (p : Pattern) : d373 (change p 134 (some 160)) = d968 p := by
  change (if p 113 then d372 (change p 134 (some 160)) else d369 (change p 134 (some 160))) = d968 p
  rw [sub880, sub877]
  rfl
theorem sub882 (p : Pattern) : d374 (change p 134 (some 160)) = d969 p := by
  change (if p 112 then d373 (change p 134 (some 160)) else d367 (change p 134 (some 160))) = d969 p
  rw [sub881, sub875]
  rfl
theorem sub883 (p : Pattern) : d375 (change p 134 (some 160)) = d970 p := by
  change (if p 106 then d374 (change p 134 (some 160)) else d364 (change p 134 (some 160))) = d970 p
  rw [sub882, sub872]
  rfl
theorem sub884 (p : Pattern) : d376 (change p 134 (some 160)) = d971 p := by
  change (if p 86 then d375 (change p 134 (some 160)) else d355 (change p 134 (some 160))) = d971 p
  rw [sub883, sub859]
  rfl
theorem sub885 (p : Pattern) : d377 (change p 134 (some 160)) = d972 p := by
  change (if p 112 then d353 (change p 134 (some 160)) else d347 (change p 134 (some 160))) = d972 p
  rw [sub857, sub851]
  rfl
theorem sub886 (p : Pattern) : d378 (change p 134 (some 160)) = d973 p := by
  change (if p 106 then d377 (change p 134 (some 160)) else d341 (change p 134 (some 160))) = d973 p
  rw [sub885, sub843]
  rfl
theorem sub887 (p : Pattern) : d379 (change p 134 (some 160)) = d974 p := by
  change (if p 133 then d345 (change p 134 (some 160)) else d370 (change p 134 (some 160))) = d974 p
  rw [sub849, sub878]
  rfl
theorem sub888 (p : Pattern) : d380 (change p 134 (some 160)) = d975 p := by
  change (if p 132 then d379 (change p 134 (some 160)) else d370 (change p 134 (some 160))) = d975 p
  rw [sub887, sub878]
  rfl
theorem sub889 (p : Pattern) : d381 (change p 134 (some 160)) = d976 p := by
  change (if p 113 then d380 (change p 134 (some 160)) else d363 (change p 134 (some 160))) = d976 p
  rw [sub888, sub871]
  rfl
theorem sub890 (p : Pattern) : d382 (change p 134 (some 160)) = d977 p := by
  change (if p 112 then d381 (change p 134 (some 160)) else d360 (change p 134 (some 160))) = d977 p
  rw [sub889, sub866]
  rfl
theorem sub891 (p : Pattern) : d383 (change p 134 (some 160)) = d978 p := by
  change (if p 113 then d352 (change p 134 (some 160)) else d347 (change p 134 (some 160))) = d978 p
  rw [sub856, sub851]
  rfl
theorem sub892 (p : Pattern) : d384 (change p 134 (some 160)) = d979 p := by
  change (if p 113 then d2 (change p 134 (some 160)) else d372 (change p 134 (some 160))) = d979 p
  rw [sub804, sub880]
  rfl
theorem sub893 (p : Pattern) : d385 (change p 134 (some 160)) = d980 p := by
  change (if p 112 then d384 (change p 134 (some 160)) else d383 (change p 134 (some 160))) = d980 p
  rw [sub892, sub891]
  rfl
theorem sub894 (p : Pattern) : d386 (change p 134 (some 160)) = d981 p := by
  change (if p 106 then d385 (change p 134 (some 160)) else d382 (change p 134 (some 160))) = d981 p
  rw [sub893, sub890]
  rfl
theorem sub895 (p : Pattern) : d387 (change p 134 (some 160)) = d982 p := by
  change (if p 86 then d386 (change p 134 (some 160)) else d378 (change p 134 (some 160))) = d982 p
  rw [sub894, sub886]
  rfl
theorem sub896 (p : Pattern) : d388 (change p 134 (some 160)) = d983 p := by
  change (if p 80 then d387 (change p 134 (some 160)) else d376 (change p 134 (some 160))) = d983 p
  rw [sub895, sub884]
  rfl
theorem sub897 (p : Pattern) : d0 (change p 10000 (some 161)) = d0 p := by
  rfl
theorem sub898 (p : Pattern) : d2 (change p 10000 (some 161)) = d2 p := by
  rfl
theorem sub899 (p : Pattern) : d3 (change p 10000 (some 161)) = d2 p := by
  change d2 (change p 10000 (some 161)) = d2 p
  exact sub898 p
theorem sub900 (p : Pattern) : d4 (change p 10000 (some 161)) = d5 p := by
  change (if p 160 then d3 (change p 10000 (some 161)) else d0 (change p 10000 (some 161))) = d5 p
  rw [sub899, sub897]
  rfl
theorem sub901 (p : Pattern) : d5 (change p 10000 (some 161)) = d5 p := by
  change (if p 160 then d2 (change p 10000 (some 161)) else d0 (change p 10000 (some 161))) = d5 p
  rw [sub898, sub897]
  rfl
theorem sub902 (p : Pattern) : d6 (change p 10000 (some 161)) = d5 p := by
  change (if p 159 then d5 (change p 10000 (some 161)) else d4 (change p 10000 (some 161))) = d5 p
  rw [sub901, sub900]
  simp only [ite_self]
theorem sub903 (p : Pattern) : d7 (change p 10000 (some 161)) = d37 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d4 (change p 10000 (some 161))) = d37 p
  rw [sub898, sub900]
  rfl
theorem sub904 (p : Pattern) : d8 (change p 10000 (some 161)) = d697 p := by
  change (if p 158 then d7 (change p 10000 (some 161)) else d6 (change p 10000 (some 161))) = d697 p
  rw [sub903, sub902]
  rfl
theorem sub905 (p : Pattern) : d1 (change p 10000 (some 161)) = d1 p := by
  rfl
theorem sub906 (p : Pattern) : d9 (change p 10000 (some 161)) = d2 p := by
  change d2 (change p 10000 (some 161)) = d2 p
  exact sub898 p
theorem sub907 (p : Pattern) : d10 (change p 10000 (some 161)) = d11 p := by
  change (if p 160 then d9 (change p 10000 (some 161)) else d1 (change p 10000 (some 161))) = d11 p
  rw [sub906, sub905]
  rfl
theorem sub908 (p : Pattern) : d11 (change p 10000 (some 161)) = d11 p := by
  change (if p 160 then d2 (change p 10000 (some 161)) else d1 (change p 10000 (some 161))) = d11 p
  rw [sub898, sub905]
  rfl
theorem sub909 (p : Pattern) : d12 (change p 10000 (some 161)) = d11 p := by
  change (if p 159 then d11 (change p 10000 (some 161)) else d10 (change p 10000 (some 161))) = d11 p
  rw [sub908, sub907]
  simp only [ite_self]
theorem sub910 (p : Pattern) : d13 (change p 10000 (some 161)) = d39 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d10 (change p 10000 (some 161))) = d39 p
  rw [sub898, sub907]
  rfl
theorem sub911 (p : Pattern) : d14 (change p 10000 (some 161)) = d698 p := by
  change (if p 158 then d13 (change p 10000 (some 161)) else d12 (change p 10000 (some 161))) = d698 p
  rw [sub910, sub909]
  rfl
theorem sub912 (p : Pattern) : d15 (change p 10000 (some 161)) = d699 p := by
  change (if p 139 then d14 (change p 10000 (some 161)) else d8 (change p 10000 (some 161))) = d699 p
  rw [sub911, sub904]
  rfl
theorem sub913 (p : Pattern) : d16 (change p 10000 (some 161)) = d700 p := by
  change (if p 138 then d15 (change p 10000 (some 161)) else d8 (change p 10000 (some 161))) = d700 p
  rw [sub912, sub904]
  rfl
theorem sub914 (p : Pattern) : d17 (change p 10000 (some 161)) = d2 p := by
  change (if p 160 then d2 (change p 10000 (some 161)) else d3 (change p 10000 (some 161))) = d2 p
  rw [sub898, sub899]
  simp only [ite_self]
theorem sub915 (p : Pattern) : d18 (change p 10000 (some 161)) = d37 p := by
  change (if p 159 then d17 (change p 10000 (some 161)) else d4 (change p 10000 (some 161))) = d37 p
  rw [sub914, sub900]
  rfl
theorem sub916 (p : Pattern) : d19 (change p 10000 (some 161)) = d2 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d17 (change p 10000 (some 161))) = d2 p
  rw [sub898, sub914]
  simp only [ite_self]
theorem sub917 (p : Pattern) : d20 (change p 10000 (some 161)) = d986 p := by
  change (if p 158 then d19 (change p 10000 (some 161)) else d18 (change p 10000 (some 161))) = d986 p
  rw [sub916, sub915]
  rfl
theorem sub918 (p : Pattern) : d21 (change p 10000 (some 161)) = d2 p := by
  change (if p 160 then d2 (change p 10000 (some 161)) else d9 (change p 10000 (some 161))) = d2 p
  rw [sub898, sub906]
  simp only [ite_self]
theorem sub919 (p : Pattern) : d22 (change p 10000 (some 161)) = d39 p := by
  change (if p 159 then d21 (change p 10000 (some 161)) else d10 (change p 10000 (some 161))) = d39 p
  rw [sub918, sub907]
  rfl
theorem sub920 (p : Pattern) : d23 (change p 10000 (some 161)) = d2 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d21 (change p 10000 (some 161))) = d2 p
  rw [sub898, sub918]
  simp only [ite_self]
theorem sub921 (p : Pattern) : d24 (change p 10000 (some 161)) = d987 p := by
  change (if p 158 then d23 (change p 10000 (some 161)) else d22 (change p 10000 (some 161))) = d987 p
  rw [sub920, sub919]
  rfl
theorem sub922 (p : Pattern) : d25 (change p 10000 (some 161)) = d988 p := by
  change (if p 139 then d24 (change p 10000 (some 161)) else d20 (change p 10000 (some 161))) = d988 p
  rw [sub921, sub917]
  rfl
theorem sub923 (p : Pattern) : d26 (change p 10000 (some 161)) = d989 p := by
  change (if p 138 then d25 (change p 10000 (some 161)) else d20 (change p 10000 (some 161))) = d989 p
  rw [sub922, sub917]
  rfl
theorem sub924 (p : Pattern) : d27 (change p 10000 (some 161)) = d990 p := by
  change (if p 134 then d26 (change p 10000 (some 161)) else d16 (change p 10000 (some 161))) = d990 p
  rw [sub923, sub913]
  rfl
theorem sub925 (p : Pattern) : d28 (change p 10000 (some 161)) = d991 p := by
  change (if p 133 then d27 (change p 10000 (some 161)) else d16 (change p 10000 (some 161))) = d991 p
  rw [sub924, sub913]
  rfl
theorem sub926 (p : Pattern) : d29 (change p 10000 (some 161)) = d1 p := by
  change d1 (change p 10000 (some 161)) = d1 p
  exact sub905 p
theorem sub927 (p : Pattern) : d30 (change p 10000 (some 161)) = d11 p := by
  change (if p 160 then d2 (change p 10000 (some 161)) else d29 (change p 10000 (some 161))) = d11 p
  rw [sub898, sub926]
  rfl
theorem sub928 (p : Pattern) : d31 (change p 10000 (some 161)) = d992 p := by
  change (if p 159 then d30 (change p 10000 (some 161)) else d4 (change p 10000 (some 161))) = d992 p
  rw [sub927, sub900]
  rfl
theorem sub929 (p : Pattern) : d32 (change p 10000 (some 161)) = d39 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d30 (change p 10000 (some 161))) = d39 p
  rw [sub898, sub927]
  rfl
theorem sub930 (p : Pattern) : d33 (change p 10000 (some 161)) = d993 p := by
  change (if p 158 then d32 (change p 10000 (some 161)) else d31 (change p 10000 (some 161))) = d993 p
  rw [sub929, sub928]
  rfl
theorem sub931 (p : Pattern) : d34 (change p 10000 (some 161)) = d994 p := by
  change (if p 139 then d24 (change p 10000 (some 161)) else d33 (change p 10000 (some 161))) = d994 p
  rw [sub921, sub930]
  rfl
theorem sub932 (p : Pattern) : d35 (change p 10000 (some 161)) = d995 p := by
  change (if p 138 then d34 (change p 10000 (some 161)) else d33 (change p 10000 (some 161))) = d995 p
  rw [sub931, sub930]
  rfl
theorem sub933 (p : Pattern) : d36 (change p 10000 (some 161)) = d996 p := by
  change (if p 134 then d35 (change p 10000 (some 161)) else d16 (change p 10000 (some 161))) = d996 p
  rw [sub932, sub913]
  rfl
theorem sub934 (p : Pattern) : d37 (change p 10000 (some 161)) = d37 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d5 (change p 10000 (some 161))) = d37 p
  rw [sub898, sub901]
  rfl
theorem sub935 (p : Pattern) : d38 (change p 10000 (some 161)) = d697 p := by
  change (if p 158 then d37 (change p 10000 (some 161)) else d6 (change p 10000 (some 161))) = d697 p
  rw [sub934, sub902]
  rfl
theorem sub936 (p : Pattern) : d39 (change p 10000 (some 161)) = d39 p := by
  change (if p 159 then d2 (change p 10000 (some 161)) else d11 (change p 10000 (some 161))) = d39 p
  rw [sub898, sub908]
  rfl
theorem sub937 (p : Pattern) : d40 (change p 10000 (some 161)) = d698 p := by
  change (if p 158 then d39 (change p 10000 (some 161)) else d12 (change p 10000 (some 161))) = d698 p
  rw [sub936, sub909]
  rfl
theorem sub938 (p : Pattern) : d41 (change p 10000 (some 161)) = d699 p := by
  change (if p 139 then d40 (change p 10000 (some 161)) else d38 (change p 10000 (some 161))) = d699 p
  rw [sub937, sub935]
  rfl
theorem sub939 (p : Pattern) : d42 (change p 10000 (some 161)) = d700 p := by
  change (if p 138 then d41 (change p 10000 (some 161)) else d38 (change p 10000 (some 161))) = d700 p
  rw [sub938, sub935]
  rfl
theorem sub940 (p : Pattern) : d43 (change p 10000 (some 161)) = d990 p := by
  change (if p 134 then d26 (change p 10000 (some 161)) else d42 (change p 10000 (some 161))) = d990 p
  rw [sub923, sub939]
  rfl
theorem sub941 (p : Pattern) : d44 (change p 10000 (some 161)) = d997 p := by
  change (if p 133 then d43 (change p 10000 (some 161)) else d36 (change p 10000 (some 161))) = d997 p
  rw [sub940, sub933]
  rfl
theorem sub942 (p : Pattern) : d45 (change p 10000 (some 161)) = d998 p := by
  change (if p 132 then d44 (change p 10000 (some 161)) else d28 (change p 10000 (some 161))) = d998 p
  rw [sub941, sub925]
  rfl
theorem sub943 (p : Pattern) : d46 (change p 10000 (some 161)) = d999 p := by
  change (if p 134 then d25 (change p 10000 (some 161)) else d15 (change p 10000 (some 161))) = d999 p
  rw [sub922, sub912]
  rfl
theorem sub944 (p : Pattern) : d47 (change p 10000 (some 161)) = d1000 p := by
  change (if p 133 then d46 (change p 10000 (some 161)) else d15 (change p 10000 (some 161))) = d1000 p
  rw [sub943, sub912]
  rfl
theorem sub945 (p : Pattern) : d48 (change p 10000 (some 161)) = d1001 p := by
  change (if p 134 then d34 (change p 10000 (some 161)) else d15 (change p 10000 (some 161))) = d1001 p
  rw [sub931, sub912]
  rfl
theorem sub946 (p : Pattern) : d49 (change p 10000 (some 161)) = d999 p := by
  change (if p 134 then d25 (change p 10000 (some 161)) else d41 (change p 10000 (some 161))) = d999 p
  rw [sub922, sub938]
  rfl
theorem sub947 (p : Pattern) : d50 (change p 10000 (some 161)) = d1002 p := by
  change (if p 133 then d49 (change p 10000 (some 161)) else d48 (change p 10000 (some 161))) = d1002 p
  rw [sub946, sub945]
  rfl
theorem sub948 (p : Pattern) : d51 (change p 10000 (some 161)) = d1003 p := by
  change (if p 132 then d50 (change p 10000 (some 161)) else d47 (change p 10000 (some 161))) = d1003 p
  rw [sub947, sub944]
  rfl
theorem sub949 (p : Pattern) : d52 (change p 10000 (some 161)) = d701 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d8 (change p 10000 (some 161))) = d701 p
  rw [sub898, sub904]
  rfl
theorem sub950 (p : Pattern) : d53 (change p 10000 (some 161)) = d702 p := by
  change (if p 138 then d52 (change p 10000 (some 161)) else d15 (change p 10000 (some 161))) = d702 p
  rw [sub949, sub912]
  rfl
theorem sub951 (p : Pattern) : d54 (change p 10000 (some 161)) = d1004 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d20 (change p 10000 (some 161))) = d1004 p
  rw [sub898, sub917]
  rfl
theorem sub952 (p : Pattern) : d55 (change p 10000 (some 161)) = d1005 p := by
  change (if p 138 then d54 (change p 10000 (some 161)) else d25 (change p 10000 (some 161))) = d1005 p
  rw [sub951, sub922]
  rfl
theorem sub953 (p : Pattern) : d56 (change p 10000 (some 161)) = d1006 p := by
  change (if p 134 then d55 (change p 10000 (some 161)) else d53 (change p 10000 (some 161))) = d1006 p
  rw [sub952, sub950]
  rfl
theorem sub954 (p : Pattern) : d57 (change p 10000 (some 161)) = d1007 p := by
  change (if p 133 then d56 (change p 10000 (some 161)) else d53 (change p 10000 (some 161))) = d1007 p
  rw [sub953, sub950]
  rfl
theorem sub955 (p : Pattern) : d58 (change p 10000 (some 161)) = d1008 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d33 (change p 10000 (some 161))) = d1008 p
  rw [sub898, sub930]
  rfl
theorem sub956 (p : Pattern) : d59 (change p 10000 (some 161)) = d1009 p := by
  change (if p 138 then d58 (change p 10000 (some 161)) else d34 (change p 10000 (some 161))) = d1009 p
  rw [sub955, sub931]
  rfl
theorem sub957 (p : Pattern) : d60 (change p 10000 (some 161)) = d1010 p := by
  change (if p 134 then d59 (change p 10000 (some 161)) else d53 (change p 10000 (some 161))) = d1010 p
  rw [sub956, sub950]
  rfl
theorem sub958 (p : Pattern) : d61 (change p 10000 (some 161)) = d701 p := by
  change (if p 139 then d2 (change p 10000 (some 161)) else d38 (change p 10000 (some 161))) = d701 p
  rw [sub898, sub935]
  rfl
theorem sub959 (p : Pattern) : d62 (change p 10000 (some 161)) = d702 p := by
  change (if p 138 then d61 (change p 10000 (some 161)) else d41 (change p 10000 (some 161))) = d702 p
  rw [sub958, sub938]
  rfl
end NetHack.Sokoban32Refined
