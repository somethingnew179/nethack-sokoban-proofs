/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions01
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s300 (pattern : Twelve) : d194 (change pattern 12 12) = d194 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d181 (change pattern 12 12)) = d194 pattern
  rw [s20, s298]
  rfl
theorem s301 (pattern : Twelve) : d204 (change pattern 12 12) = d204 pattern := by
  change (if pattern.f then d194 (change pattern 12 12) else d193 (change pattern 12 12)) = d204 pattern
  rw [s300, s299]
  rfl
theorem s302 (pattern : Twelve) : d911 (change pattern 12 12) = d911 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d194 (change pattern 12 12)) = d911 pattern
  rw [s20, s300]
  rfl
theorem s303 (pattern : Twelve) : d915 (change pattern 12 12) = d915 pattern := by
  change (if pattern.e then d911 (change pattern 12 12) else d204 (change pattern 12 12)) = d915 pattern
  rw [s302, s301]
  rfl
theorem s304 (pattern : Twelve) : d196 (change pattern 12 12) = d196 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d183 (change pattern 12 12)) = d196 pattern
  rw [s20, s251]
  rfl
theorem s305 (pattern : Twelve) : d206 (change pattern 12 12) = d206 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d196 (change pattern 12 12)) = d206 pattern
  rw [s20, s304]
  rfl
theorem s306 (pattern : Twelve) : d916 (change pattern 12 12) = d916 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d206 (change pattern 12 12)) = d916 pattern
  rw [s20, s305]
  rfl
theorem s307 (pattern : Twelve) : d919 (change pattern 12 12) = d919 pattern := by
  change (if pattern.j then d916 (change pattern 12 12) else d915 (change pattern 12 12)) = d919 pattern
  rw [s306, s303]
  rfl
theorem s308 (pattern : Twelve) : d920 (change pattern 12 12) = d920 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d916 (change pattern 12 12)) = d920 pattern
  rw [s20, s306]
  rfl
theorem s309 (pattern : Twelve) : d922 (change pattern 12 12) = d922 pattern := by
  change (if pattern.d then d920 (change pattern 12 12) else d919 (change pattern 12 12)) = d922 pattern
  rw [s308, s307]
  rfl
theorem s310 (pattern : Twelve) : d923 (change pattern 12 12) = d923 pattern := by
  change (if pattern.c then d922 (change pattern 12 12) else d921 (change pattern 12 12)) = d923 pattern
  rw [s309, s295]
  rfl
theorem s311 (pattern : Twelve) : d924 (change pattern 12 12) = d924 pattern := by
  change (if pattern.g then d6 (change pattern 12 12) else d923 (change pattern 12 12)) = d924 pattern
  rw [s20, s310]
  rfl
theorem s312 (pattern : Twelve) : d925 (change pattern 12 12) = d925 pattern := by
  change (if pattern.b then d6 (change pattern 12 12) else d924 (change pattern 12 12)) = d925 pattern
  rw [s20, s311]
  rfl
theorem s313 (pattern : Twelve) : d926 (change pattern 12 12) = d926 pattern := by
  change (if pattern.a then d6 (change pattern 12 12) else d925 (change pattern 12 12)) = d926 pattern
  rw [s20, s312]
  rfl
theorem s314 (pattern : Twelve) : d1355 (change pattern 12 12) = d1355 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d908 (change pattern 12 12)) = d1355 pattern
  rw [s20, s273]
  rfl
theorem s315 (pattern : Twelve) : d1356 (change pattern 12 12) = d1356 pattern := by
  change (if pattern.e then d1355 (change pattern 12 12) else d909 (change pattern 12 12)) = d1356 pattern
  rw [s314, s274]
  rfl
theorem s316 (pattern : Twelve) : d1357 (change pattern 12 12) = d1357 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d910 (change pattern 12 12)) = d1357 pattern
  rw [s20, s286]
  rfl
theorem s317 (pattern : Twelve) : d1359 (change pattern 12 12) = d1359 pattern := by
  change (if pattern.j then d1357 (change pattern 12 12) else d1356 (change pattern 12 12)) = d1359 pattern
  rw [s316, s315]
  rfl
theorem s318 (pattern : Twelve) : d1360 (change pattern 12 12) = d1360 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1357 (change pattern 12 12)) = d1360 pattern
  rw [s20, s316]
  rfl
theorem s319 (pattern : Twelve) : d1362 (change pattern 12 12) = d1362 pattern := by
  change (if pattern.d then d1360 (change pattern 12 12) else d1359 (change pattern 12 12)) = d1362 pattern
  rw [s318, s317]
  rfl
theorem s320 (pattern : Twelve) : d1358 (change pattern 12 12) = d1358 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d911 (change pattern 12 12)) = d1358 pattern
  rw [s20, s302]
  rfl
theorem s321 (pattern : Twelve) : d1361 (change pattern 12 12) = d1361 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1358 (change pattern 12 12)) = d1361 pattern
  rw [s20, s320]
  rfl
theorem s322 (pattern : Twelve) : d1363 (change pattern 12 12) = d1363 pattern := by
  change (if pattern.d then d6 (change pattern 12 12) else d1361 (change pattern 12 12)) = d1363 pattern
  rw [s20, s321]
  rfl
theorem s323 (pattern : Twelve) : d1364 (change pattern 12 12) = d1364 pattern := by
  change (if pattern.c then d1363 (change pattern 12 12) else d1362 (change pattern 12 12)) = d1364 pattern
  rw [s322, s319]
  rfl
theorem s324 (pattern : Twelve) : d1365 (change pattern 12 12) = d1365 pattern := by
  change (if pattern.g then d6 (change pattern 12 12) else d1364 (change pattern 12 12)) = d1365 pattern
  rw [s20, s323]
  rfl
theorem s325 (pattern : Twelve) : d1366 (change pattern 12 12) = d1366 pattern := by
  change (if pattern.b then d6 (change pattern 12 12) else d1365 (change pattern 12 12)) = d1366 pattern
  rw [s20, s324]
  rfl
theorem s326 (pattern : Twelve) : d1367 (change pattern 12 12) = d1367 pattern := by
  change (if pattern.a then d6 (change pattern 12 12) else d1366 (change pattern 12 12)) = d1367 pattern
  rw [s20, s325]
  rfl
theorem s327 (pattern : Twelve) : d1679 (change pattern 12 12) = d1679 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d1355 (change pattern 12 12)) = d1679 pattern
  rw [s20, s314]
  rfl
theorem s328 (pattern : Twelve) : d1680 (change pattern 12 12) = d1680 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1679 (change pattern 12 12)) = d1680 pattern
  rw [s20, s327]
  rfl
theorem s329 (pattern : Twelve) : d1681 (change pattern 12 12) = d1681 pattern := by
  change (if pattern.d then d6 (change pattern 12 12) else d1680 (change pattern 12 12)) = d1681 pattern
  rw [s20, s328]
  rfl
theorem s330 (pattern : Twelve) : d1682 (change pattern 12 12) = d1682 pattern := by
  change (if pattern.c then d6 (change pattern 12 12) else d1681 (change pattern 12 12)) = d1682 pattern
  rw [s20, s329]
  rfl
theorem s331 (pattern : Twelve) : d1683 (change pattern 12 12) = d1683 pattern := by
  change (if pattern.g then d6 (change pattern 12 12) else d1682 (change pattern 12 12)) = d1683 pattern
  rw [s20, s330]
  rfl
theorem s332 (pattern : Twelve) : d1684 (change pattern 12 12) = d1684 pattern := by
  change (if pattern.b then d6 (change pattern 12 12) else d1683 (change pattern 12 12)) = d1684 pattern
  rw [s20, s331]
  rfl
theorem s333 (pattern : Twelve) : d1685 (change pattern 12 12) = d1685 pattern := by
  change (if pattern.a then d6 (change pattern 12 12) else d1684 (change pattern 12 12)) = d1685 pattern
  rw [s20, s332]
  rfl
theorem s334 (pattern : Twelve) : d26 (change pattern 12 12) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 12) else d0 (change pattern 12 12)) = d26 pattern
  rw [s1, s0]
  rfl
theorem s335 (pattern : Twelve) : d50 (change pattern 12 12) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 12) else d26 (change pattern 12 12)) = d50 pattern
  rw [s4, s334]
  rfl
theorem s336 (pattern : Twelve) : d72 (change pattern 12 12) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 12 12) else d0 (change pattern 12 12)) = d72 pattern
  rw [s335, s0]
  rfl
theorem s337 (pattern : Twelve) : d18 (change pattern 12 12) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 12 12) else d8 (change pattern 12 12)) = d18 pattern
  rw [s28, s96]
  rfl
theorem s338 (pattern : Twelve) : d28 (change pattern 12 12) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 12 12) else d17 (change pattern 12 12)) = d28 pattern
  rw [s337, s3]
  rfl
theorem s339 (pattern : Twelve) : d51 (change pattern 12 12) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 12 12) else d28 (change pattern 12 12)) = d51 pattern
  rw [s110, s338]
  rfl
theorem s340 (pattern : Twelve) : d73 (change pattern 12 12) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 12 12) else d0 (change pattern 12 12)) = d73 pattern
  rw [s339, s0]
  rfl
theorem s341 (pattern : Twelve) : d91 (change pattern 12 12) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 12 12) else d72 (change pattern 12 12)) = d91 pattern
  rw [s340, s336]
  rfl
theorem s342 (pattern : Twelve) : d31 (change pattern 12 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 12 12) else d0 (change pattern 12 12)) = d31 pattern
  rw [s156, s0]
  rfl
theorem s343 (pattern : Twelve) : d52 (change pattern 12 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 12 12) else d30 (change pattern 12 12)) = d52 pattern
  rw [s342, s25]
  rfl
theorem s344 (pattern : Twelve) : d32 (change pattern 12 12) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 12 12) else d17 (change pattern 12 12)) = d32 pattern
  rw [s58, s3]
  rfl
theorem s345 (pattern : Twelve) : d53 (change pattern 12 12) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 12 12) else d30 (change pattern 12 12)) = d53 pattern
  rw [s344, s25]
  rfl
theorem s346 (pattern : Twelve) : d74 (change pattern 12 12) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 12 12) else d52 (change pattern 12 12)) = d74 pattern
  rw [s345, s343]
  rfl
theorem s347 (pattern : Twelve) : d33 (change pattern 12 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d0 (change pattern 12 12)) = d33 pattern
  rw [s166, s0]
  rfl
theorem s348 (pattern : Twelve) : d54 (change pattern 12 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 12 12) else d30 (change pattern 12 12)) = d54 pattern
  rw [s347, s25]
  rfl
theorem s349 (pattern : Twelve) : d55 (change pattern 12 12) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 12) else d34 (change pattern 12 12)) = d55 pattern
  rw [s110, s30]
  rfl
theorem s350 (pattern : Twelve) : d75 (change pattern 12 12) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 12 12) else d54 (change pattern 12 12)) = d75 pattern
  rw [s349, s348]
  rfl
theorem s351 (pattern : Twelve) : d92 (change pattern 12 12) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 12 12) else d74 (change pattern 12 12)) = d92 pattern
  rw [s350, s346]
  rfl
theorem s352 (pattern : Twelve) : d102 (change pattern 12 12) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 12 12) else d91 (change pattern 12 12)) = d102 pattern
  rw [s351, s341]
  rfl
theorem s353 (pattern : Twelve) : d76 (change pattern 12 12) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 12 12) else d0 (change pattern 12 12)) = d76 pattern
  rw [s349, s0]
  rfl
theorem s354 (pattern : Twelve) : d93 (change pattern 12 12) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 12 12) else d72 (change pattern 12 12)) = d93 pattern
  rw [s353, s336]
  rfl
theorem s355 (pattern : Twelve) : d57 (change pattern 12 12) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 12 12) else d30 (change pattern 12 12)) = d57 pattern
  rw [s34, s25]
  rfl
theorem s356 (pattern : Twelve) : d77 (change pattern 12 12) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 12 12) else d56 (change pattern 12 12)) = d77 pattern
  rw [s355, s27]
  rfl
theorem s357 (pattern : Twelve) : d78 (change pattern 12 12) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 12 12) else d56 (change pattern 12 12)) = d78 pattern
  rw [s349, s27]
  rfl
theorem s358 (pattern : Twelve) : d94 (change pattern 12 12) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 12 12) else d77 (change pattern 12 12)) = d94 pattern
  rw [s357, s356]
  rfl
theorem s359 (pattern : Twelve) : d103 (change pattern 12 12) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 12 12) else d93 (change pattern 12 12)) = d103 pattern
  rw [s358, s354]
  rfl
theorem s360 (pattern : Twelve) : d110 (change pattern 12 12) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 12 12) else d102 (change pattern 12 12)) = d110 pattern
  rw [s359, s352]
  rfl
theorem s361 (pattern : Twelve) : d37 (change pattern 12 12) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d17 (change pattern 12 12)) = d37 pattern
  rw [s11, s3]
  rfl
theorem s362 (pattern : Twelve) : d58 (change pattern 12 12) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 12 12) else d30 (change pattern 12 12)) = d58 pattern
  rw [s361, s25]
  rfl
theorem s363 (pattern : Twelve) : d79 (change pattern 12 12) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 12 12) else d30 (change pattern 12 12)) = d79 pattern
  rw [s362, s25]
  rfl
theorem s364 (pattern : Twelve) : d80 (change pattern 12 12) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 12 12) else d30 (change pattern 12 12)) = d80 pattern
  rw [s349, s25]
  rfl
theorem s365 (pattern : Twelve) : d95 (change pattern 12 12) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 12 12) else d79 (change pattern 12 12)) = d95 pattern
  rw [s364, s363]
  rfl
theorem s366 (pattern : Twelve) : d60 (change pattern 12 12) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 12 12) else d38 (change pattern 12 12)) = d60 pattern
  rw [s54, s44]
  rfl
theorem s367 (pattern : Twelve) : d81 (change pattern 12 12) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 12 12) else d59 (change pattern 12 12)) = d81 pattern
  rw [s366, s46]
  rfl
theorem s368 (pattern : Twelve) : d61 (change pattern 12 12) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 12 12) else d41 (change pattern 12 12)) = d61 pattern
  rw [s21, s49]
  rfl
theorem s369 (pattern : Twelve) : d82 (change pattern 12 12) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 12 12) else d59 (change pattern 12 12)) = d82 pattern
  rw [s368, s46]
  rfl
theorem s370 (pattern : Twelve) : d96 (change pattern 12 12) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 12 12) else d81 (change pattern 12 12)) = d96 pattern
  rw [s369, s367]
  rfl
theorem s371 (pattern : Twelve) : d104 (change pattern 12 12) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 12 12) else d95 (change pattern 12 12)) = d104 pattern
  rw [s370, s365]
  rfl
theorem s372 (pattern : Twelve) : d105 (change pattern 12 12) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d94 (change pattern 12 12)) = d105 pattern
  rw [s20, s358]
  rfl
theorem s373 (pattern : Twelve) : d111 (change pattern 12 12) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 12 12) else d104 (change pattern 12 12)) = d111 pattern
  rw [s372, s371]
  rfl
theorem s374 (pattern : Twelve) : d114 (change pattern 12 12) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 12 12) else d110 (change pattern 12 12)) = d114 pattern
  rw [s373, s360]
  rfl
theorem s375 (pattern : Twelve) : d97 (change pattern 12 12) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 12 12) else d72 (change pattern 12 12)) = d97 pattern
  rw [s364, s336]
  rfl
theorem s376 (pattern : Twelve) : d43 (change pattern 12 12) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 12 12) else d1 (change pattern 12 12)) = d43 pattern
  rw [s58, s1]
  rfl
theorem s377 (pattern : Twelve) : d62 (change pattern 12 12) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 12 12) else d30 (change pattern 12 12)) = d62 pattern
  rw [s376, s25]
  rfl
theorem s378 (pattern : Twelve) : d83 (change pattern 12 12) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 12 12) else d52 (change pattern 12 12)) = d83 pattern
  rw [s377, s343]
  rfl
theorem s379 (pattern : Twelve) : d44 (change pattern 12 12) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 12 12) else d2 (change pattern 12 12)) = d44 pattern
  rw [s166, s9]
  rfl
theorem s380 (pattern : Twelve) : d63 (change pattern 12 12) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 12 12) else d30 (change pattern 12 12)) = d63 pattern
  rw [s379, s25]
  rfl
theorem s381 (pattern : Twelve) : d64 (change pattern 12 12) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 12 12) else d34 (change pattern 12 12)) = d64 pattern
  rw [s54, s30]
  rfl
theorem s382 (pattern : Twelve) : d84 (change pattern 12 12) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 12 12) else d63 (change pattern 12 12)) = d84 pattern
  rw [s381, s380]
  rfl
theorem s383 (pattern : Twelve) : d98 (change pattern 12 12) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 12 12) else d83 (change pattern 12 12)) = d98 pattern
  rw [s382, s378]
  rfl
theorem s384 (pattern : Twelve) : d106 (change pattern 12 12) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 12 12) else d97 (change pattern 12 12)) = d106 pattern
  rw [s383, s375]
  rfl
theorem s385 (pattern : Twelve) : d65 (change pattern 12 12) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 12 12) else d30 (change pattern 12 12)) = d65 pattern
  rw [s71, s25]
  rfl
theorem s386 (pattern : Twelve) : d85 (change pattern 12 12) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 12 12) else d56 (change pattern 12 12)) = d85 pattern
  rw [s385, s27]
  rfl
theorem s387 (pattern : Twelve) : d66 (change pattern 12 12) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 12 12) else d30 (change pattern 12 12)) = d66 pattern
  rw [s45, s25]
  rfl
theorem s388 (pattern : Twelve) : d86 (change pattern 12 12) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 12 12) else d66 (change pattern 12 12)) = d86 pattern
  rw [s381, s387]
  rfl
theorem s389 (pattern : Twelve) : d99 (change pattern 12 12) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 12 12) else d85 (change pattern 12 12)) = d99 pattern
  rw [s388, s386]
  rfl
theorem s390 (pattern : Twelve) : d107 (change pattern 12 12) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 12 12) else d97 (change pattern 12 12)) = d107 pattern
  rw [s389, s375]
  rfl
theorem s391 (pattern : Twelve) : d112 (change pattern 12 12) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 12 12) else d106 (change pattern 12 12)) = d112 pattern
  rw [s390, s384]
  rfl
theorem s392 (pattern : Twelve) : d67 (change pattern 12 12) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 12 12) else d30 (change pattern 12 12)) = d67 pattern
  rw [s78, s25]
  rfl
theorem s393 (pattern : Twelve) : d87 (change pattern 12 12) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 12 12) else d30 (change pattern 12 12)) = d87 pattern
  rw [s392, s25]
  rfl
theorem s394 (pattern : Twelve) : d68 (change pattern 12 12) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 12 12) else d30 (change pattern 12 12)) = d68 pattern
  rw [s44, s25]
  rfl
theorem s395 (pattern : Twelve) : d88 (change pattern 12 12) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 12 12) else d68 (change pattern 12 12)) = d88 pattern
  rw [s381, s394]
  rfl
theorem s396 (pattern : Twelve) : d100 (change pattern 12 12) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 12 12) else d87 (change pattern 12 12)) = d100 pattern
  rw [s395, s393]
  rfl
theorem s397 (pattern : Twelve) : d69 (change pattern 12 12) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 12 12) else d38 (change pattern 12 12)) = d69 pattern
  rw [s84, s44]
  rfl
theorem s398 (pattern : Twelve) : d89 (change pattern 12 12) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 12 12) else d59 (change pattern 12 12)) = d89 pattern
  rw [s397, s46]
  rfl
theorem s399 (pattern : Twelve) : d70 (change pattern 12 12) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 12 12) else d38 (change pattern 12 12)) = d70 pattern
  rw [s87, s44]
  rfl
theorem s400 (pattern : Twelve) : d71 (change pattern 12 12) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 12 12) else d41 (change pattern 12 12)) = d71 pattern
  rw [s143, s49]
  rfl
theorem s401 (pattern : Twelve) : d90 (change pattern 12 12) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 12 12) else d70 (change pattern 12 12)) = d90 pattern
  rw [s400, s399]
  rfl
theorem s402 (pattern : Twelve) : d101 (change pattern 12 12) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 12 12) else d89 (change pattern 12 12)) = d101 pattern
  rw [s401, s398]
  rfl
theorem s403 (pattern : Twelve) : d108 (change pattern 12 12) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 12 12) else d100 (change pattern 12 12)) = d108 pattern
  rw [s402, s396]
  rfl
theorem s404 (pattern : Twelve) : d109 (change pattern 12 12) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d99 (change pattern 12 12)) = d109 pattern
  rw [s20, s389]
  rfl
theorem s405 (pattern : Twelve) : d113 (change pattern 12 12) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 12 12) else d108 (change pattern 12 12)) = d113 pattern
  rw [s404, s403]
  rfl
theorem s406 (pattern : Twelve) : d115 (change pattern 12 12) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 12 12) else d112 (change pattern 12 12)) = d115 pattern
  rw [s405, s391]
  rfl
theorem s407 (pattern : Twelve) : d116 (change pattern 12 12) = d116 pattern := by
  change (if pattern.g then d115 (change pattern 12 12) else d114 (change pattern 12 12)) = d116 pattern
  rw [s406, s374]
  rfl
theorem s408 (pattern : Twelve) : d0 (change pattern 12 3) = d0 pattern := by
  rfl
theorem s409 (pattern : Twelve) : d1 (change pattern 12 3) = d1 pattern := by
  rfl
theorem s410 (pattern : Twelve) : d26 (change pattern 12 3) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 3) else d0 (change pattern 12 3)) = d26 pattern
  rw [s409, s408]
  rfl
theorem s411 (pattern : Twelve) : d7 (change pattern 12 3) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 3) else d0 (change pattern 12 3)) = d7 pattern
  rw [s409, s408]
  rfl
theorem s412 (pattern : Twelve) : d17 (change pattern 12 3) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 3) else d0 (change pattern 12 3)) = d17 pattern
  rw [s411, s408]
  rfl
theorem s413 (pattern : Twelve) : d27 (change pattern 12 3) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 3) else d17 (change pattern 12 3)) = d27 pattern
  rw [s409, s412]
  rfl
theorem s414 (pattern : Twelve) : d50 (change pattern 12 3) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 3) else d26 (change pattern 12 3)) = d50 pattern
  rw [s413, s410]
  rfl
theorem s415 (pattern : Twelve) : d72 (change pattern 12 3) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 12 3) else d0 (change pattern 12 3)) = d72 pattern
  rw [s414, s408]
  rfl
theorem s416 (pattern : Twelve) : d2 (change pattern 12 3) = d2 pattern := by
  rfl
theorem s417 (pattern : Twelve) : d3 (change pattern 12 3) = d3 pattern := by
  rfl
theorem s418 (pattern : Twelve) : d9 (change pattern 12 3) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 3) else d2 (change pattern 12 3)) = d9 pattern
  rw [s417, s416]
  rfl
theorem s419 (pattern : Twelve) : d23 (change pattern 12 3) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 3) else d2 (change pattern 12 3)) = d23 pattern
  rw [s418, s416]
  rfl
theorem s420 (pattern : Twelve) : d34 (change pattern 12 3) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 3) else d17 (change pattern 12 3)) = d34 pattern
  rw [s419, s412]
  rfl
theorem s421 (pattern : Twelve) : d10 (change pattern 12 3) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 3) else d0 (change pattern 12 3)) = d10 pattern
  rw [s416, s408]
  rfl
theorem s422 (pattern : Twelve) : d11 (change pattern 12 3) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 3) else d1 (change pattern 12 3)) = d11 pattern
  rw [s417, s409]
  rfl
theorem s423 (pattern : Twelve) : d19 (change pattern 12 3) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 3) else d10 (change pattern 12 3)) = d19 pattern
  rw [s422, s421]
  rfl
theorem s424 (pattern : Twelve) : d6 (change pattern 12 3) = d6 pattern := by
  rfl
theorem s425 (pattern : Twelve) : d29 (change pattern 12 3) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d19 (change pattern 12 3)) = d29 pattern
  rw [s424, s423]
  rfl
theorem s426 (pattern : Twelve) : d55 (change pattern 12 3) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 3) else d34 (change pattern 12 3)) = d55 pattern
  rw [s425, s420]
  rfl
theorem s427 (pattern : Twelve) : d76 (change pattern 12 3) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 12 3) else d0 (change pattern 12 3)) = d76 pattern
  rw [s426, s408]
  rfl
theorem s428 (pattern : Twelve) : d93 (change pattern 12 3) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 12 3) else d72 (change pattern 12 3)) = d93 pattern
  rw [s427, s415]
  rfl
theorem s429 (pattern : Twelve) : d30 (change pattern 12 3) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 3) else d0 (change pattern 12 3)) = d30 pattern
  rw [s416, s408]
  rfl
theorem s430 (pattern : Twelve) : d35 (change pattern 12 3) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d0 (change pattern 12 3)) = d35 pattern
  rw [s424, s408]
  rfl
theorem s431 (pattern : Twelve) : d56 (change pattern 12 3) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 3) else d30 (change pattern 12 3)) = d56 pattern
  rw [s430, s429]
  rfl
theorem s432 (pattern : Twelve) : d36 (change pattern 12 3) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d17 (change pattern 12 3)) = d36 pattern
  rw [s424, s412]
  rfl
theorem s433 (pattern : Twelve) : d57 (change pattern 12 3) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 12 3) else d30 (change pattern 12 3)) = d57 pattern
  rw [s432, s429]
  rfl
theorem s434 (pattern : Twelve) : d77 (change pattern 12 3) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 12 3) else d56 (change pattern 12 3)) = d77 pattern
  rw [s433, s431]
  rfl
theorem s435 (pattern : Twelve) : d78 (change pattern 12 3) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 12 3) else d56 (change pattern 12 3)) = d78 pattern
  rw [s426, s431]
  rfl
theorem s436 (pattern : Twelve) : d94 (change pattern 12 3) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 12 3) else d77 (change pattern 12 3)) = d94 pattern
  rw [s435, s434]
  rfl
theorem s437 (pattern : Twelve) : d103 (change pattern 12 3) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 12 3) else d93 (change pattern 12 3)) = d103 pattern
  rw [s436, s428]
  rfl
theorem s438 (pattern : Twelve) : d110 (change pattern 12 3) = d103 pattern := by
  change d103 (change pattern 12 3) = d103 pattern
  exact s437 pattern
theorem s439 (pattern : Twelve) : d105 (change pattern 12 3) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 12 3) else d94 (change pattern 12 3)) = d105 pattern
  rw [s424, s436]
  rfl
theorem s440 (pattern : Twelve) : d111 (change pattern 12 3) = d105 pattern := by
  change d105 (change pattern 12 3) = d105 pattern
  exact s439 pattern
theorem s441 (pattern : Twelve) : d114 (change pattern 12 3) = d1880 pattern := by
  change (if pattern.c then d111 (change pattern 12 3) else d110 (change pattern 12 3)) = d1880 pattern
  rw [s440, s438]
  rfl
theorem s442 (pattern : Twelve) : d80 (change pattern 12 3) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 12 3) else d30 (change pattern 12 3)) = d80 pattern
  rw [s426, s429]
  rfl
theorem s443 (pattern : Twelve) : d97 (change pattern 12 3) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 12 3) else d72 (change pattern 12 3)) = d97 pattern
  rw [s442, s415]
  rfl
theorem s444 (pattern : Twelve) : d45 (change pattern 12 3) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d1 (change pattern 12 3)) = d45 pattern
  rw [s424, s409]
  rfl
theorem s445 (pattern : Twelve) : d65 (change pattern 12 3) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 12 3) else d30 (change pattern 12 3)) = d65 pattern
  rw [s444, s429]
  rfl
theorem s446 (pattern : Twelve) : d85 (change pattern 12 3) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 12 3) else d56 (change pattern 12 3)) = d85 pattern
  rw [s445, s431]
  rfl
theorem s447 (pattern : Twelve) : d39 (change pattern 12 3) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d2 (change pattern 12 3)) = d39 pattern
  rw [s424, s416]
  rfl
theorem s448 (pattern : Twelve) : d66 (change pattern 12 3) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 12 3) else d30 (change pattern 12 3)) = d66 pattern
  rw [s447, s429]
  rfl
theorem s449 (pattern : Twelve) : d40 (change pattern 12 3) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 3) else d23 (change pattern 12 3)) = d40 pattern
  rw [s424, s419]
  rfl
end NetHack.Sokoban21.Diagram
