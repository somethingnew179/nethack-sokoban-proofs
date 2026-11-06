/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions41
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6300 (pattern : Twelve) : d34 (change pattern 12 0) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 12 0) else d17 (change pattern 12 0)) = d34 pattern
  rw [s6299, s6265]
  rfl
theorem s6301 (pattern : Twelve) : d55 (change pattern 12 0) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 12 0) else d34 (change pattern 12 0)) = d55 pattern
  rw [s6279, s6300]
  rfl
theorem s6302 (pattern : Twelve) : d75 (change pattern 12 0) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 12 0) else d54 (change pattern 12 0)) = d75 pattern
  rw [s6301, s6298]
  rfl
theorem s6303 (pattern : Twelve) : d92 (change pattern 12 0) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 12 0) else d74 (change pattern 12 0)) = d92 pattern
  rw [s6302, s6295]
  rfl
theorem s6304 (pattern : Twelve) : d102 (change pattern 12 0) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 12 0) else d91 (change pattern 12 0)) = d102 pattern
  rw [s6303, s6282]
  rfl
theorem s6305 (pattern : Twelve) : d76 (change pattern 12 0) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 12 0) else d0 (change pattern 12 0)) = d76 pattern
  rw [s6301, s6261]
  rfl
theorem s6306 (pattern : Twelve) : d93 (change pattern 12 0) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 12 0) else d72 (change pattern 12 0)) = d93 pattern
  rw [s6305, s6268]
  rfl
theorem s6307 (pattern : Twelve) : d35 (change pattern 12 0) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d0 (change pattern 12 0)) = d35 pattern
  rw [s6278, s6261]
  rfl
theorem s6308 (pattern : Twelve) : d56 (change pattern 12 0) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 0) else d30 (change pattern 12 0)) = d56 pattern
  rw [s6307, s6283]
  rfl
theorem s6309 (pattern : Twelve) : d36 (change pattern 12 0) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d17 (change pattern 12 0)) = d36 pattern
  rw [s6278, s6265]
  rfl
theorem s6310 (pattern : Twelve) : d57 (change pattern 12 0) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 12 0) else d30 (change pattern 12 0)) = d57 pattern
  rw [s6309, s6283]
  rfl
theorem s6311 (pattern : Twelve) : d77 (change pattern 12 0) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 12 0) else d56 (change pattern 12 0)) = d77 pattern
  rw [s6310, s6308]
  rfl
theorem s6312 (pattern : Twelve) : d78 (change pattern 12 0) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 12 0) else d56 (change pattern 12 0)) = d78 pattern
  rw [s6301, s6308]
  rfl
theorem s6313 (pattern : Twelve) : d94 (change pattern 12 0) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 12 0) else d77 (change pattern 12 0)) = d94 pattern
  rw [s6312, s6311]
  rfl
theorem s6314 (pattern : Twelve) : d103 (change pattern 12 0) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 12 0) else d93 (change pattern 12 0)) = d103 pattern
  rw [s6313, s6306]
  rfl
theorem s6315 (pattern : Twelve) : d110 (change pattern 12 0) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 12 0) else d102 (change pattern 12 0)) = d110 pattern
  rw [s6314, s6304]
  rfl
theorem s6316 (pattern : Twelve) : d37 (change pattern 12 0) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d17 (change pattern 12 0)) = d37 pattern
  rw [s6271, s6265]
  rfl
theorem s6317 (pattern : Twelve) : d58 (change pattern 12 0) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 12 0) else d30 (change pattern 12 0)) = d58 pattern
  rw [s6316, s6283]
  rfl
theorem s6318 (pattern : Twelve) : d79 (change pattern 12 0) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 12 0) else d30 (change pattern 12 0)) = d79 pattern
  rw [s6317, s6283]
  rfl
theorem s6319 (pattern : Twelve) : d80 (change pattern 12 0) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 12 0) else d30 (change pattern 12 0)) = d80 pattern
  rw [s6301, s6283]
  rfl
theorem s6320 (pattern : Twelve) : d95 (change pattern 12 0) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 12 0) else d79 (change pattern 12 0)) = d95 pattern
  rw [s6319, s6318]
  rfl
theorem s6321 (pattern : Twelve) : d38 (change pattern 12 0) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 0) else d2 (change pattern 12 0)) = d38 pattern
  rw [s6286, s6269]
  rfl
theorem s6322 (pattern : Twelve) : d39 (change pattern 12 0) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d2 (change pattern 12 0)) = d39 pattern
  rw [s6278, s6269]
  rfl
theorem s6323 (pattern : Twelve) : d59 (change pattern 12 0) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 12 0) else d38 (change pattern 12 0)) = d59 pattern
  rw [s6322, s6321]
  rfl
theorem s6324 (pattern : Twelve) : d40 (change pattern 12 0) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d23 (change pattern 12 0)) = d40 pattern
  rw [s6278, s6299]
  rfl
theorem s6325 (pattern : Twelve) : d60 (change pattern 12 0) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 12 0) else d38 (change pattern 12 0)) = d60 pattern
  rw [s6324, s6321]
  rfl
theorem s6326 (pattern : Twelve) : d81 (change pattern 12 0) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 12 0) else d59 (change pattern 12 0)) = d81 pattern
  rw [s6325, s6323]
  rfl
theorem s6327 (pattern : Twelve) : d15 (change pattern 12 0) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 0) else d4 (change pattern 12 0)) = d15 pattern
  rw [s6284, s6286]
  rfl
theorem s6328 (pattern : Twelve) : d24 (change pattern 12 0) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 12 0) else d4 (change pattern 12 0)) = d24 pattern
  rw [s6327, s6286]
  rfl
theorem s6329 (pattern : Twelve) : d41 (change pattern 12 0) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 12 0) else d23 (change pattern 12 0)) = d41 pattern
  rw [s6328, s6299]
  rfl
theorem s6330 (pattern : Twelve) : d16 (change pattern 12 0) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 0) else d2 (change pattern 12 0)) = d16 pattern
  rw [s6286, s6269]
  rfl
theorem s6331 (pattern : Twelve) : d25 (change pattern 12 0) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 12 0) else d16 (change pattern 12 0)) = d25 pattern
  rw [s6285, s6330]
  rfl
theorem s6332 (pattern : Twelve) : d42 (change pattern 12 0) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d25 (change pattern 12 0)) = d42 pattern
  rw [s6278, s6331]
  rfl
theorem s6333 (pattern : Twelve) : d61 (change pattern 12 0) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 12 0) else d41 (change pattern 12 0)) = d61 pattern
  rw [s6332, s6329]
  rfl
theorem s6334 (pattern : Twelve) : d82 (change pattern 12 0) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 12 0) else d59 (change pattern 12 0)) = d82 pattern
  rw [s6333, s6323]
  rfl
theorem s6335 (pattern : Twelve) : d96 (change pattern 12 0) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 12 0) else d81 (change pattern 12 0)) = d96 pattern
  rw [s6334, s6326]
  rfl
theorem s6336 (pattern : Twelve) : d104 (change pattern 12 0) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 12 0) else d95 (change pattern 12 0)) = d104 pattern
  rw [s6335, s6320]
  rfl
theorem s6337 (pattern : Twelve) : d105 (change pattern 12 0) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d94 (change pattern 12 0)) = d105 pattern
  rw [s6278, s6313]
  rfl
theorem s6338 (pattern : Twelve) : d111 (change pattern 12 0) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 12 0) else d104 (change pattern 12 0)) = d111 pattern
  rw [s6337, s6336]
  rfl
theorem s6339 (pattern : Twelve) : d114 (change pattern 12 0) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 12 0) else d110 (change pattern 12 0)) = d114 pattern
  rw [s6338, s6315]
  rfl
theorem s6340 (pattern : Twelve) : d97 (change pattern 12 0) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 12 0) else d72 (change pattern 12 0)) = d97 pattern
  rw [s6319, s6268]
  rfl
theorem s6341 (pattern : Twelve) : d43 (change pattern 12 0) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 12 0) else d1 (change pattern 12 0)) = d43 pattern
  rw [s6292, s6262]
  rfl
theorem s6342 (pattern : Twelve) : d62 (change pattern 12 0) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 12 0) else d30 (change pattern 12 0)) = d62 pattern
  rw [s6341, s6283]
  rfl
theorem s6343 (pattern : Twelve) : d83 (change pattern 12 0) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 12 0) else d52 (change pattern 12 0)) = d83 pattern
  rw [s6342, s6290]
  rfl
theorem s6344 (pattern : Twelve) : d44 (change pattern 12 0) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d2 (change pattern 12 0)) = d44 pattern
  rw [s6296, s6269]
  rfl
theorem s6345 (pattern : Twelve) : d63 (change pattern 12 0) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 12 0) else d30 (change pattern 12 0)) = d63 pattern
  rw [s6344, s6283]
  rfl
theorem s6346 (pattern : Twelve) : d64 (change pattern 12 0) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 12 0) else d34 (change pattern 12 0)) = d64 pattern
  rw [s6324, s6300]
  rfl
theorem s6347 (pattern : Twelve) : d84 (change pattern 12 0) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 12 0) else d63 (change pattern 12 0)) = d84 pattern
  rw [s6346, s6345]
  rfl
theorem s6348 (pattern : Twelve) : d98 (change pattern 12 0) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 12 0) else d83 (change pattern 12 0)) = d98 pattern
  rw [s6347, s6343]
  rfl
theorem s6349 (pattern : Twelve) : d106 (change pattern 12 0) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 12 0) else d97 (change pattern 12 0)) = d106 pattern
  rw [s6348, s6340]
  rfl
theorem s6350 (pattern : Twelve) : d45 (change pattern 12 0) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d1 (change pattern 12 0)) = d45 pattern
  rw [s6278, s6262]
  rfl
theorem s6351 (pattern : Twelve) : d65 (change pattern 12 0) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 12 0) else d30 (change pattern 12 0)) = d65 pattern
  rw [s6350, s6283]
  rfl
theorem s6352 (pattern : Twelve) : d85 (change pattern 12 0) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 12 0) else d56 (change pattern 12 0)) = d85 pattern
  rw [s6351, s6308]
  rfl
theorem s6353 (pattern : Twelve) : d66 (change pattern 12 0) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 12 0) else d30 (change pattern 12 0)) = d66 pattern
  rw [s6322, s6283]
  rfl
theorem s6354 (pattern : Twelve) : d86 (change pattern 12 0) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 12 0) else d66 (change pattern 12 0)) = d86 pattern
  rw [s6346, s6353]
  rfl
theorem s6355 (pattern : Twelve) : d99 (change pattern 12 0) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 12 0) else d85 (change pattern 12 0)) = d99 pattern
  rw [s6354, s6352]
  rfl
theorem s6356 (pattern : Twelve) : d107 (change pattern 12 0) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 12 0) else d97 (change pattern 12 0)) = d107 pattern
  rw [s6355, s6340]
  rfl
theorem s6357 (pattern : Twelve) : d112 (change pattern 12 0) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 12 0) else d106 (change pattern 12 0)) = d112 pattern
  rw [s6356, s6349]
  rfl
theorem s6358 (pattern : Twelve) : d46 (change pattern 12 0) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d1 (change pattern 12 0)) = d46 pattern
  rw [s6271, s6262]
  rfl
theorem s6359 (pattern : Twelve) : d67 (change pattern 12 0) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 12 0) else d30 (change pattern 12 0)) = d67 pattern
  rw [s6358, s6283]
  rfl
theorem s6360 (pattern : Twelve) : d87 (change pattern 12 0) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 12 0) else d30 (change pattern 12 0)) = d87 pattern
  rw [s6359, s6283]
  rfl
theorem s6361 (pattern : Twelve) : d68 (change pattern 12 0) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 12 0) else d30 (change pattern 12 0)) = d68 pattern
  rw [s6321, s6283]
  rfl
theorem s6362 (pattern : Twelve) : d88 (change pattern 12 0) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 12 0) else d68 (change pattern 12 0)) = d88 pattern
  rw [s6346, s6361]
  rfl
theorem s6363 (pattern : Twelve) : d100 (change pattern 12 0) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 12 0) else d87 (change pattern 12 0)) = d100 pattern
  rw [s6362, s6360]
  rfl
theorem s6364 (pattern : Twelve) : d47 (change pattern 12 0) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d3 (change pattern 12 0)) = d47 pattern
  rw [s6278, s6271]
  rfl
theorem s6365 (pattern : Twelve) : d69 (change pattern 12 0) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 12 0) else d38 (change pattern 12 0)) = d69 pattern
  rw [s6364, s6321]
  rfl
theorem s6366 (pattern : Twelve) : d89 (change pattern 12 0) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 12 0) else d59 (change pattern 12 0)) = d89 pattern
  rw [s6365, s6323]
  rfl
theorem s6367 (pattern : Twelve) : d48 (change pattern 12 0) = d48 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d4 (change pattern 12 0)) = d48 pattern
  rw [s6278, s6286]
  rfl
theorem s6368 (pattern : Twelve) : d70 (change pattern 12 0) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 12 0) else d38 (change pattern 12 0)) = d70 pattern
  rw [s6367, s6321]
  rfl
theorem s6369 (pattern : Twelve) : d49 (change pattern 12 0) = d49 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d24 (change pattern 12 0)) = d49 pattern
  rw [s6278, s6328]
  rfl
theorem s6370 (pattern : Twelve) : d71 (change pattern 12 0) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 12 0) else d41 (change pattern 12 0)) = d71 pattern
  rw [s6369, s6329]
  rfl
theorem s6371 (pattern : Twelve) : d90 (change pattern 12 0) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 12 0) else d70 (change pattern 12 0)) = d90 pattern
  rw [s6370, s6368]
  rfl
theorem s6372 (pattern : Twelve) : d101 (change pattern 12 0) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 12 0) else d89 (change pattern 12 0)) = d101 pattern
  rw [s6371, s6366]
  rfl
theorem s6373 (pattern : Twelve) : d108 (change pattern 12 0) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 12 0) else d100 (change pattern 12 0)) = d108 pattern
  rw [s6372, s6363]
  rfl
theorem s6374 (pattern : Twelve) : d109 (change pattern 12 0) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d99 (change pattern 12 0)) = d109 pattern
  rw [s6278, s6355]
  rfl
theorem s6375 (pattern : Twelve) : d113 (change pattern 12 0) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 12 0) else d108 (change pattern 12 0)) = d113 pattern
  rw [s6374, s6373]
  rfl
theorem s6376 (pattern : Twelve) : d115 (change pattern 12 0) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 12 0) else d112 (change pattern 12 0)) = d115 pattern
  rw [s6375, s6357]
  rfl
theorem s6377 (pattern : Twelve) : d116 (change pattern 12 0) = d116 pattern := by
  change (if pattern.g then d115 (change pattern 12 0) else d114 (change pattern 12 0)) = d116 pattern
  rw [s6376, s6339]
  rfl
theorem s6378 (pattern : Twelve) : d814 (change pattern 12 0) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 12 0) else d7 (change pattern 12 0)) = d814 pattern
  rw [s6262, s6264]
  rfl
theorem s6379 (pattern : Twelve) : d816 (change pattern 12 0) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 12 0) else d814 (change pattern 12 0)) = d816 pattern
  rw [s6262, s6378]
  rfl
theorem s6380 (pattern : Twelve) : d824 (change pattern 12 0) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 12 0) else d27 (change pattern 12 0)) = d824 pattern
  rw [s6379, s6266]
  rfl
theorem s6381 (pattern : Twelve) : d838 (change pattern 12 0) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 12 0) else d0 (change pattern 12 0)) = d838 pattern
  rw [s6380, s6261]
  rfl
theorem s6382 (pattern : Twelve) : d817 (change pattern 12 0) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 12 0) else d19 (change pattern 12 0)) = d817 pattern
  rw [s6331, s6277]
  rfl
theorem s6383 (pattern : Twelve) : d825 (change pattern 12 0) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 12 0) else d817 (change pattern 12 0)) = d825 pattern
  rw [s6332, s6382]
  rfl
theorem s6384 (pattern : Twelve) : d839 (change pattern 12 0) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d17 (change pattern 12 0)) = d839 pattern
  rw [s6383, s6265]
  rfl
theorem s6385 (pattern : Twelve) : d853 (change pattern 12 0) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 12 0) else d838 (change pattern 12 0)) = d853 pattern
  rw [s6384, s6381]
  rfl
theorem s6386 (pattern : Twelve) : d818 (change pattern 12 0) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d814 (change pattern 12 0)) = d818 pattern
  rw [s6278, s6378]
  rfl
theorem s6387 (pattern : Twelve) : d826 (change pattern 12 0) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 12 0) else d34 (change pattern 12 0)) = d826 pattern
  rw [s6386, s6300]
  rfl
theorem s6388 (pattern : Twelve) : d840 (change pattern 12 0) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 12 0) else d56 (change pattern 12 0)) = d840 pattern
  rw [s6387, s6308]
  rfl
theorem s6389 (pattern : Twelve) : d827 (change pattern 12 0) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 12 0) else d34 (change pattern 12 0)) = d827 pattern
  rw [s6309, s6300]
  rfl
theorem s6390 (pattern : Twelve) : d841 (change pattern 12 0) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d827 (change pattern 12 0)) = d841 pattern
  rw [s6383, s6389]
  rfl
theorem s6391 (pattern : Twelve) : d854 (change pattern 12 0) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 12 0) else d840 (change pattern 12 0)) = d854 pattern
  rw [s6390, s6388]
  rfl
theorem s6392 (pattern : Twelve) : d861 (change pattern 12 0) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 12 0) else d853 (change pattern 12 0)) = d861 pattern
  rw [s6391, s6385]
  rfl
theorem s6393 (pattern : Twelve) : d819 (change pattern 12 0) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 12 0) else d814 (change pattern 12 0)) = d819 pattern
  rw [s6271, s6378]
  rfl
theorem s6394 (pattern : Twelve) : d828 (change pattern 12 0) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 12 0) else d34 (change pattern 12 0)) = d828 pattern
  rw [s6393, s6300]
  rfl
theorem s6395 (pattern : Twelve) : d842 (change pattern 12 0) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 12 0) else d30 (change pattern 12 0)) = d842 pattern
  rw [s6394, s6283]
  rfl
theorem s6396 (pattern : Twelve) : d843 (change pattern 12 0) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d34 (change pattern 12 0)) = d843 pattern
  rw [s6383, s6300]
  rfl
theorem s6397 (pattern : Twelve) : d855 (change pattern 12 0) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 12 0) else d842 (change pattern 12 0)) = d855 pattern
  rw [s6396, s6395]
  rfl
theorem s6398 (pattern : Twelve) : d815 (change pattern 12 0) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 12 0) else d9 (change pattern 12 0)) = d815 pattern
  rw [s6271, s6272]
  rfl
theorem s6399 (pattern : Twelve) : d820 (change pattern 12 0) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d815 (change pattern 12 0)) = d820 pattern
  rw [s6278, s6398]
  rfl
theorem s6400 (pattern : Twelve) : d829 (change pattern 12 0) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 12 0) else d41 (change pattern 12 0)) = d829 pattern
  rw [s6399, s6329]
  rfl
theorem s6401 (pattern : Twelve) : d844 (change pattern 12 0) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 12 0) else d59 (change pattern 12 0)) = d844 pattern
  rw [s6400, s6323]
  rfl
theorem s6402 (pattern : Twelve) : d830 (change pattern 12 0) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 12 0) else d41 (change pattern 12 0)) = d830 pattern
  rw [s6324, s6329]
  rfl
theorem s6403 (pattern : Twelve) : d821 (change pattern 12 0) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 12 0) else d25 (change pattern 12 0)) = d821 pattern
  rw [s6292, s6331]
  rfl
theorem s6404 (pattern : Twelve) : d822 (change pattern 12 0) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d21 (change pattern 12 0)) = d822 pattern
  rw [s6278, s6292]
  rfl
theorem s6405 (pattern : Twelve) : d831 (change pattern 12 0) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 12 0) else d821 (change pattern 12 0)) = d831 pattern
  rw [s6404, s6403]
  rfl
theorem s6406 (pattern : Twelve) : d845 (change pattern 12 0) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 12 0) else d830 (change pattern 12 0)) = d845 pattern
  rw [s6405, s6402]
  rfl
theorem s6407 (pattern : Twelve) : d856 (change pattern 12 0) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 12 0) else d844 (change pattern 12 0)) = d856 pattern
  rw [s6406, s6401]
  rfl
theorem s6408 (pattern : Twelve) : d862 (change pattern 12 0) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 12 0) else d855 (change pattern 12 0)) = d862 pattern
  rw [s6407, s6397]
  rfl
theorem s6409 (pattern : Twelve) : d863 (change pattern 12 0) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d854 (change pattern 12 0)) = d863 pattern
  rw [s6278, s6391]
  rfl
theorem s6410 (pattern : Twelve) : d867 (change pattern 12 0) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 12 0) else d862 (change pattern 12 0)) = d867 pattern
  rw [s6409, s6408]
  rfl
theorem s6411 (pattern : Twelve) : d869 (change pattern 12 0) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 12 0) else d861 (change pattern 12 0)) = d869 pattern
  rw [s6410, s6392]
  rfl
theorem s6412 (pattern : Twelve) : d823 (change pattern 12 0) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 12 0) else d17 (change pattern 12 0)) = d823 pattern
  rw [s6269, s6265]
  rfl
theorem s6413 (pattern : Twelve) : d846 (change pattern 12 0) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d823 (change pattern 12 0)) = d846 pattern
  rw [s6383, s6412]
  rfl
theorem s6414 (pattern : Twelve) : d857 (change pattern 12 0) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 12 0) else d838 (change pattern 12 0)) = d857 pattern
  rw [s6413, s6381]
  rfl
theorem s6415 (pattern : Twelve) : d832 (change pattern 12 0) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 12 0) else d34 (change pattern 12 0)) = d832 pattern
  rw [s6350, s6300]
  rfl
theorem s6416 (pattern : Twelve) : d847 (change pattern 12 0) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 12 0) else d56 (change pattern 12 0)) = d847 pattern
  rw [s6415, s6308]
  rfl
theorem s6417 (pattern : Twelve) : d833 (change pattern 12 0) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 12 0) else d34 (change pattern 12 0)) = d833 pattern
  rw [s6322, s6300]
  rfl
theorem s6418 (pattern : Twelve) : d848 (change pattern 12 0) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d833 (change pattern 12 0)) = d848 pattern
  rw [s6383, s6417]
  rfl
theorem s6419 (pattern : Twelve) : d858 (change pattern 12 0) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 12 0) else d847 (change pattern 12 0)) = d858 pattern
  rw [s6418, s6416]
  rfl
theorem s6420 (pattern : Twelve) : d864 (change pattern 12 0) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 12 0) else d857 (change pattern 12 0)) = d864 pattern
  rw [s6419, s6414]
  rfl
theorem s6421 (pattern : Twelve) : d834 (change pattern 12 0) = d834 pattern := by
  change (if pattern.h then d46 (change pattern 12 0) else d34 (change pattern 12 0)) = d834 pattern
  rw [s6358, s6300]
  rfl
theorem s6422 (pattern : Twelve) : d849 (change pattern 12 0) = d849 pattern := by
  change (if pattern.f then d834 (change pattern 12 0) else d30 (change pattern 12 0)) = d849 pattern
  rw [s6421, s6283]
  rfl
theorem s6423 (pattern : Twelve) : d835 (change pattern 12 0) = d835 pattern := by
  change (if pattern.h then d38 (change pattern 12 0) else d34 (change pattern 12 0)) = d835 pattern
  rw [s6321, s6300]
  rfl
theorem s6424 (pattern : Twelve) : d850 (change pattern 12 0) = d850 pattern := by
  change (if pattern.f then d825 (change pattern 12 0) else d835 (change pattern 12 0)) = d850 pattern
  rw [s6383, s6423]
  rfl
theorem s6425 (pattern : Twelve) : d859 (change pattern 12 0) = d859 pattern := by
  change (if pattern.e then d850 (change pattern 12 0) else d849 (change pattern 12 0)) = d859 pattern
  rw [s6424, s6422]
  rfl
theorem s6426 (pattern : Twelve) : d836 (change pattern 12 0) = d836 pattern := by
  change (if pattern.h then d47 (change pattern 12 0) else d41 (change pattern 12 0)) = d836 pattern
  rw [s6364, s6329]
  rfl
theorem s6427 (pattern : Twelve) : d851 (change pattern 12 0) = d851 pattern := by
  change (if pattern.f then d836 (change pattern 12 0) else d59 (change pattern 12 0)) = d851 pattern
  rw [s6426, s6323]
  rfl
theorem s6428 (pattern : Twelve) : d837 (change pattern 12 0) = d837 pattern := by
  change (if pattern.h then d48 (change pattern 12 0) else d41 (change pattern 12 0)) = d837 pattern
  rw [s6367, s6329]
  rfl
theorem s6429 (pattern : Twelve) : d852 (change pattern 12 0) = d852 pattern := by
  change (if pattern.f then d831 (change pattern 12 0) else d837 (change pattern 12 0)) = d852 pattern
  rw [s6405, s6428]
  rfl
theorem s6430 (pattern : Twelve) : d860 (change pattern 12 0) = d860 pattern := by
  change (if pattern.e then d852 (change pattern 12 0) else d851 (change pattern 12 0)) = d860 pattern
  rw [s6429, s6427]
  rfl
theorem s6431 (pattern : Twelve) : d865 (change pattern 12 0) = d865 pattern := by
  change (if pattern.j then d860 (change pattern 12 0) else d859 (change pattern 12 0)) = d865 pattern
  rw [s6430, s6425]
  rfl
theorem s6432 (pattern : Twelve) : d866 (change pattern 12 0) = d866 pattern := by
  change (if pattern.j then d6 (change pattern 12 0) else d858 (change pattern 12 0)) = d866 pattern
  rw [s6278, s6419]
  rfl
theorem s6433 (pattern : Twelve) : d868 (change pattern 12 0) = d868 pattern := by
  change (if pattern.d then d866 (change pattern 12 0) else d865 (change pattern 12 0)) = d868 pattern
  rw [s6432, s6431]
  rfl
theorem s6434 (pattern : Twelve) : d870 (change pattern 12 0) = d870 pattern := by
  change (if pattern.c then d868 (change pattern 12 0) else d864 (change pattern 12 0)) = d870 pattern
  rw [s6433, s6420]
  rfl
theorem s6435 (pattern : Twelve) : d871 (change pattern 12 0) = d871 pattern := by
  change (if pattern.g then d870 (change pattern 12 0) else d869 (change pattern 12 0)) = d871 pattern
  rw [s6434, s6411]
  rfl
theorem s6436 (pattern : Twelve) : d1275 (change pattern 12 0) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 12 0) else d7 (change pattern 12 0)) = d1275 pattern
  rw [s6270, s6264]
  rfl
theorem s6437 (pattern : Twelve) : d872 (change pattern 12 0) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 12 0) else d1 (change pattern 12 0)) = d872 pattern
  rw [s6270, s6262]
  rfl
theorem s6438 (pattern : Twelve) : d1278 (change pattern 12 0) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 12 0) else d1275 (change pattern 12 0)) = d1278 pattern
  rw [s6437, s6436]
  rfl
theorem s6439 (pattern : Twelve) : d1284 (change pattern 12 0) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 12 0) else d1278 (change pattern 12 0)) = d1284 pattern
  rw [s6437, s6438]
  rfl
theorem s6440 (pattern : Twelve) : d1293 (change pattern 12 0) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 12 0) else d17 (change pattern 12 0)) = d1293 pattern
  rw [s6439, s6265]
  rfl
theorem s6441 (pattern : Twelve) : d1294 (change pattern 12 0) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 12 0) else d19 (change pattern 12 0)) = d1294 pattern
  rw [s6278, s6277]
  rfl
theorem s6442 (pattern : Twelve) : d1305 (change pattern 12 0) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 12 0) else d1293 (change pattern 12 0)) = d1305 pattern
  rw [s6441, s6440]
  rfl
theorem s6443 (pattern : Twelve) : d117 (change pattern 12 0) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 0) else d3 (change pattern 12 0)) = d117 pattern
  rw [s6286, s6271]
  rfl
theorem s6444 (pattern : Twelve) : d1276 (change pattern 12 0) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 12 0) else d9 (change pattern 12 0)) = d1276 pattern
  rw [s6443, s6272]
  rfl
theorem s6445 (pattern : Twelve) : d1279 (change pattern 12 0) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 12 0) else d1275 (change pattern 12 0)) = d1279 pattern
  rw [s6444, s6436]
  rfl
theorem s6446 (pattern : Twelve) : d1280 (change pattern 12 0) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d872 (change pattern 12 0)) = d1280 pattern
  rw [s6278, s6437]
  rfl
theorem s6447 (pattern : Twelve) : d1285 (change pattern 12 0) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 12 0) else d1279 (change pattern 12 0)) = d1285 pattern
  rw [s6446, s6445]
  rfl
theorem s6448 (pattern : Twelve) : d1295 (change pattern 12 0) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 12 0) else d827 (change pattern 12 0)) = d1295 pattern
  rw [s6447, s6389]
  rfl
theorem s6449 (pattern : Twelve) : d1286 (change pattern 12 0) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 12 0) else d817 (change pattern 12 0)) = d1286 pattern
  rw [s6279, s6382]
  rfl
end NetHack.Sokoban21.Diagram
