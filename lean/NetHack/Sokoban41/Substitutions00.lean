/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Diagram
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s0 (pattern : Ten) : d0 (change pattern 10 10) = d0 pattern := by
  rfl
theorem s1 (pattern : Ten) : d2 (change pattern 10 10) = d2 pattern := by
  rfl
theorem s2 (pattern : Ten) : d15 (change pattern 10 10) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 10 10) else d0 (change pattern 10 10)) = d15 pattern
  rw [s1, s0]
  rfl
theorem s3 (pattern : Ten) : d4 (change pattern 10 10) = d4 pattern := by
  rfl
theorem s4 (pattern : Ten) : d10 (change pattern 10 10) = d10 pattern := by
  rfl
theorem s5 (pattern : Ten) : d42 (change pattern 10 10) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d4 (change pattern 10 10)) = d42 pattern
  rw [s4, s3]
  rfl
theorem s6 (pattern : Ten) : d48 (change pattern 10 10) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 10 10) else d15 (change pattern 10 10)) = d48 pattern
  rw [s5, s2]
  rfl
theorem s7 (pattern : Ten) : d6 (change pattern 10 10) = d6 pattern := by
  rfl
theorem s8 (pattern : Ten) : d43 (change pattern 10 10) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d6 (change pattern 10 10)) = d43 pattern
  rw [s4, s7]
  rfl
theorem s9 (pattern : Ten) : d49 (change pattern 10 10) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d43 (change pattern 10 10)) = d49 pattern
  rw [s4, s8]
  rfl
theorem s10 (pattern : Ten) : d54 (change pattern 10 10) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 10 10) else d48 (change pattern 10 10)) = d54 pattern
  rw [s9, s6]
  rfl
theorem s11 (pattern : Ten) : d44 (change pattern 10 10) = d44 pattern := by
  change (if pattern.j then d4 (change pattern 10 10) else d2 (change pattern 10 10)) = d44 pattern
  rw [s3, s1]
  rfl
theorem s12 (pattern : Ten) : d50 (change pattern 10 10) = d50 pattern := by
  change (if pattern.i then d43 (change pattern 10 10) else d44 (change pattern 10 10)) = d50 pattern
  rw [s8, s11]
  rfl
theorem s13 (pattern : Ten) : d8 (change pattern 10 10) = d8 pattern := by
  rfl
theorem s14 (pattern : Ten) : d45 (change pattern 10 10) = d45 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d8 (change pattern 10 10)) = d45 pattern
  rw [s4, s13]
  rfl
theorem s15 (pattern : Ten) : d51 (change pattern 10 10) = d51 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d45 (change pattern 10 10)) = d51 pattern
  rw [s4, s14]
  rfl
theorem s16 (pattern : Ten) : d55 (change pattern 10 10) = d55 pattern := by
  change (if pattern.h then d51 (change pattern 10 10) else d50 (change pattern 10 10)) = d55 pattern
  rw [s15, s12]
  rfl
theorem s17 (pattern : Ten) : d160 (change pattern 10 10) = d160 pattern := by
  change (if pattern.g then d55 (change pattern 10 10) else d54 (change pattern 10 10)) = d160 pattern
  rw [s16, s10]
  rfl
theorem s18 (pattern : Ten) : d157 (change pattern 10 10) = d157 pattern := by
  change (if pattern.j then d6 (change pattern 10 10) else d4 (change pattern 10 10)) = d157 pattern
  rw [s7, s3]
  rfl
theorem s19 (pattern : Ten) : d158 (change pattern 10 10) = d158 pattern := by
  change (if pattern.i then d45 (change pattern 10 10) else d157 (change pattern 10 10)) = d158 pattern
  rw [s14, s18]
  rfl
theorem s20 (pattern : Ten) : d159 (change pattern 10 10) = d159 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d158 (change pattern 10 10)) = d159 pattern
  rw [s4, s19]
  rfl
theorem s21 (pattern : Ten) : d161 (change pattern 10 10) = d161 pattern := by
  change (if pattern.g then d159 (change pattern 10 10) else d54 (change pattern 10 10)) = d161 pattern
  rw [s20, s10]
  rfl
theorem s22 (pattern : Ten) : d165 (change pattern 10 10) = d165 pattern := by
  change (if pattern.c then d161 (change pattern 10 10) else d160 (change pattern 10 10)) = d165 pattern
  rw [s21, s17]
  rfl
theorem s23 (pattern : Ten) : d162 (change pattern 10 10) = d162 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d54 (change pattern 10 10)) = d162 pattern
  rw [s4, s10]
  rfl
theorem s24 (pattern : Ten) : d163 (change pattern 10 10) = d163 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d55 (change pattern 10 10)) = d163 pattern
  rw [s4, s16]
  rfl
theorem s25 (pattern : Ten) : d166 (change pattern 10 10) = d166 pattern := by
  change (if pattern.c then d163 (change pattern 10 10) else d162 (change pattern 10 10)) = d166 pattern
  rw [s24, s23]
  rfl
theorem s26 (pattern : Ten) : d168 (change pattern 10 10) = d168 pattern := by
  change (if pattern.e then d166 (change pattern 10 10) else d165 (change pattern 10 10)) = d168 pattern
  rw [s25, s22]
  rfl
theorem s27 (pattern : Ten) : d7 (change pattern 10 10) = d7 pattern := by
  rfl
theorem s28 (pattern : Ten) : d38 (change pattern 10 10) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 10 10) else d7 (change pattern 10 10)) = d38 pattern
  rw [s13, s27]
  rfl
theorem s29 (pattern : Ten) : d40 (change pattern 10 10) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 10 10) else d38 (change pattern 10 10)) = d40 pattern
  rw [s13, s28]
  rfl
theorem s30 (pattern : Ten) : d46 (change pattern 10 10) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d40 (change pattern 10 10)) = d46 pattern
  rw [s4, s29]
  rfl
theorem s31 (pattern : Ten) : d52 (change pattern 10 10) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d46 (change pattern 10 10)) = d52 pattern
  rw [s4, s30]
  rfl
theorem s32 (pattern : Ten) : d56 (change pattern 10 10) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d52 (change pattern 10 10)) = d56 pattern
  rw [s4, s31]
  rfl
theorem s33 (pattern : Ten) : d9 (change pattern 10 10) = d9 pattern := by
  rfl
theorem s34 (pattern : Ten) : d39 (change pattern 10 10) = d39 pattern := by
  change (if pattern.b then d10 (change pattern 10 10) else d9 (change pattern 10 10)) = d39 pattern
  rw [s4, s33]
  rfl
theorem s35 (pattern : Ten) : d41 (change pattern 10 10) = d41 pattern := by
  change (if pattern.a then d10 (change pattern 10 10) else d39 (change pattern 10 10)) = d41 pattern
  rw [s4, s34]
  rfl
theorem s36 (pattern : Ten) : d47 (change pattern 10 10) = d47 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d41 (change pattern 10 10)) = d47 pattern
  rw [s4, s35]
  rfl
theorem s37 (pattern : Ten) : d53 (change pattern 10 10) = d53 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d47 (change pattern 10 10)) = d53 pattern
  rw [s4, s36]
  rfl
theorem s38 (pattern : Ten) : d57 (change pattern 10 10) = d57 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d53 (change pattern 10 10)) = d57 pattern
  rw [s4, s37]
  rfl
theorem s39 (pattern : Ten) : d164 (change pattern 10 10) = d164 pattern := by
  change (if pattern.g then d57 (change pattern 10 10) else d56 (change pattern 10 10)) = d164 pattern
  rw [s38, s32]
  rfl
theorem s40 (pattern : Ten) : d60 (change pattern 10 10) = d60 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d56 (change pattern 10 10)) = d60 pattern
  rw [s4, s32]
  rfl
theorem s41 (pattern : Ten) : d167 (change pattern 10 10) = d167 pattern := by
  change (if pattern.c then d60 (change pattern 10 10) else d164 (change pattern 10 10)) = d167 pattern
  rw [s40, s39]
  rfl
theorem s42 (pattern : Ten) : d61 (change pattern 10 10) = d61 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d57 (change pattern 10 10)) = d61 pattern
  rw [s4, s38]
  rfl
theorem s43 (pattern : Ten) : d63 (change pattern 10 10) = d63 pattern := by
  change (if pattern.c then d61 (change pattern 10 10) else d60 (change pattern 10 10)) = d63 pattern
  rw [s42, s40]
  rfl
theorem s44 (pattern : Ten) : d169 (change pattern 10 10) = d169 pattern := by
  change (if pattern.e then d63 (change pattern 10 10) else d167 (change pattern 10 10)) = d169 pattern
  rw [s43, s41]
  rfl
theorem s45 (pattern : Ten) : d170 (change pattern 10 10) = d170 pattern := by
  change (if pattern.d then d169 (change pattern 10 10) else d168 (change pattern 10 10)) = d170 pattern
  rw [s44, s26]
  rfl
theorem s46 (pattern : Ten) : d1 (change pattern 10 10) = d1 pattern := by
  rfl
theorem s47 (pattern : Ten) : d171 (change pattern 10 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 10 10) else d0 (change pattern 10 10)) = d171 pattern
  rw [s46, s0]
  rfl
theorem s48 (pattern : Ten) : d3 (change pattern 10 10) = d3 pattern := by
  rfl
theorem s49 (pattern : Ten) : d172 (change pattern 10 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 10 10) else d2 (change pattern 10 10)) = d172 pattern
  rw [s48, s1]
  rfl
theorem s50 (pattern : Ten) : d174 (change pattern 10 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 10 10) else d171 (change pattern 10 10)) = d174 pattern
  rw [s49, s47]
  rfl
theorem s51 (pattern : Ten) : d5 (change pattern 10 10) = d5 pattern := by
  rfl
theorem s52 (pattern : Ten) : d193 (change pattern 10 10) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 10 10) else d4 (change pattern 10 10)) = d193 pattern
  rw [s51, s3]
  rfl
theorem s53 (pattern : Ten) : d197 (change pattern 10 10) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d193 (change pattern 10 10)) = d197 pattern
  rw [s4, s52]
  rfl
theorem s54 (pattern : Ten) : d202 (change pattern 10 10) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 10 10) else d174 (change pattern 10 10)) = d202 pattern
  rw [s53, s50]
  rfl
theorem s55 (pattern : Ten) : d194 (change pattern 10 10) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 10 10) else d6 (change pattern 10 10)) = d194 pattern
  rw [s27, s7]
  rfl
theorem s56 (pattern : Ten) : d198 (change pattern 10 10) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d194 (change pattern 10 10)) = d198 pattern
  rw [s4, s55]
  rfl
theorem s57 (pattern : Ten) : d203 (change pattern 10 10) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d198 (change pattern 10 10)) = d203 pattern
  rw [s4, s56]
  rfl
theorem s58 (pattern : Ten) : d207 (change pattern 10 10) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 10 10) else d202 (change pattern 10 10)) = d207 pattern
  rw [s57, s54]
  rfl
theorem s59 (pattern : Ten) : d310 (change pattern 10 10) = d310 pattern := by
  change (if pattern.a then d4 (change pattern 10 10) else d3 (change pattern 10 10)) = d310 pattern
  rw [s3, s48]
  rfl
theorem s60 (pattern : Ten) : d314 (change pattern 10 10) = d314 pattern := by
  change (if pattern.f then d310 (change pattern 10 10) else d172 (change pattern 10 10)) = d314 pattern
  rw [s59, s49]
  rfl
theorem s61 (pattern : Ten) : d311 (change pattern 10 10) = d311 pattern := by
  change (if pattern.a then d6 (change pattern 10 10) else d5 (change pattern 10 10)) = d311 pattern
  rw [s7, s51]
  rfl
theorem s62 (pattern : Ten) : d315 (change pattern 10 10) = d315 pattern := by
  change (if pattern.f then d311 (change pattern 10 10) else d193 (change pattern 10 10)) = d315 pattern
  rw [s61, s52]
  rfl
theorem s63 (pattern : Ten) : d320 (change pattern 10 10) = d320 pattern := by
  change (if pattern.j then d315 (change pattern 10 10) else d314 (change pattern 10 10)) = d320 pattern
  rw [s62, s60]
  rfl
theorem s64 (pattern : Ten) : d312 (change pattern 10 10) = d312 pattern := by
  change (if pattern.a then d8 (change pattern 10 10) else d7 (change pattern 10 10)) = d312 pattern
  rw [s13, s27]
  rfl
theorem s65 (pattern : Ten) : d316 (change pattern 10 10) = d316 pattern := by
  change (if pattern.f then d312 (change pattern 10 10) else d194 (change pattern 10 10)) = d316 pattern
  rw [s64, s55]
  rfl
theorem s66 (pattern : Ten) : d319 (change pattern 10 10) = d319 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d316 (change pattern 10 10)) = d319 pattern
  rw [s4, s65]
  rfl
theorem s67 (pattern : Ten) : d323 (change pattern 10 10) = d323 pattern := by
  change (if pattern.i then d319 (change pattern 10 10) else d320 (change pattern 10 10)) = d323 pattern
  rw [s66, s63]
  rfl
theorem s68 (pattern : Ten) : d195 (change pattern 10 10) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 10 10) else d8 (change pattern 10 10)) = d195 pattern
  rw [s33, s13]
  rfl
theorem s69 (pattern : Ten) : d11 (change pattern 10 10) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 10) else d9 (change pattern 10 10)) = d11 pattern
  rw [s4, s33]
  rfl
theorem s70 (pattern : Ten) : d196 (change pattern 10 10) = d196 pattern := by
  change (if pattern.f then d11 (change pattern 10 10) else d195 (change pattern 10 10)) = d196 pattern
  rw [s69, s68]
  rfl
theorem s71 (pattern : Ten) : d201 (change pattern 10 10) = d201 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d196 (change pattern 10 10)) = d201 pattern
  rw [s4, s70]
  rfl
theorem s72 (pattern : Ten) : d206 (change pattern 10 10) = d206 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d201 (change pattern 10 10)) = d206 pattern
  rw [s4, s71]
  rfl
theorem s73 (pattern : Ten) : d325 (change pattern 10 10) = d325 pattern := by
  change (if pattern.h then d206 (change pattern 10 10) else d323 (change pattern 10 10)) = d325 pattern
  rw [s72, s67]
  rfl
theorem s74 (pattern : Ten) : d344 (change pattern 10 10) = d344 pattern := by
  change (if pattern.g then d325 (change pattern 10 10) else d207 (change pattern 10 10)) = d344 pattern
  rw [s73, s58]
  rfl
theorem s75 (pattern : Ten) : d341 (change pattern 10 10) = d341 pattern := by
  change (if pattern.j then d316 (change pattern 10 10) else d315 (change pattern 10 10)) = d341 pattern
  rw [s65, s62]
  rfl
theorem s76 (pattern : Ten) : d342 (change pattern 10 10) = d342 pattern := by
  change (if pattern.i then d201 (change pattern 10 10) else d341 (change pattern 10 10)) = d342 pattern
  rw [s71, s75]
  rfl
theorem s77 (pattern : Ten) : d343 (change pattern 10 10) = d343 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d342 (change pattern 10 10)) = d343 pattern
  rw [s4, s76]
  rfl
theorem s78 (pattern : Ten) : d345 (change pattern 10 10) = d345 pattern := by
  change (if pattern.g then d343 (change pattern 10 10) else d207 (change pattern 10 10)) = d345 pattern
  rw [s77, s58]
  rfl
theorem s79 (pattern : Ten) : d346 (change pattern 10 10) = d346 pattern := by
  change (if pattern.c then d345 (change pattern 10 10) else d344 (change pattern 10 10)) = d346 pattern
  rw [s78, s74]
  rfl
theorem s80 (pattern : Ten) : d309 (change pattern 10 10) = d309 pattern := by
  change (if pattern.a then d2 (change pattern 10 10) else d1 (change pattern 10 10)) = d309 pattern
  rw [s1, s46]
  rfl
theorem s81 (pattern : Ten) : d313 (change pattern 10 10) = d313 pattern := by
  change (if pattern.f then d309 (change pattern 10 10) else d171 (change pattern 10 10)) = d313 pattern
  rw [s80, s47]
  rfl
theorem s82 (pattern : Ten) : d317 (change pattern 10 10) = d317 pattern := by
  change (if pattern.j then d314 (change pattern 10 10) else d313 (change pattern 10 10)) = d317 pattern
  rw [s60, s81]
  rfl
theorem s83 (pattern : Ten) : d318 (change pattern 10 10) = d318 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d315 (change pattern 10 10)) = d318 pattern
  rw [s4, s62]
  rfl
theorem s84 (pattern : Ten) : d321 (change pattern 10 10) = d321 pattern := by
  change (if pattern.i then d318 (change pattern 10 10) else d317 (change pattern 10 10)) = d321 pattern
  rw [s83, s82]
  rfl
theorem s85 (pattern : Ten) : d322 (change pattern 10 10) = d322 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d319 (change pattern 10 10)) = d322 pattern
  rw [s4, s66]
  rfl
theorem s86 (pattern : Ten) : d324 (change pattern 10 10) = d324 pattern := by
  change (if pattern.h then d322 (change pattern 10 10) else d321 (change pattern 10 10)) = d324 pattern
  rw [s85, s84]
  rfl
theorem s87 (pattern : Ten) : d333 (change pattern 10 10) = d333 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d324 (change pattern 10 10)) = d333 pattern
  rw [s4, s86]
  rfl
theorem s88 (pattern : Ten) : d334 (change pattern 10 10) = d334 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d325 (change pattern 10 10)) = d334 pattern
  rw [s4, s73]
  rfl
theorem s89 (pattern : Ten) : d336 (change pattern 10 10) = d336 pattern := by
  change (if pattern.c then d334 (change pattern 10 10) else d333 (change pattern 10 10)) = d336 pattern
  rw [s88, s87]
  rfl
theorem s90 (pattern : Ten) : d347 (change pattern 10 10) = d347 pattern := by
  change (if pattern.e then d336 (change pattern 10 10) else d346 (change pattern 10 10)) = d347 pattern
  rw [s89, s79]
  rfl
theorem s91 (pattern : Ten) : d200 (change pattern 10 10) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d195 (change pattern 10 10)) = d200 pattern
  rw [s4, s68]
  rfl
theorem s92 (pattern : Ten) : d205 (change pattern 10 10) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d200 (change pattern 10 10)) = d205 pattern
  rw [s4, s91]
  rfl
theorem s93 (pattern : Ten) : d209 (change pattern 10 10) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d205 (change pattern 10 10)) = d209 pattern
  rw [s4, s92]
  rfl
theorem s94 (pattern : Ten) : d214 (change pattern 10 10) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d209 (change pattern 10 10)) = d214 pattern
  rw [s4, s93]
  rfl
theorem s95 (pattern : Ten) : d210 (change pattern 10 10) = d210 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d206 (change pattern 10 10)) = d210 pattern
  rw [s4, s72]
  rfl
theorem s96 (pattern : Ten) : d335 (change pattern 10 10) = d335 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d210 (change pattern 10 10)) = d335 pattern
  rw [s4, s95]
  rfl
theorem s97 (pattern : Ten) : d337 (change pattern 10 10) = d337 pattern := by
  change (if pattern.c then d10 (change pattern 10 10) else d335 (change pattern 10 10)) = d337 pattern
  rw [s4, s96]
  rfl
theorem s98 (pattern : Ten) : d348 (change pattern 10 10) = d348 pattern := by
  change (if pattern.e then d337 (change pattern 10 10) else d214 (change pattern 10 10)) = d348 pattern
  rw [s97, s94]
  rfl
theorem s99 (pattern : Ten) : d349 (change pattern 10 10) = d349 pattern := by
  change (if pattern.d then d348 (change pattern 10 10) else d347 (change pattern 10 10)) = d349 pattern
  rw [s98, s90]
  rfl
theorem s100 (pattern : Ten) : d173 (change pattern 10 10) = d173 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d171 (change pattern 10 10)) = d173 pattern
  rw [s4, s47]
  rfl
theorem s101 (pattern : Ten) : d176 (change pattern 10 10) = d176 pattern := by
  change (if pattern.i then d173 (change pattern 10 10) else d171 (change pattern 10 10)) = d176 pattern
  rw [s100, s47]
  rfl
theorem s102 (pattern : Ten) : d177 (change pattern 10 10) = d177 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d173 (change pattern 10 10)) = d177 pattern
  rw [s4, s100]
  rfl
theorem s103 (pattern : Ten) : d180 (change pattern 10 10) = d180 pattern := by
  change (if pattern.h then d177 (change pattern 10 10) else d176 (change pattern 10 10)) = d180 pattern
  rw [s102, s101]
  rfl
theorem s104 (pattern : Ten) : d181 (change pattern 10 10) = d181 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d177 (change pattern 10 10)) = d181 pattern
  rw [s4, s102]
  rfl
theorem s105 (pattern : Ten) : d184 (change pattern 10 10) = d184 pattern := by
  change (if pattern.g then d181 (change pattern 10 10) else d180 (change pattern 10 10)) = d184 pattern
  rw [s104, s103]
  rfl
theorem s106 (pattern : Ten) : d175 (change pattern 10 10) = d175 pattern := by
  change (if pattern.j then d10 (change pattern 10 10) else d172 (change pattern 10 10)) = d175 pattern
  rw [s4, s49]
  rfl
theorem s107 (pattern : Ten) : d178 (change pattern 10 10) = d178 pattern := by
  change (if pattern.i then d175 (change pattern 10 10) else d174 (change pattern 10 10)) = d178 pattern
  rw [s106, s50]
  rfl
theorem s108 (pattern : Ten) : d179 (change pattern 10 10) = d179 pattern := by
  change (if pattern.i then d10 (change pattern 10 10) else d175 (change pattern 10 10)) = d179 pattern
  rw [s4, s106]
  rfl
theorem s109 (pattern : Ten) : d182 (change pattern 10 10) = d182 pattern := by
  change (if pattern.h then d179 (change pattern 10 10) else d178 (change pattern 10 10)) = d182 pattern
  rw [s108, s107]
  rfl
theorem s110 (pattern : Ten) : d185 (change pattern 10 10) = d185 pattern := by
  change (if pattern.g then d181 (change pattern 10 10) else d182 (change pattern 10 10)) = d185 pattern
  rw [s104, s109]
  rfl
theorem s111 (pattern : Ten) : d188 (change pattern 10 10) = d188 pattern := by
  change (if pattern.c then d185 (change pattern 10 10) else d184 (change pattern 10 10)) = d188 pattern
  rw [s110, s105]
  rfl
theorem s112 (pattern : Ten) : d186 (change pattern 10 10) = d186 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d181 (change pattern 10 10)) = d186 pattern
  rw [s4, s104]
  rfl
theorem s113 (pattern : Ten) : d183 (change pattern 10 10) = d183 pattern := by
  change (if pattern.h then d10 (change pattern 10 10) else d179 (change pattern 10 10)) = d183 pattern
  rw [s4, s108]
  rfl
theorem s114 (pattern : Ten) : d187 (change pattern 10 10) = d187 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d183 (change pattern 10 10)) = d187 pattern
  rw [s4, s113]
  rfl
theorem s115 (pattern : Ten) : d189 (change pattern 10 10) = d189 pattern := by
  change (if pattern.c then d187 (change pattern 10 10) else d186 (change pattern 10 10)) = d189 pattern
  rw [s114, s112]
  rfl
theorem s116 (pattern : Ten) : d190 (change pattern 10 10) = d190 pattern := by
  change (if pattern.e then d189 (change pattern 10 10) else d188 (change pattern 10 10)) = d190 pattern
  rw [s115, s111]
  rfl
theorem s117 (pattern : Ten) : d191 (change pattern 10 10) = d191 pattern := by
  change (if pattern.e then d10 (change pattern 10 10) else d189 (change pattern 10 10)) = d191 pattern
  rw [s4, s115]
  rfl
theorem s118 (pattern : Ten) : d192 (change pattern 10 10) = d192 pattern := by
  change (if pattern.d then d191 (change pattern 10 10) else d190 (change pattern 10 10)) = d192 pattern
  rw [s117, s116]
  rfl
theorem s119 (pattern : Ten) : d211 (change pattern 10 10) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d207 (change pattern 10 10)) = d211 pattern
  rw [s4, s58]
  rfl
theorem s120 (pattern : Ten) : d199 (change pattern 10 10) = d199 pattern := by
  change (if pattern.j then d193 (change pattern 10 10) else d172 (change pattern 10 10)) = d199 pattern
  rw [s52, s49]
  rfl
theorem s121 (pattern : Ten) : d204 (change pattern 10 10) = d204 pattern := by
  change (if pattern.i then d198 (change pattern 10 10) else d199 (change pattern 10 10)) = d204 pattern
  rw [s56, s120]
  rfl
theorem s122 (pattern : Ten) : d208 (change pattern 10 10) = d208 pattern := by
  change (if pattern.h then d205 (change pattern 10 10) else d204 (change pattern 10 10)) = d208 pattern
  rw [s92, s121]
  rfl
theorem s123 (pattern : Ten) : d212 (change pattern 10 10) = d212 pattern := by
  change (if pattern.g then d10 (change pattern 10 10) else d208 (change pattern 10 10)) = d212 pattern
  rw [s4, s122]
  rfl
theorem s124 (pattern : Ten) : d215 (change pattern 10 10) = d215 pattern := by
  change (if pattern.c then d212 (change pattern 10 10) else d211 (change pattern 10 10)) = d215 pattern
  rw [s123, s119]
  rfl
theorem s125 (pattern : Ten) : d218 (change pattern 10 10) = d218 pattern := by
  change (if pattern.e then d215 (change pattern 10 10) else d207 (change pattern 10 10)) = d218 pattern
  rw [s124, s58]
  rfl
theorem s126 (pattern : Ten) : d213 (change pattern 10 10) = d213 pattern := by
  change (if pattern.g then d210 (change pattern 10 10) else d209 (change pattern 10 10)) = d213 pattern
  rw [s95, s93]
  rfl
theorem s127 (pattern : Ten) : d216 (change pattern 10 10) = d216 pattern := by
  change (if pattern.c then d213 (change pattern 10 10) else d209 (change pattern 10 10)) = d216 pattern
  rw [s126, s93]
  rfl
theorem s128 (pattern : Ten) : d217 (change pattern 10 10) = d217 pattern := by
  change (if pattern.c then d10 (change pattern 10 10) else d214 (change pattern 10 10)) = d217 pattern
  rw [s4, s94]
  rfl
theorem s129 (pattern : Ten) : d219 (change pattern 10 10) = d219 pattern := by
  change (if pattern.e then d217 (change pattern 10 10) else d216 (change pattern 10 10)) = d219 pattern
  rw [s128, s127]
  rfl
theorem s130 (pattern : Ten) : d220 (change pattern 10 10) = d220 pattern := by
  change (if pattern.d then d219 (change pattern 10 10) else d218 (change pattern 10 10)) = d220 pattern
  rw [s129, s125]
  rfl
theorem s131 (pattern : Ten) : d0 (change pattern 0 10) = d0 pattern := by
  rfl
theorem s132 (pattern : Ten) : d221 (change pattern 0 10) = d0 pattern := by
  change d0 (change pattern 0 10) = d0 pattern
  exact s131 pattern
theorem s133 (pattern : Ten) : d222 (change pattern 0 10) = d0 pattern := by
  change (if pattern.f then d0 (change pattern 0 10) else d221 (change pattern 0 10)) = d0 pattern
  rw [s131, s132]
  simp only [ite_self]
theorem s134 (pattern : Ten) : d223 (change pattern 0 10) = d0 pattern := by
  change (if pattern.j then d0 (change pattern 0 10) else d222 (change pattern 0 10)) = d0 pattern
  rw [s131, s133]
  simp only [ite_self]
theorem s135 (pattern : Ten) : d10 (change pattern 0 10) = d10 pattern := by
  rfl
theorem s136 (pattern : Ten) : d12 (change pattern 0 10) = d12 pattern := by
  change (if pattern.j then d10 (change pattern 0 10) else d0 (change pattern 0 10)) = d12 pattern
  rw [s135, s131]
  rfl
theorem s137 (pattern : Ten) : d224 (change pattern 0 10) = d17 pattern := by
  change (if pattern.i then d12 (change pattern 0 10) else d223 (change pattern 0 10)) = d17 pattern
  rw [s136, s134]
  rfl
theorem s138 (pattern : Ten) : d18 (change pattern 0 10) = d18 pattern := by
  change (if pattern.i then d10 (change pattern 0 10) else d12 (change pattern 0 10)) = d18 pattern
  rw [s135, s136]
  rfl
theorem s139 (pattern : Ten) : d225 (change pattern 0 10) = d23 pattern := by
  change (if pattern.h then d18 (change pattern 0 10) else d224 (change pattern 0 10)) = d23 pattern
  rw [s138, s137]
  rfl
theorem s140 (pattern : Ten) : d26 (change pattern 0 10) = d26 pattern := by
  change (if pattern.h then d10 (change pattern 0 10) else d18 (change pattern 0 10)) = d26 pattern
  rw [s135, s138]
  rfl
theorem s141 (pattern : Ten) : d226 (change pattern 0 10) = d408 pattern := by
  change (if pattern.g then d26 (change pattern 0 10) else d225 (change pattern 0 10)) = d408 pattern
  rw [s140, s139]
  rfl
theorem s142 (pattern : Ten) : d2 (change pattern 0 10) = d2 pattern := by
  rfl
theorem s143 (pattern : Ten) : d15 (change pattern 0 10) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 0 10) else d0 (change pattern 0 10)) = d15 pattern
  rw [s142, s131]
  rfl
theorem s144 (pattern : Ten) : d16 (change pattern 0 10) = d16 pattern := by
  change (if pattern.j then d10 (change pattern 0 10) else d2 (change pattern 0 10)) = d16 pattern
  rw [s135, s142]
  rfl
theorem s145 (pattern : Ten) : d21 (change pattern 0 10) = d21 pattern := by
  change (if pattern.i then d16 (change pattern 0 10) else d15 (change pattern 0 10)) = d21 pattern
  rw [s144, s143]
  rfl
theorem s146 (pattern : Ten) : d22 (change pattern 0 10) = d22 pattern := by
  change (if pattern.i then d10 (change pattern 0 10) else d16 (change pattern 0 10)) = d22 pattern
  rw [s135, s144]
  rfl
theorem s147 (pattern : Ten) : d25 (change pattern 0 10) = d25 pattern := by
  change (if pattern.h then d22 (change pattern 0 10) else d21 (change pattern 0 10)) = d25 pattern
  rw [s146, s145]
  rfl
theorem s148 (pattern : Ten) : d227 (change pattern 0 10) = d227 pattern := by
  change (if pattern.g then d26 (change pattern 0 10) else d25 (change pattern 0 10)) = d227 pattern
  rw [s140, s147]
  rfl
theorem s149 (pattern : Ten) : d230 (change pattern 0 10) = d409 pattern := by
  change (if pattern.c then d227 (change pattern 0 10) else d226 (change pattern 0 10)) = d409 pattern
  rw [s148, s141]
  rfl
end NetHack.Sokoban41.Diagram
