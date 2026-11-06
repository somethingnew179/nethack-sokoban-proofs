/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions01
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem s300 (pattern : Ten) : d38 (change pattern 10 3) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 10 3) else d7 (change pattern 10 3)) = d38 pattern
  rw [s299, s298]
  rfl
theorem s301 (pattern : Ten) : d40 (change pattern 10 3) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 10 3) else d38 (change pattern 10 3)) = d40 pattern
  rw [s299, s300]
  rfl
theorem s302 (pattern : Ten) : d10 (change pattern 10 3) = d10 pattern := by
  rfl
theorem s303 (pattern : Ten) : d46 (change pattern 10 3) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 10 3) else d40 (change pattern 10 3)) = d46 pattern
  rw [s302, s301]
  rfl
theorem s304 (pattern : Ten) : d52 (change pattern 10 3) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 10 3) else d46 (change pattern 10 3)) = d52 pattern
  rw [s302, s303]
  rfl
theorem s305 (pattern : Ten) : d56 (change pattern 10 3) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 10 3) else d52 (change pattern 10 3)) = d56 pattern
  rw [s302, s304]
  rfl
theorem s306 (pattern : Ten) : d60 (change pattern 10 3) = d60 pattern := by
  change (if pattern.g then d10 (change pattern 10 3) else d56 (change pattern 10 3)) = d60 pattern
  rw [s302, s305]
  rfl
theorem s307 (pattern : Ten) : d9 (change pattern 10 3) = d9 pattern := by
  rfl
theorem s308 (pattern : Ten) : d39 (change pattern 10 3) = d39 pattern := by
  change (if pattern.b then d10 (change pattern 10 3) else d9 (change pattern 10 3)) = d39 pattern
  rw [s302, s307]
  rfl
theorem s309 (pattern : Ten) : d41 (change pattern 10 3) = d41 pattern := by
  change (if pattern.a then d10 (change pattern 10 3) else d39 (change pattern 10 3)) = d41 pattern
  rw [s302, s308]
  rfl
theorem s310 (pattern : Ten) : d47 (change pattern 10 3) = d47 pattern := by
  change (if pattern.j then d10 (change pattern 10 3) else d41 (change pattern 10 3)) = d47 pattern
  rw [s302, s309]
  rfl
theorem s311 (pattern : Ten) : d53 (change pattern 10 3) = d53 pattern := by
  change (if pattern.i then d10 (change pattern 10 3) else d47 (change pattern 10 3)) = d53 pattern
  rw [s302, s310]
  rfl
theorem s312 (pattern : Ten) : d57 (change pattern 10 3) = d57 pattern := by
  change (if pattern.h then d10 (change pattern 10 3) else d53 (change pattern 10 3)) = d57 pattern
  rw [s302, s311]
  rfl
theorem s313 (pattern : Ten) : d61 (change pattern 10 3) = d61 pattern := by
  change (if pattern.g then d10 (change pattern 10 3) else d57 (change pattern 10 3)) = d61 pattern
  rw [s302, s312]
  rfl
theorem s314 (pattern : Ten) : d63 (change pattern 10 3) = d63 pattern := by
  change (if pattern.c then d61 (change pattern 10 3) else d60 (change pattern 10 3)) = d63 pattern
  rw [s313, s306]
  rfl
theorem s315 (pattern : Ten) : d65 (change pattern 10 3) = d65 pattern := by
  change (if pattern.e then d63 (change pattern 10 3) else d56 (change pattern 10 3)) = d65 pattern
  rw [s314, s305]
  rfl
theorem s316 (pattern : Ten) : d66 (change pattern 10 3) = d65 pattern := by
  change d65 (change pattern 10 3) = d65 pattern
  exact s315 pattern
theorem s317 (pattern : Ten) : d195 (change pattern 10 3) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 10 3) else d8 (change pattern 10 3)) = d195 pattern
  rw [s307, s299]
  rfl
theorem s318 (pattern : Ten) : d200 (change pattern 10 3) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 10 3) else d195 (change pattern 10 3)) = d200 pattern
  rw [s302, s317]
  rfl
theorem s319 (pattern : Ten) : d205 (change pattern 10 3) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 10 3) else d200 (change pattern 10 3)) = d205 pattern
  rw [s302, s318]
  rfl
theorem s320 (pattern : Ten) : d209 (change pattern 10 3) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 10 3) else d205 (change pattern 10 3)) = d209 pattern
  rw [s302, s319]
  rfl
theorem s321 (pattern : Ten) : d11 (change pattern 10 3) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 10 3) else d9 (change pattern 10 3)) = d11 pattern
  rw [s302, s307]
  rfl
theorem s322 (pattern : Ten) : d196 (change pattern 10 3) = d196 pattern := by
  change (if pattern.f then d11 (change pattern 10 3) else d195 (change pattern 10 3)) = d196 pattern
  rw [s321, s317]
  rfl
theorem s323 (pattern : Ten) : d201 (change pattern 10 3) = d201 pattern := by
  change (if pattern.j then d10 (change pattern 10 3) else d196 (change pattern 10 3)) = d201 pattern
  rw [s302, s322]
  rfl
theorem s324 (pattern : Ten) : d206 (change pattern 10 3) = d206 pattern := by
  change (if pattern.i then d10 (change pattern 10 3) else d201 (change pattern 10 3)) = d206 pattern
  rw [s302, s323]
  rfl
theorem s325 (pattern : Ten) : d210 (change pattern 10 3) = d210 pattern := by
  change (if pattern.h then d10 (change pattern 10 3) else d206 (change pattern 10 3)) = d210 pattern
  rw [s302, s324]
  rfl
theorem s326 (pattern : Ten) : d213 (change pattern 10 3) = d213 pattern := by
  change (if pattern.g then d210 (change pattern 10 3) else d209 (change pattern 10 3)) = d213 pattern
  rw [s325, s320]
  rfl
theorem s327 (pattern : Ten) : d216 (change pattern 10 3) = d216 pattern := by
  change (if pattern.c then d213 (change pattern 10 3) else d209 (change pattern 10 3)) = d216 pattern
  rw [s326, s320]
  rfl
theorem s328 (pattern : Ten) : d214 (change pattern 10 3) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 10 3) else d209 (change pattern 10 3)) = d214 pattern
  rw [s302, s320]
  rfl
theorem s329 (pattern : Ten) : d217 (change pattern 10 3) = d217 pattern := by
  change (if pattern.c then d10 (change pattern 10 3) else d214 (change pattern 10 3)) = d217 pattern
  rw [s302, s328]
  rfl
theorem s330 (pattern : Ten) : d219 (change pattern 10 3) = d219 pattern := by
  change (if pattern.e then d217 (change pattern 10 3) else d216 (change pattern 10 3)) = d219 pattern
  rw [s329, s327]
  rfl
theorem s331 (pattern : Ten) : d220 (change pattern 10 3) = d219 pattern := by
  change d219 (change pattern 10 3) = d219 pattern
  exact s330 pattern
theorem s332 (pattern : Ten) : d0 (change pattern 2 10) = d0 pattern := by
  rfl
theorem s333 (pattern : Ten) : d1 (change pattern 2 10) = d1 pattern := by
  rfl
theorem s334 (pattern : Ten) : d171 (change pattern 2 10) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 2 10) else d0 (change pattern 2 10)) = d171 pattern
  rw [s333, s332]
  rfl
theorem s335 (pattern : Ten) : d2 (change pattern 2 10) = d2 pattern := by
  rfl
theorem s336 (pattern : Ten) : d3 (change pattern 2 10) = d3 pattern := by
  rfl
theorem s337 (pattern : Ten) : d172 (change pattern 2 10) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 2 10) else d2 (change pattern 2 10)) = d172 pattern
  rw [s336, s335]
  rfl
theorem s338 (pattern : Ten) : d174 (change pattern 2 10) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 2 10) else d171 (change pattern 2 10)) = d174 pattern
  rw [s337, s334]
  rfl
theorem s339 (pattern : Ten) : d4 (change pattern 2 10) = d4 pattern := by
  rfl
theorem s340 (pattern : Ten) : d5 (change pattern 2 10) = d5 pattern := by
  rfl
theorem s341 (pattern : Ten) : d193 (change pattern 2 10) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 2 10) else d4 (change pattern 2 10)) = d193 pattern
  rw [s340, s339]
  rfl
theorem s342 (pattern : Ten) : d10 (change pattern 2 10) = d10 pattern := by
  rfl
theorem s343 (pattern : Ten) : d197 (change pattern 2 10) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d193 (change pattern 2 10)) = d197 pattern
  rw [s342, s341]
  rfl
theorem s344 (pattern : Ten) : d202 (change pattern 2 10) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 2 10) else d174 (change pattern 2 10)) = d202 pattern
  rw [s343, s338]
  rfl
theorem s345 (pattern : Ten) : d6 (change pattern 2 10) = d6 pattern := by
  rfl
theorem s346 (pattern : Ten) : d7 (change pattern 2 10) = d7 pattern := by
  rfl
theorem s347 (pattern : Ten) : d194 (change pattern 2 10) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 2 10) else d6 (change pattern 2 10)) = d194 pattern
  rw [s346, s345]
  rfl
theorem s348 (pattern : Ten) : d198 (change pattern 2 10) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d194 (change pattern 2 10)) = d198 pattern
  rw [s342, s347]
  rfl
theorem s349 (pattern : Ten) : d203 (change pattern 2 10) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 2 10) else d198 (change pattern 2 10)) = d203 pattern
  rw [s342, s348]
  rfl
theorem s350 (pattern : Ten) : d207 (change pattern 2 10) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 2 10) else d202 (change pattern 2 10)) = d207 pattern
  rw [s349, s344]
  rfl
theorem s351 (pattern : Ten) : d235 (change pattern 2 10) = d207 pattern := by
  change d207 (change pattern 2 10) = d207 pattern
  exact s350 pattern
theorem s352 (pattern : Ten) : d211 (change pattern 2 10) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 2 10) else d207 (change pattern 2 10)) = d211 pattern
  rw [s342, s350]
  rfl
theorem s353 (pattern : Ten) : d236 (change pattern 2 10) = d434 pattern := by
  change (if pattern.e then d211 (change pattern 2 10) else d235 (change pattern 2 10)) = d434 pattern
  rw [s352, s351]
  rfl
theorem s354 (pattern : Ten) : d8 (change pattern 2 10) = d8 pattern := by
  rfl
theorem s355 (pattern : Ten) : d9 (change pattern 2 10) = d9 pattern := by
  rfl
theorem s356 (pattern : Ten) : d195 (change pattern 2 10) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 2 10) else d8 (change pattern 2 10)) = d195 pattern
  rw [s355, s354]
  rfl
theorem s357 (pattern : Ten) : d200 (change pattern 2 10) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d195 (change pattern 2 10)) = d200 pattern
  rw [s342, s356]
  rfl
theorem s358 (pattern : Ten) : d205 (change pattern 2 10) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 2 10) else d200 (change pattern 2 10)) = d205 pattern
  rw [s342, s357]
  rfl
theorem s359 (pattern : Ten) : d209 (change pattern 2 10) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 2 10) else d205 (change pattern 2 10)) = d209 pattern
  rw [s342, s358]
  rfl
theorem s360 (pattern : Ten) : d214 (change pattern 2 10) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 2 10) else d209 (change pattern 2 10)) = d214 pattern
  rw [s342, s359]
  rfl
theorem s361 (pattern : Ten) : d237 (change pattern 2 10) = d237 pattern := by
  change (if pattern.e then d214 (change pattern 2 10) else d209 (change pattern 2 10)) = d237 pattern
  rw [s360, s359]
  rfl
theorem s362 (pattern : Ten) : d238 (change pattern 2 10) = d435 pattern := by
  change (if pattern.d then d237 (change pattern 2 10) else d236 (change pattern 2 10)) = d435 pattern
  rw [s361, s353]
  rfl
theorem s363 (pattern : Ten) : d0 (change pattern 2 4) = d0 pattern := by
  rfl
theorem s364 (pattern : Ten) : d2 (change pattern 2 4) = d2 pattern := by
  rfl
theorem s365 (pattern : Ten) : d15 (change pattern 2 4) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 2 4) else d0 (change pattern 2 4)) = d15 pattern
  rw [s364, s363]
  rfl
theorem s366 (pattern : Ten) : d4 (change pattern 2 4) = d4 pattern := by
  rfl
theorem s367 (pattern : Ten) : d10 (change pattern 2 4) = d10 pattern := by
  rfl
theorem s368 (pattern : Ten) : d42 (change pattern 2 4) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d4 (change pattern 2 4)) = d42 pattern
  rw [s367, s366]
  rfl
theorem s369 (pattern : Ten) : d48 (change pattern 2 4) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 2 4) else d15 (change pattern 2 4)) = d48 pattern
  rw [s368, s365]
  rfl
theorem s370 (pattern : Ten) : d6 (change pattern 2 4) = d6 pattern := by
  rfl
theorem s371 (pattern : Ten) : d43 (change pattern 2 4) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d6 (change pattern 2 4)) = d43 pattern
  rw [s367, s370]
  rfl
theorem s372 (pattern : Ten) : d49 (change pattern 2 4) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 2 4) else d43 (change pattern 2 4)) = d49 pattern
  rw [s367, s371]
  rfl
theorem s373 (pattern : Ten) : d54 (change pattern 2 4) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 2 4) else d48 (change pattern 2 4)) = d54 pattern
  rw [s372, s369]
  rfl
theorem s374 (pattern : Ten) : d9 (change pattern 2 4) = d9 pattern := by
  rfl
theorem s375 (pattern : Ten) : d11 (change pattern 2 4) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 2 4) else d9 (change pattern 2 4)) = d11 pattern
  rw [s367, s374]
  rfl
theorem s376 (pattern : Ten) : d14 (change pattern 2 4) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d11 (change pattern 2 4)) = d14 pattern
  rw [s367, s375]
  rfl
theorem s377 (pattern : Ten) : d20 (change pattern 2 4) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 2 4) else d14 (change pattern 2 4)) = d20 pattern
  rw [s367, s376]
  rfl
theorem s378 (pattern : Ten) : d27 (change pattern 2 4) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 2 4) else d20 (change pattern 2 4)) = d27 pattern
  rw [s367, s377]
  rfl
theorem s379 (pattern : Ten) : d58 (change pattern 2 4) = d58 pattern := by
  change (if pattern.g then d27 (change pattern 2 4) else d54 (change pattern 2 4)) = d58 pattern
  rw [s378, s373]
  rfl
theorem s380 (pattern : Ten) : d83 (change pattern 2 4) = d58 pattern := by
  change d58 (change pattern 2 4) = d58 pattern
  exact s379 pattern
theorem s381 (pattern : Ten) : d7 (change pattern 2 4) = d7 pattern := by
  rfl
theorem s382 (pattern : Ten) : d8 (change pattern 2 4) = d8 pattern := by
  rfl
theorem s383 (pattern : Ten) : d38 (change pattern 2 4) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 2 4) else d7 (change pattern 2 4)) = d38 pattern
  rw [s382, s381]
  rfl
theorem s384 (pattern : Ten) : d40 (change pattern 2 4) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 2 4) else d38 (change pattern 2 4)) = d40 pattern
  rw [s382, s383]
  rfl
theorem s385 (pattern : Ten) : d46 (change pattern 2 4) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d40 (change pattern 2 4)) = d46 pattern
  rw [s367, s384]
  rfl
theorem s386 (pattern : Ten) : d52 (change pattern 2 4) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 2 4) else d46 (change pattern 2 4)) = d52 pattern
  rw [s367, s385]
  rfl
theorem s387 (pattern : Ten) : d56 (change pattern 2 4) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 2 4) else d52 (change pattern 2 4)) = d56 pattern
  rw [s367, s386]
  rfl
theorem s388 (pattern : Ten) : d60 (change pattern 2 4) = d60 pattern := by
  change (if pattern.g then d10 (change pattern 2 4) else d56 (change pattern 2 4)) = d60 pattern
  rw [s367, s387]
  rfl
theorem s389 (pattern : Ten) : d84 (change pattern 2 4) = d60 pattern := by
  change d60 (change pattern 2 4) = d60 pattern
  exact s388 pattern
theorem s390 (pattern : Ten) : d85 (change pattern 2 4) = d437 pattern := by
  change (if pattern.d then d84 (change pattern 2 4) else d83 (change pattern 2 4)) = d437 pattern
  rw [s389, s380]
  rfl
theorem s391 (pattern : Ten) : d1 (change pattern 2 4) = d1 pattern := by
  rfl
theorem s392 (pattern : Ten) : d171 (change pattern 2 4) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 2 4) else d0 (change pattern 2 4)) = d171 pattern
  rw [s391, s363]
  rfl
theorem s393 (pattern : Ten) : d3 (change pattern 2 4) = d3 pattern := by
  rfl
theorem s394 (pattern : Ten) : d172 (change pattern 2 4) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 2 4) else d2 (change pattern 2 4)) = d172 pattern
  rw [s393, s364]
  rfl
theorem s395 (pattern : Ten) : d174 (change pattern 2 4) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 2 4) else d171 (change pattern 2 4)) = d174 pattern
  rw [s394, s392]
  rfl
theorem s396 (pattern : Ten) : d5 (change pattern 2 4) = d5 pattern := by
  rfl
theorem s397 (pattern : Ten) : d193 (change pattern 2 4) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 2 4) else d4 (change pattern 2 4)) = d193 pattern
  rw [s396, s366]
  rfl
theorem s398 (pattern : Ten) : d197 (change pattern 2 4) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d193 (change pattern 2 4)) = d197 pattern
  rw [s367, s397]
  rfl
theorem s399 (pattern : Ten) : d202 (change pattern 2 4) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 2 4) else d174 (change pattern 2 4)) = d202 pattern
  rw [s398, s395]
  rfl
theorem s400 (pattern : Ten) : d194 (change pattern 2 4) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 2 4) else d6 (change pattern 2 4)) = d194 pattern
  rw [s381, s370]
  rfl
theorem s401 (pattern : Ten) : d198 (change pattern 2 4) = d198 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d194 (change pattern 2 4)) = d198 pattern
  rw [s367, s400]
  rfl
theorem s402 (pattern : Ten) : d203 (change pattern 2 4) = d203 pattern := by
  change (if pattern.i then d10 (change pattern 2 4) else d198 (change pattern 2 4)) = d203 pattern
  rw [s367, s401]
  rfl
theorem s403 (pattern : Ten) : d207 (change pattern 2 4) = d207 pattern := by
  change (if pattern.h then d203 (change pattern 2 4) else d202 (change pattern 2 4)) = d207 pattern
  rw [s402, s399]
  rfl
theorem s404 (pattern : Ten) : d211 (change pattern 2 4) = d211 pattern := by
  change (if pattern.g then d10 (change pattern 2 4) else d207 (change pattern 2 4)) = d211 pattern
  rw [s367, s403]
  rfl
theorem s405 (pattern : Ten) : d236 (change pattern 2 4) = d211 pattern := by
  change d211 (change pattern 2 4) = d211 pattern
  exact s404 pattern
theorem s406 (pattern : Ten) : d195 (change pattern 2 4) = d195 pattern := by
  change (if pattern.a then d9 (change pattern 2 4) else d8 (change pattern 2 4)) = d195 pattern
  rw [s374, s382]
  rfl
theorem s407 (pattern : Ten) : d200 (change pattern 2 4) = d200 pattern := by
  change (if pattern.j then d10 (change pattern 2 4) else d195 (change pattern 2 4)) = d200 pattern
  rw [s367, s406]
  rfl
theorem s408 (pattern : Ten) : d205 (change pattern 2 4) = d205 pattern := by
  change (if pattern.i then d10 (change pattern 2 4) else d200 (change pattern 2 4)) = d205 pattern
  rw [s367, s407]
  rfl
theorem s409 (pattern : Ten) : d209 (change pattern 2 4) = d209 pattern := by
  change (if pattern.h then d10 (change pattern 2 4) else d205 (change pattern 2 4)) = d209 pattern
  rw [s367, s408]
  rfl
theorem s410 (pattern : Ten) : d214 (change pattern 2 4) = d214 pattern := by
  change (if pattern.g then d10 (change pattern 2 4) else d209 (change pattern 2 4)) = d214 pattern
  rw [s367, s409]
  rfl
theorem s411 (pattern : Ten) : d237 (change pattern 2 4) = d214 pattern := by
  change d214 (change pattern 2 4) = d214 pattern
  exact s410 pattern
theorem s412 (pattern : Ten) : d238 (change pattern 2 4) = d438 pattern := by
  change (if pattern.d then d237 (change pattern 2 4) else d236 (change pattern 2 4)) = d438 pattern
  rw [s411, s405]
  rfl
theorem s413 (pattern : Ten) : d15 (change pattern 2 10) = d15 pattern := by
  change (if pattern.j then d2 (change pattern 2 10) else d0 (change pattern 2 10)) = d15 pattern
  rw [s335, s332]
  rfl
theorem s414 (pattern : Ten) : d42 (change pattern 2 10) = d42 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d4 (change pattern 2 10)) = d42 pattern
  rw [s342, s339]
  rfl
theorem s415 (pattern : Ten) : d48 (change pattern 2 10) = d48 pattern := by
  change (if pattern.i then d42 (change pattern 2 10) else d15 (change pattern 2 10)) = d48 pattern
  rw [s414, s413]
  rfl
theorem s416 (pattern : Ten) : d43 (change pattern 2 10) = d43 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d6 (change pattern 2 10)) = d43 pattern
  rw [s342, s345]
  rfl
theorem s417 (pattern : Ten) : d49 (change pattern 2 10) = d49 pattern := by
  change (if pattern.i then d10 (change pattern 2 10) else d43 (change pattern 2 10)) = d49 pattern
  rw [s342, s416]
  rfl
theorem s418 (pattern : Ten) : d54 (change pattern 2 10) = d54 pattern := by
  change (if pattern.h then d49 (change pattern 2 10) else d48 (change pattern 2 10)) = d54 pattern
  rw [s417, s415]
  rfl
theorem s419 (pattern : Ten) : d82 (change pattern 2 10) = d54 pattern := by
  change d54 (change pattern 2 10) = d54 pattern
  exact s418 pattern
theorem s420 (pattern : Ten) : d11 (change pattern 2 10) = d11 pattern := by
  change (if pattern.a then d10 (change pattern 2 10) else d9 (change pattern 2 10)) = d11 pattern
  rw [s342, s355]
  rfl
theorem s421 (pattern : Ten) : d14 (change pattern 2 10) = d14 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d11 (change pattern 2 10)) = d14 pattern
  rw [s342, s420]
  rfl
theorem s422 (pattern : Ten) : d20 (change pattern 2 10) = d20 pattern := by
  change (if pattern.i then d10 (change pattern 2 10) else d14 (change pattern 2 10)) = d20 pattern
  rw [s342, s421]
  rfl
theorem s423 (pattern : Ten) : d27 (change pattern 2 10) = d27 pattern := by
  change (if pattern.h then d10 (change pattern 2 10) else d20 (change pattern 2 10)) = d27 pattern
  rw [s342, s422]
  rfl
theorem s424 (pattern : Ten) : d58 (change pattern 2 10) = d58 pattern := by
  change (if pattern.g then d27 (change pattern 2 10) else d54 (change pattern 2 10)) = d58 pattern
  rw [s423, s418]
  rfl
theorem s425 (pattern : Ten) : d83 (change pattern 2 10) = d439 pattern := by
  change (if pattern.e then d58 (change pattern 2 10) else d82 (change pattern 2 10)) = d439 pattern
  rw [s424, s419]
  rfl
theorem s426 (pattern : Ten) : d38 (change pattern 2 10) = d38 pattern := by
  change (if pattern.b then d8 (change pattern 2 10) else d7 (change pattern 2 10)) = d38 pattern
  rw [s354, s346]
  rfl
theorem s427 (pattern : Ten) : d40 (change pattern 2 10) = d40 pattern := by
  change (if pattern.a then d8 (change pattern 2 10) else d38 (change pattern 2 10)) = d40 pattern
  rw [s354, s426]
  rfl
theorem s428 (pattern : Ten) : d46 (change pattern 2 10) = d46 pattern := by
  change (if pattern.j then d10 (change pattern 2 10) else d40 (change pattern 2 10)) = d46 pattern
  rw [s342, s427]
  rfl
theorem s429 (pattern : Ten) : d52 (change pattern 2 10) = d52 pattern := by
  change (if pattern.i then d10 (change pattern 2 10) else d46 (change pattern 2 10)) = d52 pattern
  rw [s342, s428]
  rfl
theorem s430 (pattern : Ten) : d56 (change pattern 2 10) = d56 pattern := by
  change (if pattern.h then d10 (change pattern 2 10) else d52 (change pattern 2 10)) = d56 pattern
  rw [s342, s429]
  rfl
theorem s431 (pattern : Ten) : d60 (change pattern 2 10) = d60 pattern := by
  change (if pattern.g then d10 (change pattern 2 10) else d56 (change pattern 2 10)) = d60 pattern
  rw [s342, s430]
  rfl
theorem s432 (pattern : Ten) : d84 (change pattern 2 10) = d84 pattern := by
  change (if pattern.e then d60 (change pattern 2 10) else d56 (change pattern 2 10)) = d84 pattern
  rw [s431, s430]
  rfl
theorem s433 (pattern : Ten) : d85 (change pattern 2 10) = d440 pattern := by
  change (if pattern.d then d84 (change pattern 2 10) else d83 (change pattern 2 10)) = d440 pattern
  rw [s432, s425]
  rfl
theorem s434 (pattern : Ten) : d0 (change pattern 10 5) = d0 pattern := by
  rfl
theorem s435 (pattern : Ten) : d1 (change pattern 10 5) = d1 pattern := by
  rfl
theorem s436 (pattern : Ten) : d171 (change pattern 10 5) = d171 pattern := by
  change (if pattern.a then d1 (change pattern 10 5) else d0 (change pattern 10 5)) = d171 pattern
  rw [s435, s434]
  rfl
theorem s437 (pattern : Ten) : d2 (change pattern 10 5) = d2 pattern := by
  rfl
theorem s438 (pattern : Ten) : d3 (change pattern 10 5) = d3 pattern := by
  rfl
theorem s439 (pattern : Ten) : d172 (change pattern 10 5) = d172 pattern := by
  change (if pattern.a then d3 (change pattern 10 5) else d2 (change pattern 10 5)) = d172 pattern
  rw [s438, s437]
  rfl
theorem s440 (pattern : Ten) : d174 (change pattern 10 5) = d174 pattern := by
  change (if pattern.j then d172 (change pattern 10 5) else d171 (change pattern 10 5)) = d174 pattern
  rw [s439, s436]
  rfl
theorem s441 (pattern : Ten) : d4 (change pattern 10 5) = d4 pattern := by
  rfl
theorem s442 (pattern : Ten) : d5 (change pattern 10 5) = d5 pattern := by
  rfl
theorem s443 (pattern : Ten) : d193 (change pattern 10 5) = d193 pattern := by
  change (if pattern.a then d5 (change pattern 10 5) else d4 (change pattern 10 5)) = d193 pattern
  rw [s442, s441]
  rfl
theorem s444 (pattern : Ten) : d10 (change pattern 10 5) = d10 pattern := by
  rfl
theorem s445 (pattern : Ten) : d197 (change pattern 10 5) = d197 pattern := by
  change (if pattern.j then d10 (change pattern 10 5) else d193 (change pattern 10 5)) = d197 pattern
  rw [s444, s443]
  rfl
theorem s446 (pattern : Ten) : d202 (change pattern 10 5) = d202 pattern := by
  change (if pattern.i then d197 (change pattern 10 5) else d174 (change pattern 10 5)) = d202 pattern
  rw [s445, s440]
  rfl
theorem s447 (pattern : Ten) : d6 (change pattern 10 5) = d6 pattern := by
  rfl
theorem s448 (pattern : Ten) : d7 (change pattern 10 5) = d7 pattern := by
  rfl
theorem s449 (pattern : Ten) : d194 (change pattern 10 5) = d194 pattern := by
  change (if pattern.a then d7 (change pattern 10 5) else d6 (change pattern 10 5)) = d194 pattern
  rw [s448, s447]
  rfl
end NetHack.Sokoban41.Diagram
