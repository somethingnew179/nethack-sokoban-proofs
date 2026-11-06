import NetHack.Soko22Hazard87.OracleCases02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases300 : List OracleBranch := [((.walk 80), d1)]
theorem oracleMember267 : ((.walk 80), d1) ∈ rowCases300 := by
  exact List.mem_cons_self
noncomputable def rowCases301 : List OracleBranch := [((.walk 78), d1)]
theorem oracleMember268 : ((.walk 78), d1) ∈ rowCases301 := by
  exact List.mem_cons_self
noncomputable def rowCases302 : List OracleBranch := [((.walk 124), d1)]
theorem oracleMember269 : ((.walk 124), d1) ∈ rowCases302 := by
  exact List.mem_cons_self
noncomputable def rowCases303 : List OracleBranch := [((.walk 122), d1)]
theorem oracleMember270 : ((.walk 122), d1) ∈ rowCases303 := by
  exact List.mem_cons_self
noncomputable def rowCases304 : List OracleBranch := [((.walk 80), d1)]
theorem oracleMember271 : ((.walk 80), d1) ∈ rowCases304 := by
  exact List.mem_cons_self
noncomputable def rowCases305 : List OracleBranch := [((.walk 124), d1), ((.push 124 (.stay 146)), d0)]
theorem oracleMember272 : ((.walk 124), d1) ∈ rowCases305 := by
  exact List.mem_cons_self
theorem oracleMember273 : ((.push 124 (.stay 146)), d0) ∈ rowCases305 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases306 : List OracleBranch := [((.walk 103), d1), ((.push 103 (.stay 104)), d0)]
theorem oracleMember274 : ((.walk 103), d1) ∈ rowCases306 := by
  exact List.mem_cons_self
theorem oracleMember275 : ((.push 103 (.stay 104)), d0) ∈ rowCases306 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases307 : List OracleBranch := [((.walk 101), d1), ((.push 101 (.stay 100)), d0)]
theorem oracleMember276 : ((.walk 101), d1) ∈ rowCases307 := by
  exact List.mem_cons_self
theorem oracleMember277 : ((.push 101 (.stay 100)), d0) ∈ rowCases307 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases308 : List OracleBranch := [((.walk 81), d1)]
theorem oracleMember278 : ((.walk 81), d1) ∈ rowCases308 := by
  exact List.mem_cons_self
noncomputable def rowCases309 : List OracleBranch := [((.walk 79), d1)]
theorem oracleMember279 : ((.walk 79), d1) ∈ rowCases309 := by
  exact List.mem_cons_self
noncomputable def rowCases310 : List OracleBranch := [((.walk 125), d1)]
theorem oracleMember280 : ((.walk 125), d1) ∈ rowCases310 := by
  exact List.mem_cons_self
noncomputable def rowCases311 : List OracleBranch := [((.walk 123), d1)]
theorem oracleMember281 : ((.walk 123), d1) ∈ rowCases311 := by
  exact List.mem_cons_self
noncomputable def rowCases312 : List OracleBranch := [((.walk 81), d1)]
theorem oracleMember282 : ((.walk 81), d1) ∈ rowCases312 := by
  exact List.mem_cons_self
noncomputable def rowCases313 : List OracleBranch := [((.walk 125), d1), ((.push 125 (.stay 147)), d0)]
theorem oracleMember283 : ((.walk 125), d1) ∈ rowCases313 := by
  exact List.mem_cons_self
theorem oracleMember284 : ((.push 125 (.stay 147)), d0) ∈ rowCases313 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases314 : List OracleBranch := [((.walk 104), d1), ((.push 104 (.stay 105)), d0)]
theorem oracleMember285 : ((.walk 104), d1) ∈ rowCases314 := by
  exact List.mem_cons_self
theorem oracleMember286 : ((.push 104 (.stay 105)), d0) ∈ rowCases314 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases315 : List OracleBranch := [((.walk 102), d1), ((.push 102 (.stay 101)), d0)]
theorem oracleMember287 : ((.walk 102), d1) ∈ rowCases315 := by
  exact List.mem_cons_self
theorem oracleMember288 : ((.push 102 (.stay 101)), d0) ∈ rowCases315 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases316 : List OracleBranch := [((.walk 82), d1)]
theorem oracleMember289 : ((.walk 82), d1) ∈ rowCases316 := by
  exact List.mem_cons_self
noncomputable def rowCases317 : List OracleBranch := [((.walk 80), d1)]
theorem oracleMember290 : ((.walk 80), d1) ∈ rowCases317 := by
  exact List.mem_cons_self
noncomputable def rowCases318 : List OracleBranch := [((.walk 126), d1)]
theorem oracleMember291 : ((.walk 126), d1) ∈ rowCases318 := by
  exact List.mem_cons_self
noncomputable def rowCases319 : List OracleBranch := [((.walk 124), d1)]
theorem oracleMember292 : ((.walk 124), d1) ∈ rowCases319 := by
  exact List.mem_cons_self
noncomputable def rowCases320 : List OracleBranch := [((.walk 82), d1)]
theorem oracleMember293 : ((.walk 82), d1) ∈ rowCases320 := by
  exact List.mem_cons_self
noncomputable def rowCases321 : List OracleBranch := [((.walk 126), d1), ((.push 126 (.stay 148)), d0)]
theorem oracleMember294 : ((.walk 126), d1) ∈ rowCases321 := by
  exact List.mem_cons_self
theorem oracleMember295 : ((.push 126 (.stay 148)), d0) ∈ rowCases321 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases322 : List OracleBranch := [((.walk 105), d1), ((.push 105 (.stay 106)), d0)]
theorem oracleMember296 : ((.walk 105), d1) ∈ rowCases322 := by
  exact List.mem_cons_self
theorem oracleMember297 : ((.push 105 (.stay 106)), d0) ∈ rowCases322 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases323 : List OracleBranch := [((.walk 103), d1), ((.push 103 (.stay 102)), d0)]
theorem oracleMember298 : ((.walk 103), d1) ∈ rowCases323 := by
  exact List.mem_cons_self
theorem oracleMember299 : ((.push 103 (.stay 102)), d0) ∈ rowCases323 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases324 : List OracleBranch := [((.walk 83), d1)]
theorem oracleMember300 : ((.walk 83), d1) ∈ rowCases324 := by
  exact List.mem_cons_self
noncomputable def rowCases325 : List OracleBranch := [((.walk 81), d1)]
theorem oracleMember301 : ((.walk 81), d1) ∈ rowCases325 := by
  exact List.mem_cons_self
noncomputable def rowCases326 : List OracleBranch := [((.walk 127), d1)]
theorem oracleMember302 : ((.walk 127), d1) ∈ rowCases326 := by
  exact List.mem_cons_self
noncomputable def rowCases327 : List OracleBranch := [((.walk 125), d1)]
theorem oracleMember303 : ((.walk 125), d1) ∈ rowCases327 := by
  exact List.mem_cons_self
noncomputable def rowCases328 : List OracleBranch := [((.walk 83), d1)]
theorem oracleMember304 : ((.walk 83), d1) ∈ rowCases328 := by
  exact List.mem_cons_self
noncomputable def rowCases329 : List OracleBranch := [((.walk 127), d1), ((.push 127 (.stay 149)), d0)]
theorem oracleMember305 : ((.walk 127), d1) ∈ rowCases329 := by
  exact List.mem_cons_self
theorem oracleMember306 : ((.push 127 (.stay 149)), d0) ∈ rowCases329 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases330 : List OracleBranch := [((.walk 106), d1)]
theorem oracleMember307 : ((.walk 106), d1) ∈ rowCases330 := by
  exact List.mem_cons_self
noncomputable def rowCases331 : List OracleBranch := [((.walk 104), d1), ((.push 104 (.stay 103)), d0)]
theorem oracleMember308 : ((.walk 104), d1) ∈ rowCases331 := by
  exact List.mem_cons_self
theorem oracleMember309 : ((.push 104 (.stay 103)), d0) ∈ rowCases331 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases332 : List OracleBranch := [((.walk 84), d1)]
theorem oracleMember310 : ((.walk 84), d1) ∈ rowCases332 := by
  exact List.mem_cons_self
noncomputable def rowCases333 : List OracleBranch := [((.walk 82), d1)]
theorem oracleMember311 : ((.walk 82), d1) ∈ rowCases333 := by
  exact List.mem_cons_self
noncomputable def rowCases334 : List OracleBranch := [((.walk 128), d1)]
theorem oracleMember312 : ((.walk 128), d1) ∈ rowCases334 := by
  exact List.mem_cons_self
noncomputable def rowCases335 : List OracleBranch := [((.walk 126), d1)]
theorem oracleMember313 : ((.walk 126), d1) ∈ rowCases335 := by
  exact List.mem_cons_self
noncomputable def rowCases336 : List OracleBranch := [((.walk 84), d1)]
theorem oracleMember314 : ((.walk 84), d1) ∈ rowCases336 := by
  exact List.mem_cons_self
noncomputable def rowCases337 : List OracleBranch := [((.walk 128), d1), ((.push 128 (.stay 150)), d0)]
theorem oracleMember315 : ((.walk 128), d1) ∈ rowCases337 := by
  exact List.mem_cons_self
theorem oracleMember316 : ((.push 128 (.stay 150)), d0) ∈ rowCases337 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases338 : List OracleBranch := []
noncomputable def rowCases339 : List OracleBranch := [((.walk 105), d1), ((.push 105 (.stay 104)), d0)]
theorem oracleMember317 : ((.walk 105), d1) ∈ rowCases339 := by
  exact List.mem_cons_self
theorem oracleMember318 : ((.push 105 (.stay 104)), d0) ∈ rowCases339 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases340 : List OracleBranch := []
noncomputable def rowCases341 : List OracleBranch := [((.walk 83), d1)]
theorem oracleMember319 : ((.walk 83), d1) ∈ rowCases341 := by
  exact List.mem_cons_self
noncomputable def rowCases342 : List OracleBranch := []
noncomputable def rowCases343 : List OracleBranch := [((.walk 127), d1)]
theorem oracleMember320 : ((.walk 127), d1) ∈ rowCases343 := by
  exact List.mem_cons_self
noncomputable def rowCases344 : List OracleBranch := [((.walk 89), d74075), ((.push 89 (.stay 67)), d67924)]
theorem oracleMember321 : ((.walk 89), d74075) ∈ rowCases344 := by
  exact List.mem_cons_self
theorem oracleMember322 : ((.push 89 (.stay 67)), d67924) ∈ rowCases344 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases345 : List OracleBranch := [((.walk 133), d82685), ((.push 133 (.stay 155)), d82690)]
theorem oracleMember323 : ((.walk 133), d82685) ∈ rowCases345 := by
  exact List.mem_cons_self
theorem oracleMember324 : ((.push 133 (.stay 155)), d82690) ∈ rowCases345 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases346 : List OracleBranch := []
noncomputable def rowCases347 : List OracleBranch := []
noncomputable def rowCases348 : List OracleBranch := [((.walk 90), d77113)]
theorem oracleMember325 : ((.walk 90), d77113) ∈ rowCases348 := by
  exact List.mem_cons_self
noncomputable def rowCases349 : List OracleBranch := []
noncomputable def rowCases350 : List OracleBranch := [((.walk 134), d82694)]
theorem oracleMember326 : ((.walk 134), d82694) ∈ rowCases350 := by
  exact List.mem_cons_self
noncomputable def rowCases351 : List OracleBranch := []
noncomputable def rowCases352 : List OracleBranch := [((.walk 91), d75629), ((.push 91 (.stay 69)), d70148)]
theorem oracleMember327 : ((.walk 91), d75629) ∈ rowCases352 := by
  exact List.mem_cons_self
theorem oracleMember328 : ((.push 91 (.stay 69)), d70148) ∈ rowCases352 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases353 : List OracleBranch := [((.walk 135), d83662), ((.push 135 (.stay 157)), d85724)]
theorem oracleMember329 : ((.walk 135), d83662) ∈ rowCases353 := by
  exact List.mem_cons_self
theorem oracleMember330 : ((.push 135 (.stay 157)), d85724) ∈ rowCases353 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases354 : List OracleBranch := [((.walk 114), d89600), ((.push 114 (.stay 115)), d89603)]
theorem oracleMember331 : ((.walk 114), d89600) ∈ rowCases354 := by
  exact List.mem_cons_self
theorem oracleMember332 : ((.push 114 (.stay 115)), d89603) ∈ rowCases354 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases355 : List OracleBranch := []
noncomputable def rowCases356 : List OracleBranch := []
noncomputable def rowCases357 : List OracleBranch := [((.walk 90), d75630)]
theorem oracleMember333 : ((.walk 90), d75630) ∈ rowCases357 := by
  exact List.mem_cons_self
noncomputable def rowCases358 : List OracleBranch := [((.walk 136), d92317)]
theorem oracleMember334 : ((.walk 136), d92317) ∈ rowCases358 := by
  exact List.mem_cons_self
noncomputable def rowCases359 : List OracleBranch := [((.walk 134), d94517)]
theorem oracleMember335 : ((.walk 134), d94517) ∈ rowCases359 := by
  exact List.mem_cons_self
noncomputable def rowCases360 : List OracleBranch := []
noncomputable def rowCases361 : List OracleBranch := [((.walk 136), d94518), ((.push 136 (.stay 158)), d94756)]
theorem oracleMember336 : ((.walk 136), d94518) ∈ rowCases361 := by
  exact List.mem_cons_self
theorem oracleMember337 : ((.push 136 (.stay 158)), d94756) ∈ rowCases361 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases362 : List OracleBranch := [((.walk 115), d98788), ((.push 115 (.stay 116)), d98791)]
theorem oracleMember338 : ((.walk 115), d98788) ∈ rowCases362 := by
  exact List.mem_cons_self
theorem oracleMember339 : ((.push 115 (.stay 116)), d98791) ∈ rowCases362 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases363 : List OracleBranch := [((.walk 113), d89600)]
theorem oracleMember340 : ((.walk 113), d89600) ∈ rowCases363 := by
  exact List.mem_cons_self
noncomputable def rowCases364 : List OracleBranch := [((.walk 93), d82334)]
theorem oracleMember341 : ((.walk 93), d82334) ∈ rowCases364 := by
  exact List.mem_cons_self
noncomputable def rowCases365 : List OracleBranch := [((.walk 91), d81525)]
theorem oracleMember342 : ((.walk 91), d81525) ∈ rowCases365 := by
  exact List.mem_cons_self
noncomputable def rowCases366 : List OracleBranch := []
noncomputable def rowCases367 : List OracleBranch := [((.walk 135), d98801)]
theorem oracleMember343 : ((.walk 135), d98801) ∈ rowCases367 := by
  exact List.mem_cons_self
noncomputable def rowCases368 : List OracleBranch := [((.walk 93), d82320), ((.push 93 (.stay 71)), d73777)]
theorem oracleMember344 : ((.walk 93), d82320) ∈ rowCases368 := by
  exact List.mem_cons_self
theorem oracleMember345 : ((.push 93 (.stay 71)), d73777) ∈ rowCases368 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases369 : List OracleBranch := []
noncomputable def rowCases370 : List OracleBranch := [((.walk 116), d82331)]
theorem oracleMember346 : ((.walk 116), d82331) ∈ rowCases370 := by
  exact List.mem_cons_self
noncomputable def rowCases371 : List OracleBranch := [((.walk 114), d98788), ((.push 114 (.stay 113)), d89603)]
theorem oracleMember347 : ((.walk 114), d98788) ∈ rowCases371 := by
  exact List.mem_cons_self
theorem oracleMember348 : ((.push 114 (.stay 113)), d89603) ∈ rowCases371 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases372 : List OracleBranch := [((.walk 94), d82355)]
theorem oracleMember349 : ((.walk 94), d82355) ∈ rowCases372 := by
  exact List.mem_cons_self
noncomputable def rowCases373 : List OracleBranch := []
noncomputable def rowCases374 : List OracleBranch := [((.walk 138), d100900)]
theorem oracleMember350 : ((.walk 138), d100900) ∈ rowCases374 := by
  exact List.mem_cons_self
noncomputable def rowCases375 : List OracleBranch := [((.walk 136), d100902)]
theorem oracleMember351 : ((.walk 136), d100902) ∈ rowCases375 := by
  exact List.mem_cons_self
noncomputable def rowCases376 : List OracleBranch := [((.walk 94), d82335)]
theorem oracleMember352 : ((.walk 94), d82335) ∈ rowCases376 := by
  exact List.mem_cons_self
noncomputable def rowCases377 : List OracleBranch := [((.walk 138), d100899), ((.push 138 (.stay 160)), d100907)]
theorem oracleMember353 : ((.walk 138), d100899) ∈ rowCases377 := by
  exact List.mem_cons_self
theorem oracleMember354 : ((.push 138 (.stay 160)), d100907) ∈ rowCases377 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases378 : List OracleBranch := []
noncomputable def rowCases379 : List OracleBranch := [((.walk 115), d82331), ((.push 115 (.stay 114)), d98791)]
theorem oracleMember355 : ((.walk 115), d82331) ∈ rowCases379 := by
  exact List.mem_cons_self
theorem oracleMember356 : ((.push 115 (.stay 114)), d98791) ∈ rowCases379 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases380 : List OracleBranch := [((.walk 95), d82362)]
theorem oracleMember357 : ((.walk 95), d82362) ∈ rowCases380 := by
  exact List.mem_cons_self
noncomputable def rowCases381 : List OracleBranch := [((.walk 93), d82333)]
theorem oracleMember358 : ((.walk 93), d82333) ∈ rowCases381 := by
  exact List.mem_cons_self
noncomputable def rowCases382 : List OracleBranch := []
noncomputable def rowCases383 : List OracleBranch := []
noncomputable def rowCases384 : List OracleBranch := [((.walk 96), d82363), ((.push 96 (.stay 74)), d74052)]
theorem oracleMember359 : ((.walk 96), d82363) ∈ rowCases384 := by
  exact List.mem_cons_self
theorem oracleMember360 : ((.push 96 (.stay 74)), d74052) ∈ rowCases384 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases385 : List OracleBranch := []
noncomputable def rowCases386 : List OracleBranch := [((.walk 119), d100937), ((.push 119 (.stay 120)), d100940)]
theorem oracleMember361 : ((.walk 119), d100937) ∈ rowCases386 := by
  exact List.mem_cons_self
theorem oracleMember362 : ((.push 119 (.stay 120)), d100940) ∈ rowCases386 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases387 : List OracleBranch := []
noncomputable def rowCases388 : List OracleBranch := [((.walk 97), d82414)]
theorem oracleMember363 : ((.walk 97), d82414) ∈ rowCases388 := by
  exact List.mem_cons_self
noncomputable def rowCases389 : List OracleBranch := [((.walk 95), d82360)]
theorem oracleMember364 : ((.walk 95), d82360) ∈ rowCases389 := by
  exact List.mem_cons_self
noncomputable def rowCases390 : List OracleBranch := [((.walk 141), d100942)]
theorem oracleMember365 : ((.walk 141), d100942) ∈ rowCases390 := by
  exact List.mem_cons_self
noncomputable def rowCases391 : List OracleBranch := []
noncomputable def rowCases392 : List OracleBranch := [((.walk 97), d82376)]
theorem oracleMember366 : ((.walk 97), d82376) ∈ rowCases392 := by
  exact List.mem_cons_self
noncomputable def rowCases393 : List OracleBranch := [((.walk 141), d100941), ((.push 141 (.stay 163)), d102055)]
theorem oracleMember367 : ((.walk 141), d100941) ∈ rowCases393 := by
  exact List.mem_cons_self
theorem oracleMember368 : ((.push 141 (.stay 163)), d102055) ∈ rowCases393 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases394 : List OracleBranch := [((.walk 120), d82407)]
theorem oracleMember369 : ((.walk 120), d82407) ∈ rowCases394 := by
  exact List.mem_cons_self
noncomputable def rowCases395 : List OracleBranch := [((.walk 118), d100937)]
theorem oracleMember370 : ((.walk 118), d100937) ∈ rowCases395 := by
  exact List.mem_cons_self
noncomputable def rowCases396 : List OracleBranch := [((.walk 98), d82422)]
theorem oracleMember371 : ((.walk 98), d82422) ∈ rowCases396 := by
  exact List.mem_cons_self
noncomputable def rowCases397 : List OracleBranch := [((.walk 96), d82375)]
theorem oracleMember372 : ((.walk 96), d82375) ∈ rowCases397 := by
  exact List.mem_cons_self
noncomputable def rowCases398 : List OracleBranch := []
noncomputable def rowCases399 : List OracleBranch := []
end NetHack.Soko22Hazard87
