import NetHack.Soko22Hazard87.OracleCases03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases400 : List OracleBranch := [((.walk 98), d82415), ((.push 98 (.stay 76)), d74072)]
theorem oracleMember373 : ((.walk 98), d82415) ∈ rowCases400 := by
  exact List.mem_cons_self
theorem oracleMember374 : ((.push 98 (.stay 76)), d74072) ∈ rowCases400 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases401 : List OracleBranch := []
noncomputable def rowCases402 : List OracleBranch := []
noncomputable def rowCases403 : List OracleBranch := [((.walk 119), d82407), ((.push 119 (.stay 118)), d100940)]
theorem oracleMember375 : ((.walk 119), d82407) ∈ rowCases403 := by
  exact List.mem_cons_self
theorem oracleMember376 : ((.push 119 (.stay 118)), d100940) ∈ rowCases403 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases404 : List OracleBranch := []
noncomputable def rowCases405 : List OracleBranch := [((.walk 97), d82409)]
theorem oracleMember377 : ((.walk 97), d82409) ∈ rowCases405 := by
  exact List.mem_cons_self
noncomputable def rowCases406 : List OracleBranch := []
noncomputable def rowCases407 : List OracleBranch := [((.walk 141), d102105)]
theorem oracleMember378 : ((.walk 141), d102105) ∈ rowCases407 := by
  exact List.mem_cons_self
noncomputable def rowCases408 : List OracleBranch := [((.walk 100), d1), ((.push 100 (.stay 78)), d0)]
theorem oracleMember379 : ((.walk 100), d1) ∈ rowCases408 := by
  exact List.mem_cons_self
theorem oracleMember380 : ((.push 100 (.stay 78)), d0) ∈ rowCases408 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases409 : List OracleBranch := [((.walk 144), d1), ((.push 144 (.stay 166)), d0)]
theorem oracleMember381 : ((.walk 144), d1) ∈ rowCases409 := by
  exact List.mem_cons_self
theorem oracleMember382 : ((.push 144 (.stay 166)), d0) ∈ rowCases409 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases410 : List OracleBranch := [((.walk 123), d1), ((.push 123 (.stay 124)), d0)]
theorem oracleMember383 : ((.walk 123), d1) ∈ rowCases410 := by
  exact List.mem_cons_self
theorem oracleMember384 : ((.push 123 (.stay 124)), d0) ∈ rowCases410 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases411 : List OracleBranch := []
noncomputable def rowCases412 : List OracleBranch := [((.walk 101), d1)]
theorem oracleMember385 : ((.walk 101), d1) ∈ rowCases412 := by
  exact List.mem_cons_self
noncomputable def rowCases413 : List OracleBranch := []
noncomputable def rowCases414 : List OracleBranch := [((.walk 145), d1)]
theorem oracleMember386 : ((.walk 145), d1) ∈ rowCases414 := by
  exact List.mem_cons_self
noncomputable def rowCases415 : List OracleBranch := []
noncomputable def rowCases416 : List OracleBranch := [((.walk 101), d1), ((.push 101 (.stay 79)), d0)]
theorem oracleMember387 : ((.walk 101), d1) ∈ rowCases416 := by
  exact List.mem_cons_self
theorem oracleMember388 : ((.push 101 (.stay 79)), d0) ∈ rowCases416 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases417 : List OracleBranch := [((.walk 145), d1), ((.push 145 (.stay 167)), d0)]
theorem oracleMember389 : ((.walk 145), d1) ∈ rowCases417 := by
  exact List.mem_cons_self
theorem oracleMember390 : ((.push 145 (.stay 167)), d0) ∈ rowCases417 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases418 : List OracleBranch := [((.walk 124), d1), ((.push 124 (.stay 125)), d0)]
theorem oracleMember391 : ((.walk 124), d1) ∈ rowCases418 := by
  exact List.mem_cons_self
theorem oracleMember392 : ((.push 124 (.stay 125)), d0) ∈ rowCases418 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases419 : List OracleBranch := [((.walk 122), d1)]
theorem oracleMember393 : ((.walk 122), d1) ∈ rowCases419 := by
  exact List.mem_cons_self
noncomputable def rowCases420 : List OracleBranch := [((.walk 102), d1)]
theorem oracleMember394 : ((.walk 102), d1) ∈ rowCases420 := by
  exact List.mem_cons_self
noncomputable def rowCases421 : List OracleBranch := [((.walk 100), d1)]
theorem oracleMember395 : ((.walk 100), d1) ∈ rowCases421 := by
  exact List.mem_cons_self
noncomputable def rowCases422 : List OracleBranch := [((.walk 146), d1)]
theorem oracleMember396 : ((.walk 146), d1) ∈ rowCases422 := by
  exact List.mem_cons_self
noncomputable def rowCases423 : List OracleBranch := [((.walk 144), d1)]
theorem oracleMember397 : ((.walk 144), d1) ∈ rowCases423 := by
  exact List.mem_cons_self
noncomputable def rowCases424 : List OracleBranch := [((.walk 102), d1), ((.push 102 (.stay 80)), d0)]
theorem oracleMember398 : ((.walk 102), d1) ∈ rowCases424 := by
  exact List.mem_cons_self
theorem oracleMember399 : ((.push 102 (.stay 80)), d0) ∈ rowCases424 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases425 : List OracleBranch := [((.walk 146), d1), ((.push 146 (.stay 168)), d0)]
theorem oracleMember400 : ((.walk 146), d1) ∈ rowCases425 := by
  exact List.mem_cons_self
theorem oracleMember401 : ((.push 146 (.stay 168)), d0) ∈ rowCases425 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases426 : List OracleBranch := [((.walk 125), d1), ((.push 125 (.stay 126)), d0)]
theorem oracleMember402 : ((.walk 125), d1) ∈ rowCases426 := by
  exact List.mem_cons_self
theorem oracleMember403 : ((.push 125 (.stay 126)), d0) ∈ rowCases426 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases427 : List OracleBranch := [((.walk 123), d1), ((.push 123 (.stay 122)), d0)]
theorem oracleMember404 : ((.walk 123), d1) ∈ rowCases427 := by
  exact List.mem_cons_self
theorem oracleMember405 : ((.push 123 (.stay 122)), d0) ∈ rowCases427 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases428 : List OracleBranch := [((.walk 103), d1)]
theorem oracleMember406 : ((.walk 103), d1) ∈ rowCases428 := by
  exact List.mem_cons_self
noncomputable def rowCases429 : List OracleBranch := [((.walk 101), d1)]
theorem oracleMember407 : ((.walk 101), d1) ∈ rowCases429 := by
  exact List.mem_cons_self
noncomputable def rowCases430 : List OracleBranch := [((.walk 147), d1)]
theorem oracleMember408 : ((.walk 147), d1) ∈ rowCases430 := by
  exact List.mem_cons_self
noncomputable def rowCases431 : List OracleBranch := [((.walk 145), d1)]
theorem oracleMember409 : ((.walk 145), d1) ∈ rowCases431 := by
  exact List.mem_cons_self
noncomputable def rowCases432 : List OracleBranch := [((.walk 103), d1), ((.push 103 (.stay 81)), d0)]
theorem oracleMember410 : ((.walk 103), d1) ∈ rowCases432 := by
  exact List.mem_cons_self
theorem oracleMember411 : ((.push 103 (.stay 81)), d0) ∈ rowCases432 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases433 : List OracleBranch := [((.walk 147), d1), ((.push 147 (.stay 169)), d0)]
theorem oracleMember412 : ((.walk 147), d1) ∈ rowCases433 := by
  exact List.mem_cons_self
theorem oracleMember413 : ((.push 147 (.stay 169)), d0) ∈ rowCases433 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases434 : List OracleBranch := [((.walk 126), d1), ((.push 126 (.stay 127)), d0)]
theorem oracleMember414 : ((.walk 126), d1) ∈ rowCases434 := by
  exact List.mem_cons_self
theorem oracleMember415 : ((.push 126 (.stay 127)), d0) ∈ rowCases434 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases435 : List OracleBranch := [((.walk 124), d1), ((.push 124 (.stay 123)), d0)]
theorem oracleMember416 : ((.walk 124), d1) ∈ rowCases435 := by
  exact List.mem_cons_self
theorem oracleMember417 : ((.push 124 (.stay 123)), d0) ∈ rowCases435 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases436 : List OracleBranch := [((.walk 104), d1)]
theorem oracleMember418 : ((.walk 104), d1) ∈ rowCases436 := by
  exact List.mem_cons_self
noncomputable def rowCases437 : List OracleBranch := [((.walk 102), d1)]
theorem oracleMember419 : ((.walk 102), d1) ∈ rowCases437 := by
  exact List.mem_cons_self
noncomputable def rowCases438 : List OracleBranch := [((.walk 148), d1)]
theorem oracleMember420 : ((.walk 148), d1) ∈ rowCases438 := by
  exact List.mem_cons_self
noncomputable def rowCases439 : List OracleBranch := [((.walk 146), d1)]
theorem oracleMember421 : ((.walk 146), d1) ∈ rowCases439 := by
  exact List.mem_cons_self
noncomputable def rowCases440 : List OracleBranch := [((.walk 104), d1), ((.push 104 (.stay 82)), d0)]
theorem oracleMember422 : ((.walk 104), d1) ∈ rowCases440 := by
  exact List.mem_cons_self
theorem oracleMember423 : ((.push 104 (.stay 82)), d0) ∈ rowCases440 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases441 : List OracleBranch := [((.walk 148), d1), ((.push 148 (.stay 170)), d0)]
theorem oracleMember424 : ((.walk 148), d1) ∈ rowCases441 := by
  exact List.mem_cons_self
theorem oracleMember425 : ((.push 148 (.stay 170)), d0) ∈ rowCases441 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases442 : List OracleBranch := [((.walk 127), d1), ((.push 127 (.stay 128)), d0)]
theorem oracleMember426 : ((.walk 127), d1) ∈ rowCases442 := by
  exact List.mem_cons_self
theorem oracleMember427 : ((.push 127 (.stay 128)), d0) ∈ rowCases442 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases443 : List OracleBranch := [((.walk 125), d1), ((.push 125 (.stay 124)), d0)]
theorem oracleMember428 : ((.walk 125), d1) ∈ rowCases443 := by
  exact List.mem_cons_self
theorem oracleMember429 : ((.push 125 (.stay 124)), d0) ∈ rowCases443 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases444 : List OracleBranch := [((.walk 105), d1)]
theorem oracleMember430 : ((.walk 105), d1) ∈ rowCases444 := by
  exact List.mem_cons_self
noncomputable def rowCases445 : List OracleBranch := [((.walk 103), d1)]
theorem oracleMember431 : ((.walk 103), d1) ∈ rowCases445 := by
  exact List.mem_cons_self
noncomputable def rowCases446 : List OracleBranch := [((.walk 149), d1)]
theorem oracleMember432 : ((.walk 149), d1) ∈ rowCases446 := by
  exact List.mem_cons_self
noncomputable def rowCases447 : List OracleBranch := [((.walk 147), d1)]
theorem oracleMember433 : ((.walk 147), d1) ∈ rowCases447 := by
  exact List.mem_cons_self
noncomputable def rowCases448 : List OracleBranch := [((.walk 105), d1), ((.push 105 (.stay 83)), d0)]
theorem oracleMember434 : ((.walk 105), d1) ∈ rowCases448 := by
  exact List.mem_cons_self
theorem oracleMember435 : ((.push 105 (.stay 83)), d0) ∈ rowCases448 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases449 : List OracleBranch := [((.walk 149), d1), ((.push 149 (.stay 171)), d0)]
theorem oracleMember436 : ((.walk 149), d1) ∈ rowCases449 := by
  exact List.mem_cons_self
theorem oracleMember437 : ((.push 149 (.stay 171)), d0) ∈ rowCases449 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases450 : List OracleBranch := [((.walk 128), d1)]
theorem oracleMember438 : ((.walk 128), d1) ∈ rowCases450 := by
  exact List.mem_cons_self
noncomputable def rowCases451 : List OracleBranch := [((.walk 126), d1), ((.push 126 (.stay 125)), d0)]
theorem oracleMember439 : ((.walk 126), d1) ∈ rowCases451 := by
  exact List.mem_cons_self
theorem oracleMember440 : ((.push 126 (.stay 125)), d0) ∈ rowCases451 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases452 : List OracleBranch := [((.walk 106), d1)]
theorem oracleMember441 : ((.walk 106), d1) ∈ rowCases452 := by
  exact List.mem_cons_self
noncomputable def rowCases453 : List OracleBranch := [((.walk 104), d1)]
theorem oracleMember442 : ((.walk 104), d1) ∈ rowCases453 := by
  exact List.mem_cons_self
noncomputable def rowCases454 : List OracleBranch := [((.walk 150), d1)]
theorem oracleMember443 : ((.walk 150), d1) ∈ rowCases454 := by
  exact List.mem_cons_self
noncomputable def rowCases455 : List OracleBranch := [((.walk 148), d1)]
theorem oracleMember444 : ((.walk 148), d1) ∈ rowCases455 := by
  exact List.mem_cons_self
noncomputable def rowCases456 : List OracleBranch := [((.walk 106), d1), ((.push 106 (.stay 84)), d0)]
theorem oracleMember445 : ((.walk 106), d1) ∈ rowCases456 := by
  exact List.mem_cons_self
theorem oracleMember446 : ((.push 106 (.stay 84)), d0) ∈ rowCases456 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases457 : List OracleBranch := [((.walk 150), d1), ((.push 150 (.stay 172)), d0)]
theorem oracleMember447 : ((.walk 150), d1) ∈ rowCases457 := by
  exact List.mem_cons_self
theorem oracleMember448 : ((.push 150 (.stay 172)), d0) ∈ rowCases457 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases458 : List OracleBranch := []
noncomputable def rowCases459 : List OracleBranch := [((.walk 127), d1), ((.push 127 (.stay 126)), d0)]
theorem oracleMember449 : ((.walk 127), d1) ∈ rowCases459 := by
  exact List.mem_cons_self
theorem oracleMember450 : ((.push 127 (.stay 126)), d0) ∈ rowCases459 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases460 : List OracleBranch := []
noncomputable def rowCases461 : List OracleBranch := [((.walk 105), d1)]
theorem oracleMember451 : ((.walk 105), d1) ∈ rowCases461 := by
  exact List.mem_cons_self
noncomputable def rowCases462 : List OracleBranch := []
noncomputable def rowCases463 : List OracleBranch := [((.walk 149), d1)]
theorem oracleMember452 : ((.walk 149), d1) ∈ rowCases463 := by
  exact List.mem_cons_self
noncomputable def rowCases464 : List OracleBranch := [((.walk 111), d82685), ((.push 111 (.stay 89)), d74854)]
theorem oracleMember453 : ((.walk 111), d82685) ∈ rowCases464 := by
  exact List.mem_cons_self
theorem oracleMember454 : ((.push 111 (.stay 89)), d74854) ∈ rowCases464 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases465 : List OracleBranch := [((.walk 155), d102593), ((.push 155 (.stay 177)), d102598)]
theorem oracleMember455 : ((.walk 155), d102593) ∈ rowCases465 := by
  exact List.mem_cons_self
theorem oracleMember456 : ((.push 155 (.stay 177)), d102598) ∈ rowCases465 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases466 : List OracleBranch := [((.walk 134), d82693), ((.push 134 (.stay 135)), d102601)]
theorem oracleMember457 : ((.walk 134), d82693) ∈ rowCases466 := by
  exact List.mem_cons_self
theorem oracleMember458 : ((.push 134 (.stay 135)), d102601) ∈ rowCases466 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases467 : List OracleBranch := []
noncomputable def rowCases468 : List OracleBranch := []
noncomputable def rowCases469 : List OracleBranch := []
noncomputable def rowCases470 : List OracleBranch := [((.walk 156), d104540)]
theorem oracleMember459 : ((.walk 156), d104540) ∈ rowCases470 := by
  exact List.mem_cons_self
noncomputable def rowCases471 : List OracleBranch := []
noncomputable def rowCases472 : List OracleBranch := []
noncomputable def rowCases473 : List OracleBranch := [((.walk 156), d104541)]
theorem oracleMember460 : ((.walk 156), d104541) ∈ rowCases473 := by
  exact List.mem_cons_self
noncomputable def rowCases474 : List OracleBranch := [((.walk 135), d104542), ((.push 135 (.stay 136)), d104545)]
theorem oracleMember461 : ((.walk 135), d104542) ∈ rowCases474 := by
  exact List.mem_cons_self
theorem oracleMember462 : ((.push 135 (.stay 136)), d104545) ∈ rowCases474 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases475 : List OracleBranch := [((.walk 133), d82693)]
theorem oracleMember463 : ((.walk 133), d82693) ∈ rowCases475 := by
  exact List.mem_cons_self
noncomputable def rowCases476 : List OracleBranch := [((.walk 113), d94517)]
theorem oracleMember464 : ((.walk 113), d94517) ∈ rowCases476 := by
  exact List.mem_cons_self
noncomputable def rowCases477 : List OracleBranch := [((.walk 111), d82694)]
theorem oracleMember465 : ((.walk 111), d82694) ∈ rowCases477 := by
  exact List.mem_cons_self
noncomputable def rowCases478 : List OracleBranch := [((.walk 157), d107485)]
theorem oracleMember466 : ((.walk 157), d107485) ∈ rowCases478 := by
  exact List.mem_cons_self
noncomputable def rowCases479 : List OracleBranch := [((.walk 155), d109328)]
theorem oracleMember467 : ((.walk 155), d109328) ∈ rowCases479 := by
  exact List.mem_cons_self
noncomputable def rowCases480 : List OracleBranch := [((.walk 113), d83662), ((.push 113 (.stay 91)), d77845)]
theorem oracleMember468 : ((.walk 113), d83662) ∈ rowCases480 := by
  exact List.mem_cons_self
theorem oracleMember469 : ((.push 113 (.stay 91)), d77845) ∈ rowCases480 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases481 : List OracleBranch := [((.walk 157), d107483)]
theorem oracleMember470 : ((.walk 157), d107483) ∈ rowCases481 := by
  exact List.mem_cons_self
noncomputable def rowCases482 : List OracleBranch := [((.walk 136), d92315)]
theorem oracleMember471 : ((.walk 136), d92315) ∈ rowCases482 := by
  exact List.mem_cons_self
noncomputable def rowCases483 : List OracleBranch := [((.walk 134), d104542), ((.push 134 (.stay 133)), d102601)]
theorem oracleMember472 : ((.walk 134), d104542) ∈ rowCases483 := by
  exact List.mem_cons_self
theorem oracleMember473 : ((.push 134 (.stay 133)), d102601) ∈ rowCases483 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases484 : List OracleBranch := [((.walk 114), d98801)]
theorem oracleMember474 : ((.walk 114), d98801) ∈ rowCases484 := by
  exact List.mem_cons_self
noncomputable def rowCases485 : List OracleBranch := []
noncomputable def rowCases486 : List OracleBranch := [((.walk 158), d112688)]
theorem oracleMember475 : ((.walk 158), d112688) ∈ rowCases486 := by
  exact List.mem_cons_self
noncomputable def rowCases487 : List OracleBranch := [((.walk 156), d115573)]
theorem oracleMember476 : ((.walk 156), d115573) ∈ rowCases487 := by
  exact List.mem_cons_self
noncomputable def rowCases488 : List OracleBranch := [((.walk 114), d94518)]
theorem oracleMember477 : ((.walk 114), d94518) ∈ rowCases488 := by
  exact List.mem_cons_self
noncomputable def rowCases489 : List OracleBranch := [((.walk 158), d115574), ((.push 158 (.stay 180)), d116753)]
theorem oracleMember478 : ((.walk 158), d115574) ∈ rowCases489 := by
  exact List.mem_cons_self
theorem oracleMember479 : ((.push 158 (.stay 180)), d116753) ∈ rowCases489 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases490 : List OracleBranch := []
noncomputable def rowCases491 : List OracleBranch := [((.walk 135), d92315), ((.push 135 (.stay 134)), d104545)]
theorem oracleMember480 : ((.walk 135), d92315) ∈ rowCases491 := by
  exact List.mem_cons_self
theorem oracleMember481 : ((.push 135 (.stay 134)), d104545) ∈ rowCases491 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases492 : List OracleBranch := [((.walk 115), d100902)]
theorem oracleMember482 : ((.walk 115), d100902) ∈ rowCases492 := by
  exact List.mem_cons_self
noncomputable def rowCases493 : List OracleBranch := [((.walk 113), d92317)]
theorem oracleMember483 : ((.walk 113), d92317) ∈ rowCases493 := by
  exact List.mem_cons_self
noncomputable def rowCases494 : List OracleBranch := [((.walk 159), d122306)]
theorem oracleMember484 : ((.walk 159), d122306) ∈ rowCases494 := by
  exact List.mem_cons_self
noncomputable def rowCases495 : List OracleBranch := [((.walk 157), d125748)]
theorem oracleMember485 : ((.walk 157), d125748) ∈ rowCases495 := by
  exact List.mem_cons_self
noncomputable def rowCases496 : List OracleBranch := [((.walk 116), d100899), ((.push 116 (.stay 94)), d82340)]
theorem oracleMember486 : ((.walk 116), d100899) ∈ rowCases496 := by
  exact List.mem_cons_self
theorem oracleMember487 : ((.push 116 (.stay 94)), d82340) ∈ rowCases496 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases497 : List OracleBranch := [((.walk 160), d126873), ((.push 160 (.stay 182)), d128487)]
theorem oracleMember488 : ((.walk 160), d126873) ∈ rowCases497 := by
  exact List.mem_cons_self
theorem oracleMember489 : ((.push 160 (.stay 182)), d128487) ∈ rowCases497 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases498 : List OracleBranch := []
noncomputable def rowCases499 : List OracleBranch := []
end NetHack.Soko22Hazard87
