import NetHack.Soko22Hazard87.OracleCases04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases500 : List OracleBranch := []
noncomputable def rowCases501 : List OracleBranch := [((.walk 115), d100900)]
theorem oracleMember490 : ((.walk 115), d100900) ∈ rowCases501 := by
  exact List.mem_cons_self
noncomputable def rowCases502 : List OracleBranch := [((.walk 161), d128580)]
theorem oracleMember491 : ((.walk 161), d128580) ∈ rowCases502 := by
  exact List.mem_cons_self
noncomputable def rowCases503 : List OracleBranch := [((.walk 159), d129472)]
theorem oracleMember492 : ((.walk 159), d129472) ∈ rowCases503 := by
  exact List.mem_cons_self
noncomputable def rowCases504 : List OracleBranch := [((.walk 119), d100941), ((.push 119 (.stay 97)), d82381)]
theorem oracleMember493 : ((.walk 119), d100941) ∈ rowCases504 := by
  exact List.mem_cons_self
theorem oracleMember494 : ((.push 119 (.stay 97)), d82381) ∈ rowCases504 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases505 : List OracleBranch := [((.walk 163), d129672), ((.push 163 (.stay 185)), d130390)]
theorem oracleMember495 : ((.walk 163), d129672) ∈ rowCases505 := by
  exact List.mem_cons_self
theorem oracleMember496 : ((.push 163 (.stay 185)), d130390) ∈ rowCases505 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases506 : List OracleBranch := []
noncomputable def rowCases507 : List OracleBranch := []
noncomputable def rowCases508 : List OracleBranch := [((.walk 120), d102105)]
theorem oracleMember497 : ((.walk 120), d102105) ∈ rowCases508 := by
  exact List.mem_cons_self
noncomputable def rowCases509 : List OracleBranch := [((.walk 118), d100942)]
theorem oracleMember498 : ((.walk 118), d100942) ∈ rowCases509 := by
  exact List.mem_cons_self
noncomputable def rowCases510 : List OracleBranch := [((.walk 164), d130482)]
theorem oracleMember499 : ((.walk 164), d130482) ∈ rowCases510 := by
  exact List.mem_cons_self
noncomputable def rowCases511 : List OracleBranch := [((.walk 162), d131099)]
theorem oracleMember500 : ((.walk 162), d131099) ∈ rowCases511 := by
  exact List.mem_cons_self
noncomputable def rowCases512 : List OracleBranch := [((.walk 122), d1), ((.push 122 (.stay 100)), d0)]
theorem oracleMember501 : ((.walk 122), d1) ∈ rowCases512 := by
  exact List.mem_cons_self
theorem oracleMember502 : ((.push 122 (.stay 100)), d0) ∈ rowCases512 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases513 : List OracleBranch := [((.walk 166), d1), ((.push 166 (.stay 188)), d0)]
theorem oracleMember503 : ((.walk 166), d1) ∈ rowCases513 := by
  exact List.mem_cons_self
theorem oracleMember504 : ((.push 166 (.stay 188)), d0) ∈ rowCases513 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases514 : List OracleBranch := [((.walk 145), d1), ((.push 145 (.stay 146)), d0)]
theorem oracleMember505 : ((.walk 145), d1) ∈ rowCases514 := by
  exact List.mem_cons_self
theorem oracleMember506 : ((.push 145 (.stay 146)), d0) ∈ rowCases514 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases515 : List OracleBranch := []
noncomputable def rowCases516 : List OracleBranch := [((.walk 123), d1)]
theorem oracleMember507 : ((.walk 123), d1) ∈ rowCases516 := by
  exact List.mem_cons_self
noncomputable def rowCases517 : List OracleBranch := []
noncomputable def rowCases518 : List OracleBranch := [((.walk 167), d1)]
theorem oracleMember508 : ((.walk 167), d1) ∈ rowCases518 := by
  exact List.mem_cons_self
noncomputable def rowCases519 : List OracleBranch := []
noncomputable def rowCases520 : List OracleBranch := [((.walk 123), d1), ((.push 123 (.stay 101)), d0)]
theorem oracleMember509 : ((.walk 123), d1) ∈ rowCases520 := by
  exact List.mem_cons_self
theorem oracleMember510 : ((.push 123 (.stay 101)), d0) ∈ rowCases520 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases521 : List OracleBranch := [((.walk 167), d1), ((.push 167 (.stay 189)), d0)]
theorem oracleMember511 : ((.walk 167), d1) ∈ rowCases521 := by
  exact List.mem_cons_self
theorem oracleMember512 : ((.push 167 (.stay 189)), d0) ∈ rowCases521 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases522 : List OracleBranch := [((.walk 146), d1), ((.push 146 (.stay 147)), d0)]
theorem oracleMember513 : ((.walk 146), d1) ∈ rowCases522 := by
  exact List.mem_cons_self
theorem oracleMember514 : ((.push 146 (.stay 147)), d0) ∈ rowCases522 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases523 : List OracleBranch := [((.walk 144), d1)]
theorem oracleMember515 : ((.walk 144), d1) ∈ rowCases523 := by
  exact List.mem_cons_self
noncomputable def rowCases524 : List OracleBranch := [((.walk 124), d1)]
theorem oracleMember516 : ((.walk 124), d1) ∈ rowCases524 := by
  exact List.mem_cons_self
noncomputable def rowCases525 : List OracleBranch := [((.walk 122), d1)]
theorem oracleMember517 : ((.walk 122), d1) ∈ rowCases525 := by
  exact List.mem_cons_self
noncomputable def rowCases526 : List OracleBranch := [((.walk 168), d1)]
theorem oracleMember518 : ((.walk 168), d1) ∈ rowCases526 := by
  exact List.mem_cons_self
noncomputable def rowCases527 : List OracleBranch := [((.walk 166), d1)]
theorem oracleMember519 : ((.walk 166), d1) ∈ rowCases527 := by
  exact List.mem_cons_self
noncomputable def rowCases528 : List OracleBranch := [((.walk 124), d1), ((.push 124 (.stay 102)), d0)]
theorem oracleMember520 : ((.walk 124), d1) ∈ rowCases528 := by
  exact List.mem_cons_self
theorem oracleMember521 : ((.push 124 (.stay 102)), d0) ∈ rowCases528 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases529 : List OracleBranch := [((.walk 168), d1), ((.push 168 (.stay 190)), d0)]
theorem oracleMember522 : ((.walk 168), d1) ∈ rowCases529 := by
  exact List.mem_cons_self
theorem oracleMember523 : ((.push 168 (.stay 190)), d0) ∈ rowCases529 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases530 : List OracleBranch := [((.walk 147), d1), ((.push 147 (.stay 148)), d0)]
theorem oracleMember524 : ((.walk 147), d1) ∈ rowCases530 := by
  exact List.mem_cons_self
theorem oracleMember525 : ((.push 147 (.stay 148)), d0) ∈ rowCases530 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases531 : List OracleBranch := [((.walk 145), d1), ((.push 145 (.stay 144)), d0)]
theorem oracleMember526 : ((.walk 145), d1) ∈ rowCases531 := by
  exact List.mem_cons_self
theorem oracleMember527 : ((.push 145 (.stay 144)), d0) ∈ rowCases531 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases532 : List OracleBranch := [((.walk 125), d1)]
theorem oracleMember528 : ((.walk 125), d1) ∈ rowCases532 := by
  exact List.mem_cons_self
noncomputable def rowCases533 : List OracleBranch := [((.walk 123), d1)]
theorem oracleMember529 : ((.walk 123), d1) ∈ rowCases533 := by
  exact List.mem_cons_self
noncomputable def rowCases534 : List OracleBranch := [((.walk 169), d1)]
theorem oracleMember530 : ((.walk 169), d1) ∈ rowCases534 := by
  exact List.mem_cons_self
noncomputable def rowCases535 : List OracleBranch := [((.walk 167), d1)]
theorem oracleMember531 : ((.walk 167), d1) ∈ rowCases535 := by
  exact List.mem_cons_self
noncomputable def rowCases536 : List OracleBranch := [((.walk 125), d1), ((.push 125 (.stay 103)), d0)]
theorem oracleMember532 : ((.walk 125), d1) ∈ rowCases536 := by
  exact List.mem_cons_self
theorem oracleMember533 : ((.push 125 (.stay 103)), d0) ∈ rowCases536 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases537 : List OracleBranch := [((.walk 169), d1), ((.push 169 (.stay 191)), d0)]
theorem oracleMember534 : ((.walk 169), d1) ∈ rowCases537 := by
  exact List.mem_cons_self
theorem oracleMember535 : ((.push 169 (.stay 191)), d0) ∈ rowCases537 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases538 : List OracleBranch := [((.walk 148), d1), ((.push 148 (.stay 149)), d0)]
theorem oracleMember536 : ((.walk 148), d1) ∈ rowCases538 := by
  exact List.mem_cons_self
theorem oracleMember537 : ((.push 148 (.stay 149)), d0) ∈ rowCases538 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases539 : List OracleBranch := [((.walk 146), d1), ((.push 146 (.stay 145)), d0)]
theorem oracleMember538 : ((.walk 146), d1) ∈ rowCases539 := by
  exact List.mem_cons_self
theorem oracleMember539 : ((.push 146 (.stay 145)), d0) ∈ rowCases539 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases540 : List OracleBranch := [((.walk 126), d1)]
theorem oracleMember540 : ((.walk 126), d1) ∈ rowCases540 := by
  exact List.mem_cons_self
noncomputable def rowCases541 : List OracleBranch := [((.walk 124), d1)]
theorem oracleMember541 : ((.walk 124), d1) ∈ rowCases541 := by
  exact List.mem_cons_self
noncomputable def rowCases542 : List OracleBranch := [((.walk 170), d1)]
theorem oracleMember542 : ((.walk 170), d1) ∈ rowCases542 := by
  exact List.mem_cons_self
noncomputable def rowCases543 : List OracleBranch := [((.walk 168), d1)]
theorem oracleMember543 : ((.walk 168), d1) ∈ rowCases543 := by
  exact List.mem_cons_self
noncomputable def rowCases544 : List OracleBranch := [((.walk 126), d1), ((.push 126 (.stay 104)), d0)]
theorem oracleMember544 : ((.walk 126), d1) ∈ rowCases544 := by
  exact List.mem_cons_self
theorem oracleMember545 : ((.push 126 (.stay 104)), d0) ∈ rowCases544 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases545 : List OracleBranch := [((.walk 170), d1), ((.push 170 (.stay 192)), d0)]
theorem oracleMember546 : ((.walk 170), d1) ∈ rowCases545 := by
  exact List.mem_cons_self
theorem oracleMember547 : ((.push 170 (.stay 192)), d0) ∈ rowCases545 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases546 : List OracleBranch := [((.walk 149), d1), ((.push 149 (.stay 150)), d0)]
theorem oracleMember548 : ((.walk 149), d1) ∈ rowCases546 := by
  exact List.mem_cons_self
theorem oracleMember549 : ((.push 149 (.stay 150)), d0) ∈ rowCases546 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases547 : List OracleBranch := [((.walk 147), d1), ((.push 147 (.stay 146)), d0)]
theorem oracleMember550 : ((.walk 147), d1) ∈ rowCases547 := by
  exact List.mem_cons_self
theorem oracleMember551 : ((.push 147 (.stay 146)), d0) ∈ rowCases547 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases548 : List OracleBranch := [((.walk 127), d1)]
theorem oracleMember552 : ((.walk 127), d1) ∈ rowCases548 := by
  exact List.mem_cons_self
noncomputable def rowCases549 : List OracleBranch := [((.walk 125), d1)]
theorem oracleMember553 : ((.walk 125), d1) ∈ rowCases549 := by
  exact List.mem_cons_self
noncomputable def rowCases550 : List OracleBranch := [((.walk 171), d1)]
theorem oracleMember554 : ((.walk 171), d1) ∈ rowCases550 := by
  exact List.mem_cons_self
noncomputable def rowCases551 : List OracleBranch := [((.walk 169), d1)]
theorem oracleMember555 : ((.walk 169), d1) ∈ rowCases551 := by
  exact List.mem_cons_self
noncomputable def rowCases552 : List OracleBranch := [((.walk 127), d1), ((.push 127 (.stay 105)), d0)]
theorem oracleMember556 : ((.walk 127), d1) ∈ rowCases552 := by
  exact List.mem_cons_self
theorem oracleMember557 : ((.push 127 (.stay 105)), d0) ∈ rowCases552 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases553 : List OracleBranch := [((.walk 171), d1), ((.push 171 (.stay 193)), d0)]
theorem oracleMember558 : ((.walk 171), d1) ∈ rowCases553 := by
  exact List.mem_cons_self
theorem oracleMember559 : ((.push 171 (.stay 193)), d0) ∈ rowCases553 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases554 : List OracleBranch := [((.walk 150), d1)]
theorem oracleMember560 : ((.walk 150), d1) ∈ rowCases554 := by
  exact List.mem_cons_self
noncomputable def rowCases555 : List OracleBranch := [((.walk 148), d1), ((.push 148 (.stay 147)), d0)]
theorem oracleMember561 : ((.walk 148), d1) ∈ rowCases555 := by
  exact List.mem_cons_self
theorem oracleMember562 : ((.push 148 (.stay 147)), d0) ∈ rowCases555 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases556 : List OracleBranch := [((.walk 128), d1)]
theorem oracleMember563 : ((.walk 128), d1) ∈ rowCases556 := by
  exact List.mem_cons_self
noncomputable def rowCases557 : List OracleBranch := [((.walk 126), d1)]
theorem oracleMember564 : ((.walk 126), d1) ∈ rowCases557 := by
  exact List.mem_cons_self
noncomputable def rowCases558 : List OracleBranch := [((.walk 172), d1)]
theorem oracleMember565 : ((.walk 172), d1) ∈ rowCases558 := by
  exact List.mem_cons_self
noncomputable def rowCases559 : List OracleBranch := [((.walk 170), d1)]
theorem oracleMember566 : ((.walk 170), d1) ∈ rowCases559 := by
  exact List.mem_cons_self
noncomputable def rowCases560 : List OracleBranch := [((.walk 128), d1), ((.push 128 (.stay 106)), d0)]
theorem oracleMember567 : ((.walk 128), d1) ∈ rowCases560 := by
  exact List.mem_cons_self
theorem oracleMember568 : ((.push 128 (.stay 106)), d0) ∈ rowCases560 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases561 : List OracleBranch := [((.walk 172), d1), ((.push 172 (.stay 194)), d0)]
theorem oracleMember569 : ((.walk 172), d1) ∈ rowCases561 := by
  exact List.mem_cons_self
theorem oracleMember570 : ((.push 172 (.stay 194)), d0) ∈ rowCases561 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases562 : List OracleBranch := []
noncomputable def rowCases563 : List OracleBranch := [((.walk 149), d1), ((.push 149 (.stay 148)), d0)]
theorem oracleMember571 : ((.walk 149), d1) ∈ rowCases563 := by
  exact List.mem_cons_self
theorem oracleMember572 : ((.push 149 (.stay 148)), d0) ∈ rowCases563 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases564 : List OracleBranch := []
noncomputable def rowCases565 : List OracleBranch := [((.walk 127), d1)]
theorem oracleMember573 : ((.walk 127), d1) ∈ rowCases565 := by
  exact List.mem_cons_self
noncomputable def rowCases566 : List OracleBranch := []
noncomputable def rowCases567 : List OracleBranch := [((.walk 171), d1)]
theorem oracleMember574 : ((.walk 171), d1) ∈ rowCases567 := by
  exact List.mem_cons_self
noncomputable def rowCases568 : List OracleBranch := [((.walk 133), d102593), ((.push 133 (.stay 111)), d82690)]
theorem oracleMember575 : ((.walk 133), d102593) ∈ rowCases568 := by
  exact List.mem_cons_self
theorem oracleMember576 : ((.push 133 (.stay 111)), d82690) ∈ rowCases568 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases569 : List OracleBranch := [((.walk 177), d132764), ((.push 177 (.stay 199)), d132769)]
theorem oracleMember577 : ((.walk 177), d132764) ∈ rowCases569 := by
  exact List.mem_cons_self
theorem oracleMember578 : ((.push 177 (.stay 199)), d132769) ∈ rowCases569 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases570 : List OracleBranch := [((.walk 156), d104538), ((.push 156 (.stay 157)), d132772)]
theorem oracleMember579 : ((.walk 156), d104538) ∈ rowCases570 := by
  exact List.mem_cons_self
theorem oracleMember580 : ((.push 156 (.stay 157)), d132772) ∈ rowCases570 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases571 : List OracleBranch := []
noncomputable def rowCases572 : List OracleBranch := [((.walk 134), d109328)]
theorem oracleMember581 : ((.walk 134), d109328) ∈ rowCases572 := by
  exact List.mem_cons_self
noncomputable def rowCases573 : List OracleBranch := []
noncomputable def rowCases574 : List OracleBranch := []
noncomputable def rowCases575 : List OracleBranch := []
noncomputable def rowCases576 : List OracleBranch := [((.walk 134), d104541)]
theorem oracleMember582 : ((.walk 134), d104541) ∈ rowCases576 := by
  exact List.mem_cons_self
noncomputable def rowCases577 : List OracleBranch := []
noncomputable def rowCases578 : List OracleBranch := [((.walk 157), d135429), ((.push 157 (.stay 158)), d135432)]
theorem oracleMember583 : ((.walk 157), d135429) ∈ rowCases578 := by
  exact List.mem_cons_self
theorem oracleMember584 : ((.push 157 (.stay 158)), d135432) ∈ rowCases578 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases579 : List OracleBranch := [((.walk 155), d104538)]
theorem oracleMember585 : ((.walk 155), d104538) ∈ rowCases579 := by
  exact List.mem_cons_self
noncomputable def rowCases580 : List OracleBranch := [((.walk 135), d115573)]
theorem oracleMember586 : ((.walk 135), d115573) ∈ rowCases580 := by
  exact List.mem_cons_self
noncomputable def rowCases581 : List OracleBranch := [((.walk 133), d104540)]
theorem oracleMember587 : ((.walk 133), d104540) ∈ rowCases581 := by
  exact List.mem_cons_self
noncomputable def rowCases582 : List OracleBranch := []
noncomputable def rowCases583 : List OracleBranch := [((.walk 177), d139752)]
theorem oracleMember588 : ((.walk 177), d139752) ∈ rowCases583 := by
  exact List.mem_cons_self
noncomputable def rowCases584 : List OracleBranch := [((.walk 135), d107483), ((.push 135 (.stay 113)), d85724)]
theorem oracleMember589 : ((.walk 135), d107483) ∈ rowCases584 := by
  exact List.mem_cons_self
theorem oracleMember590 : ((.push 135 (.stay 113)), d85724) ∈ rowCases584 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases585 : List OracleBranch := []
noncomputable def rowCases586 : List OracleBranch := [((.walk 158), d112686), ((.push 158 (.stay 159)), d142666)]
theorem oracleMember591 : ((.walk 158), d112686) ∈ rowCases586 := by
  exact List.mem_cons_self
theorem oracleMember592 : ((.push 158 (.stay 159)), d142666) ∈ rowCases586 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases587 : List OracleBranch := [((.walk 156), d135429), ((.push 156 (.stay 155)), d132772)]
theorem oracleMember593 : ((.walk 156), d135429) ∈ rowCases587 := by
  exact List.mem_cons_self
theorem oracleMember594 : ((.push 156 (.stay 155)), d132772) ∈ rowCases587 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases588 : List OracleBranch := [((.walk 136), d125748)]
theorem oracleMember595 : ((.walk 136), d125748) ∈ rowCases588 := by
  exact List.mem_cons_self
noncomputable def rowCases589 : List OracleBranch := [((.walk 134), d107485)]
theorem oracleMember596 : ((.walk 134), d107485) ∈ rowCases589 := by
  exact List.mem_cons_self
noncomputable def rowCases590 : List OracleBranch := [((.walk 180), d146837)]
theorem oracleMember597 : ((.walk 180), d146837) ∈ rowCases590 := by
  exact List.mem_cons_self
noncomputable def rowCases591 : List OracleBranch := []
noncomputable def rowCases592 : List OracleBranch := [((.walk 136), d115574), ((.push 136 (.stay 114)), d94756)]
theorem oracleMember598 : ((.walk 136), d115574) ∈ rowCases592 := by
  exact List.mem_cons_self
theorem oracleMember599 : ((.push 136 (.stay 114)), d94756) ∈ rowCases592 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases593 : List OracleBranch := [((.walk 180), d146836), ((.push 180 (.stay 202)), d152855)]
theorem oracleMember600 : ((.walk 180), d146836) ∈ rowCases593 := by
  exact List.mem_cons_self
theorem oracleMember601 : ((.push 180 (.stay 202)), d152855) ∈ rowCases593 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases594 : List OracleBranch := [((.walk 159), d122305), ((.push 159 (.stay 160)), d159762)]
theorem oracleMember602 : ((.walk 159), d122305) ∈ rowCases594 := by
  exact List.mem_cons_self
theorem oracleMember603 : ((.push 159 (.stay 160)), d159762) ∈ rowCases594 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases595 : List OracleBranch := [((.walk 157), d112686), ((.push 157 (.stay 156)), d135432)]
theorem oracleMember604 : ((.walk 157), d112686) ∈ rowCases595 := by
  exact List.mem_cons_self
theorem oracleMember605 : ((.push 157 (.stay 156)), d135432) ∈ rowCases595 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases596 : List OracleBranch := []
noncomputable def rowCases597 : List OracleBranch := [((.walk 135), d112688)]
theorem oracleMember606 : ((.walk 135), d112688) ∈ rowCases597 := by
  exact List.mem_cons_self
noncomputable def rowCases598 : List OracleBranch := [((.walk 181), d162095)]
theorem oracleMember607 : ((.walk 181), d162095) ∈ rowCases598 := by
  exact List.mem_cons_self
noncomputable def rowCases599 : List OracleBranch := []
end NetHack.Soko22Hazard87
