import NetHack.Soko22Hazard87.GammaAfter004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter500 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) = d19737 p := by
  change bonus 162 _ = _
  rw [at162]
  rfl
theorem gammaAfter501 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  rfl
theorem gammaAfter502 (p : Pattern) : bonus (HazardPattern.nextHero (.push 122 (.stay 100))) (HazardPattern.afterPattern 10000 p (.push 122 (.stay 100))) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  change d0 (u104 p) = d0 p
  exact allUpdate56 p
theorem gammaAfter503 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  rfl
theorem gammaAfter504 (p : Pattern) : bonus (HazardPattern.nextHero (.push 166 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 188))) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  change d0 (u191 p) = d0 p
  exact allUpdate107 p
theorem gammaAfter505 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter506 (p : Pattern) : bonus (HazardPattern.nextHero (.push 145 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 146))) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  change d0 (u146 p) = d0 p
  exact allUpdate86 p
theorem gammaAfter507 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter508 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter509 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter510 (p : Pattern) : bonus (HazardPattern.nextHero (.push 123 (.stay 101))) (HazardPattern.afterPattern 10000 p (.push 123 (.stay 101))) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  change d0 (u106 p) = d0 p
  exact allUpdate58 p
theorem gammaAfter511 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter512 (p : Pattern) : bonus (HazardPattern.nextHero (.push 167 (.stay 189))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 189))) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  change d0 (u195 p) = d0 p
  exact allUpdate111 p
theorem gammaAfter513 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter514 (p : Pattern) : bonus (HazardPattern.nextHero (.push 146 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 147))) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  change d0 (u150 p) = d0 p
  exact allUpdate90 p
theorem gammaAfter515 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  rfl
theorem gammaAfter516 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter517 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 122)) (HazardPattern.afterPattern 10000 p (.walk 122)) = d0 p := by
  change bonus 122 _ = _
  rw [at122]
  rfl
theorem gammaAfter518 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter519 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  rfl
theorem gammaAfter520 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter521 (p : Pattern) : bonus (HazardPattern.nextHero (.push 124 (.stay 102))) (HazardPattern.afterPattern 10000 p (.push 124 (.stay 102))) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  change d0 (u110 p) = d0 p
  exact allUpdate62 p
theorem gammaAfter522 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter523 (p : Pattern) : bonus (HazardPattern.nextHero (.push 168 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 190))) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  change d0 (u199 p) = d0 p
  exact allUpdate115 p
theorem gammaAfter524 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter525 (p : Pattern) : bonus (HazardPattern.nextHero (.push 147 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 148))) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  change d0 (u154 p) = d0 p
  exact allUpdate94 p
theorem gammaAfter526 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter527 (p : Pattern) : bonus (HazardPattern.nextHero (.push 145 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 144))) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  change d0 (u145 p) = d0 p
  exact allUpdate85 p
theorem gammaAfter528 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter529 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 123)) (HazardPattern.afterPattern 10000 p (.walk 123)) = d0 p := by
  change bonus 123 _ = _
  rw [at123]
  rfl
theorem gammaAfter530 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter531 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter532 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter533 (p : Pattern) : bonus (HazardPattern.nextHero (.push 125 (.stay 103))) (HazardPattern.afterPattern 10000 p (.push 125 (.stay 103))) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  change d0 (u114 p) = d0 p
  exact allUpdate66 p
theorem gammaAfter534 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter535 (p : Pattern) : bonus (HazardPattern.nextHero (.push 169 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 191))) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  change d0 (u203 p) = d0 p
  exact allUpdate119 p
theorem gammaAfter536 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter537 (p : Pattern) : bonus (HazardPattern.nextHero (.push 148 (.stay 149))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 149))) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  change d0 (u158 p) = d0 p
  exact allUpdate98 p
theorem gammaAfter538 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter539 (p : Pattern) : bonus (HazardPattern.nextHero (.push 146 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 145))) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  change d0 (u149 p) = d0 p
  exact allUpdate89 p
theorem gammaAfter540 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter541 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 124)) (HazardPattern.afterPattern 10000 p (.walk 124)) = d0 p := by
  change bonus 124 _ = _
  rw [at124]
  rfl
theorem gammaAfter542 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  rfl
theorem gammaAfter543 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter544 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter545 (p : Pattern) : bonus (HazardPattern.nextHero (.push 126 (.stay 104))) (HazardPattern.afterPattern 10000 p (.push 126 (.stay 104))) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  change d0 (u118 p) = d0 p
  exact allUpdate70 p
theorem gammaAfter546 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  rfl
theorem gammaAfter547 (p : Pattern) : bonus (HazardPattern.nextHero (.push 170 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 192))) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  change d0 (u207 p) = d0 p
  exact allUpdate123 p
theorem gammaAfter548 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter549 (p : Pattern) : bonus (HazardPattern.nextHero (.push 149 (.stay 150))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 150))) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  change d0 (u162 p) = d0 p
  exact allUpdate102 p
theorem gammaAfter550 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter551 (p : Pattern) : bonus (HazardPattern.nextHero (.push 147 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 146))) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  change d0 (u153 p) = d0 p
  exact allUpdate93 p
theorem gammaAfter552 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter553 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 125)) (HazardPattern.afterPattern 10000 p (.walk 125)) = d0 p := by
  change bonus 125 _ = _
  rw [at125]
  rfl
theorem gammaAfter554 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  rfl
theorem gammaAfter555 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter556 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter557 (p : Pattern) : bonus (HazardPattern.nextHero (.push 127 (.stay 105))) (HazardPattern.afterPattern 10000 p (.push 127 (.stay 105))) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  change d0 (u122 p) = d0 p
  exact allUpdate74 p
theorem gammaAfter558 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  rfl
theorem gammaAfter559 (p : Pattern) : bonus (HazardPattern.nextHero (.push 171 (.stay 193))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 193))) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  change d0 (u211 p) = d0 p
  exact allUpdate127 p
theorem gammaAfter560 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  rfl
theorem gammaAfter561 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter562 (p : Pattern) : bonus (HazardPattern.nextHero (.push 148 (.stay 147))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 147))) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  change d0 (u157 p) = d0 p
  exact allUpdate97 p
theorem gammaAfter563 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  rfl
theorem gammaAfter564 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 126)) (HazardPattern.afterPattern 10000 p (.walk 126)) = d0 p := by
  change bonus 126 _ = _
  rw [at126]
  rfl
theorem gammaAfter565 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) = d0 p := by
  change bonus 172 _ = _
  rw [at172]
  rfl
theorem gammaAfter566 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  rfl
theorem gammaAfter567 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 128)) (HazardPattern.afterPattern 10000 p (.walk 128)) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  rfl
theorem gammaAfter568 (p : Pattern) : bonus (HazardPattern.nextHero (.push 128 (.stay 106))) (HazardPattern.afterPattern 10000 p (.push 128 (.stay 106))) = d0 p := by
  change bonus 128 _ = _
  rw [at128]
  change d0 (u126 p) = d0 p
  exact allUpdate78 p
theorem gammaAfter569 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) = d0 p := by
  change bonus 172 _ = _
  rw [at172]
  rfl
theorem gammaAfter570 (p : Pattern) : bonus (HazardPattern.nextHero (.push 172 (.stay 194))) (HazardPattern.afterPattern 10000 p (.push 172 (.stay 194))) = d0 p := by
  change bonus 172 _ = _
  rw [at172]
  change d0 (u213 p) = d0 p
  exact allUpdate129 p
theorem gammaAfter571 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter572 (p : Pattern) : bonus (HazardPattern.nextHero (.push 149 (.stay 148))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 148))) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  change d0 (u161 p) = d0 p
  exact allUpdate101 p
theorem gammaAfter573 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 127)) (HazardPattern.afterPattern 10000 p (.walk 127)) = d0 p := by
  change bonus 127 _ = _
  rw [at127]
  rfl
theorem gammaAfter574 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  rfl
theorem gammaAfter575 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) = d5849 p := by
  change bonus 133 _ = _
  rw [at133]
  rfl
theorem gammaAfter576 (p : Pattern) : bonus (HazardPattern.nextHero (.push 133 (.stay 111))) (HazardPattern.afterPattern 10000 p (.push 133 (.stay 111))) = d0 p := by
  change bonus 133 _ = _
  rw [at133]
  change d5849 (u128 p) = d0 p
  exact allUpdate5300 p
theorem gammaAfter577 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) = d5849 p := by
  change bonus 177 _ = _
  rw [at177]
  rfl
theorem gammaAfter578 (p : Pattern) : bonus (HazardPattern.nextHero (.push 177 (.stay 199))) (HazardPattern.afterPattern 10000 p (.push 177 (.stay 199))) = d0 p := by
  change bonus 177 _ = _
  rw [at177]
  change d5849 (u215 p) = d0 p
  exact allUpdate6265 p
theorem gammaAfter579 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter580 (p : Pattern) : bonus (HazardPattern.nextHero (.push 156 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 157))) = d134046 p := by
  change bonus 156 _ = _
  rw [at156]
  change d5849 (u169 p) = d134046 p
  exact allUpdate6256 p
theorem gammaAfter581 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter582 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter583 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter584 (p : Pattern) : bonus (HazardPattern.nextHero (.push 157 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 158))) = d136857 p := by
  change bonus 157 _ = _
  rw [at157]
  change d12224 (u171 p) = d136857 p
  exact allUpdate11273 p
theorem gammaAfter585 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) = d5849 p := by
  change bonus 155 _ = _
  rw [at155]
  rfl
theorem gammaAfter586 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter587 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 133)) (HazardPattern.afterPattern 10000 p (.walk 133)) = d5849 p := by
  change bonus 133 _ = _
  rw [at133]
  rfl
theorem gammaAfter588 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 177)) (HazardPattern.afterPattern 10000 p (.walk 177)) = d5849 p := by
  change bonus 177 _ = _
  rw [at177]
  rfl
theorem gammaAfter589 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter590 (p : Pattern) : bonus (HazardPattern.nextHero (.push 135 (.stay 113))) (HazardPattern.afterPattern 10000 p (.push 135 (.stay 113))) = d140066 p := by
  change bonus 135 _ = _
  rw [at135]
  change d8234 (u132 p) = d140066 p
  exact allUpdate8959 p
theorem gammaAfter591 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter592 (p : Pattern) : bonus (HazardPattern.nextHero (.push 158 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 159))) = d144103 p := by
  change bonus 158 _ = _
  rw [at158]
  change d13979 (u174 p) = d144103 p
  exact allUpdate12742 p
theorem gammaAfter593 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter594 (p : Pattern) : bonus (HazardPattern.nextHero (.push 156 (.stay 155))) (HazardPattern.afterPattern 10000 p (.push 156 (.stay 155))) = d0 p := by
  change bonus 156 _ = _
  rw [at156]
  change d5849 (u168 p) = d0 p
  exact allUpdate5792 p
theorem gammaAfter595 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter596 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 134)) (HazardPattern.afterPattern 10000 p (.walk 134)) = d5849 p := by
  change bonus 134 _ = _
  rw [at134]
  rfl
theorem gammaAfter597 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) = d23134 p := by
  change bonus 180 _ = _
  rw [at180]
  rfl
theorem gammaAfter598 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter599 (p : Pattern) : bonus (HazardPattern.nextHero (.push 136 (.stay 114))) (HazardPattern.afterPattern 10000 p (.push 136 (.stay 114))) = d0 p := by
  change bonus 136 _ = _
  rw [at136]
  change d9291 (u136 p) = d0 p
  exact allUpdate9850 p
end NetHack.Soko22Hazard87
