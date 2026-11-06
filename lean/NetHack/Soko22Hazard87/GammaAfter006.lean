import NetHack.Soko22Hazard87.GammaAfter005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter600 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) = d23134 p := by
  change bonus 180 _ = _
  rw [at180]
  rfl
theorem gammaAfter601 (p : Pattern) : bonus (HazardPattern.nextHero (.push 180 (.stay 202))) (HazardPattern.afterPattern 10000 p (.push 180 (.stay 202))) = d154952 p := by
  change bonus 180 _ = _
  rw [at180]
  change d23134 (u217 p) = d154952 p
  exact allUpdate21196 p
theorem gammaAfter602 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter603 (p : Pattern) : bonus (HazardPattern.nextHero (.push 159 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 160))) = d0 p := by
  change bonus 159 _ = _
  rw [at159]
  change d15965 (u177 p) = d0 p
  exact allUpdate14182 p
theorem gammaAfter604 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter605 (p : Pattern) : bonus (HazardPattern.nextHero (.push 157 (.stay 156))) (HazardPattern.afterPattern 10000 p (.push 157 (.stay 156))) = d0 p := by
  change bonus 157 _ = _
  rw [at157]
  change d12224 (u170 p) = d0 p
  exact allUpdate10811 p
theorem gammaAfter606 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 135)) (HazardPattern.afterPattern 10000 p (.walk 135)) = d8234 p := by
  change bonus 135 _ = _
  rw [at135]
  rfl
theorem gammaAfter607 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) = d17560 p := by
  change bonus 181 _ = _
  rw [at181]
  rfl
theorem gammaAfter608 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) = d17560 p := by
  change bonus 181 _ = _
  rw [at181]
  rfl
theorem gammaAfter609 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) = d17560 p := by
  change bonus 160 _ = _
  rw [at160]
  rfl
theorem gammaAfter610 (p : Pattern) : bonus (HazardPattern.nextHero (.push 160 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 161))) = d165069 p := by
  change bonus 160 _ = _
  rw [at160]
  change d17560 (u180 p) = d165069 p
  exact allUpdate15848 p
theorem gammaAfter611 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter612 (p : Pattern) : bonus (HazardPattern.nextHero (.push 158 (.stay 157))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 157))) = d167238 p := by
  change bonus 158 _ = _
  rw [at158]
  change d13979 (u173 p) = d167238 p
  exact allUpdate12247 p
theorem gammaAfter613 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  rfl
theorem gammaAfter614 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 136)) (HazardPattern.afterPattern 10000 p (.walk 136)) = d9291 p := by
  change bonus 136 _ = _
  rw [at136]
  rfl
theorem gammaAfter615 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) = d17560 p := by
  change bonus 182 _ = _
  rw [at182]
  rfl
theorem gammaAfter616 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) = d23134 p := by
  change bonus 180 _ = _
  rw [at180]
  rfl
theorem gammaAfter617 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  rfl
theorem gammaAfter618 (p : Pattern) : bonus (HazardPattern.nextHero (.push 138 (.stay 116))) (HazardPattern.afterPattern 10000 p (.push 138 (.stay 116))) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  change d0 (u138 p) = d0 p
  exact allUpdate80 p
theorem gammaAfter619 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) = d17560 p := by
  change bonus 182 _ = _
  rw [at182]
  rfl
theorem gammaAfter620 (p : Pattern) : bonus (HazardPattern.nextHero (.push 182 (.stay 204))) (HazardPattern.afterPattern 10000 p (.push 182 (.stay 204))) = d172575 p := by
  change bonus 182 _ = _
  rw [at182]
  change d17560 (u221 p) = d172575 p
  exact allUpdate18355 p
theorem gammaAfter621 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) = d18533 p := by
  change bonus 161 _ = _
  rw [at161]
  rfl
theorem gammaAfter622 (p : Pattern) : bonus (HazardPattern.nextHero (.push 161 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 162))) = d174647 p := by
  change bonus 161 _ = _
  rw [at161]
  change d18533 (u183 p) = d174647 p
  exact allUpdate18814 p
theorem gammaAfter623 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter624 (p : Pattern) : bonus (HazardPattern.nextHero (.push 159 (.stay 158))) (HazardPattern.afterPattern 10000 p (.push 159 (.stay 158))) = d177183 p := by
  change bonus 159 _ = _
  rw [at159]
  change d15965 (u176 p) = d177183 p
  exact allUpdate13763 p
theorem gammaAfter625 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) = d17560 p := by
  change bonus 181 _ = _
  rw [at181]
  rfl
theorem gammaAfter626 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) = d19737 p := by
  change bonus 162 _ = _
  rw [at162]
  rfl
theorem gammaAfter627 (p : Pattern) : bonus (HazardPattern.nextHero (.push 162 (.stay 163))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 163))) = d182839 p := by
  change bonus 162 _ = _
  rw [at162]
  change d19737 (u185 p) = d182839 p
  exact allUpdate19522 p
theorem gammaAfter628 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) = d17560 p := by
  change bonus 160 _ = _
  rw [at160]
  rfl
theorem gammaAfter629 (p : Pattern) : bonus (HazardPattern.nextHero (.push 160 (.stay 159))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 159))) = d186172 p := by
  change bonus 160 _ = _
  rw [at160]
  change d17560 (u179 p) = d186172 p
  exact allUpdate15276 p
theorem gammaAfter630 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 138)) (HazardPattern.afterPattern 10000 p (.walk 138)) = d0 p := by
  change bonus 138 _ = _
  rw [at138]
  rfl
theorem gammaAfter631 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) = d20891 p := by
  change bonus 184 _ = _
  rw [at184]
  rfl
theorem gammaAfter632 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) = d17560 p := by
  change bonus 182 _ = _
  rw [at182]
  rfl
theorem gammaAfter633 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) = d20891 p := by
  change bonus 184 _ = _
  rw [at184]
  rfl
theorem gammaAfter634 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter635 (p : Pattern) : bonus (HazardPattern.nextHero (.push 163 (.stay 164))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 164))) = d0 p := by
  change bonus 163 _ = _
  rw [at163]
  change d20389 (u188 p) = d0 p
  exact allUpdate20136 p
theorem gammaAfter636 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) = d18533 p := by
  change bonus 161 _ = _
  rw [at161]
  rfl
theorem gammaAfter637 (p : Pattern) : bonus (HazardPattern.nextHero (.push 161 (.stay 160))) (HazardPattern.afterPattern 10000 p (.push 161 (.stay 160))) = d0 p := by
  change bonus 161 _ = _
  rw [at161]
  change d18533 (u182 p) = d0 p
  exact allUpdate18509 p
theorem gammaAfter638 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter639 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) = d20891 p := by
  change bonus 185 _ = _
  rw [at185]
  rfl
theorem gammaAfter640 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter641 (p : Pattern) : bonus (HazardPattern.nextHero (.push 141 (.stay 119))) (HazardPattern.afterPattern 10000 p (.push 141 (.stay 119))) = d189322 p := by
  change bonus 141 _ = _
  rw [at141]
  change d10648 (u140 p) = d189322 p
  exact allUpdate10653 p
theorem gammaAfter642 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) = d20891 p := by
  change bonus 185 _ = _
  rw [at185]
  rfl
theorem gammaAfter643 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) = d20891 p := by
  change bonus 164 _ = _
  rw [at164]
  rfl
theorem gammaAfter644 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) = d19737 p := by
  change bonus 162 _ = _
  rw [at162]
  rfl
theorem gammaAfter645 (p : Pattern) : bonus (HazardPattern.nextHero (.push 162 (.stay 161))) (HazardPattern.afterPattern 10000 p (.push 162 (.stay 161))) = d191282 p := by
  change bonus 162 _ = _
  rw [at162]
  change d19737 (u184 p) = d191282 p
  exact allUpdate19168 p
theorem gammaAfter646 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) = d20891 p := by
  change bonus 186 _ = _
  rw [at186]
  rfl
theorem gammaAfter647 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) = d20891 p := by
  change bonus 184 _ = _
  rw [at184]
  rfl
theorem gammaAfter648 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) = d20891 p := by
  change bonus 186 _ = _
  rw [at186]
  rfl
theorem gammaAfter649 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter650 (p : Pattern) : bonus (HazardPattern.nextHero (.push 163 (.stay 162))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 162))) = d193613 p := by
  change bonus 163 _ = _
  rw [at163]
  change d20389 (u187 p) = d193613 p
  exact allUpdate20132 p
theorem gammaAfter651 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 141)) (HazardPattern.afterPattern 10000 p (.walk 141)) = d10648 p := by
  change bonus 141 _ = _
  rw [at141]
  rfl
theorem gammaAfter652 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) = d20891 p := by
  change bonus 185 _ = _
  rw [at185]
  rfl
theorem gammaAfter653 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  rfl
theorem gammaAfter654 (p : Pattern) : bonus (HazardPattern.nextHero (.push 144 (.stay 122))) (HazardPattern.afterPattern 10000 p (.push 144 (.stay 122))) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  change d0 (u142 p) = d0 p
  exact allUpdate82 p
theorem gammaAfter655 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) = d0 p := by
  change bonus 188 _ = _
  rw [at188]
  rfl
theorem gammaAfter656 (p : Pattern) : bonus (HazardPattern.nextHero (.push 188 (.stay 210))) (HazardPattern.afterPattern 10000 p (.push 188 (.stay 210))) = d0 p := by
  change bonus 188 _ = _
  rw [at188]
  change d0 (u225 p) = d0 p
  exact allUpdate131 p
theorem gammaAfter657 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter658 (p : Pattern) : bonus (HazardPattern.nextHero (.push 167 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 168))) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  change d0 (u194 p) = d0 p
  exact allUpdate110 p
theorem gammaAfter659 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter660 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  rfl
theorem gammaAfter661 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter662 (p : Pattern) : bonus (HazardPattern.nextHero (.push 145 (.stay 123))) (HazardPattern.afterPattern 10000 p (.push 145 (.stay 123))) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  change d0 (u144 p) = d0 p
  exact allUpdate84 p
theorem gammaAfter663 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  rfl
theorem gammaAfter664 (p : Pattern) : bonus (HazardPattern.nextHero (.push 189 (.stay 211))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 211))) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  change d0 (u229 p) = d0 p
  exact allUpdate135 p
theorem gammaAfter665 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter666 (p : Pattern) : bonus (HazardPattern.nextHero (.push 168 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 169))) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  change d0 (u198 p) = d0 p
  exact allUpdate114 p
theorem gammaAfter667 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  rfl
theorem gammaAfter668 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter669 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 144)) (HazardPattern.afterPattern 10000 p (.walk 144)) = d0 p := by
  change bonus 144 _ = _
  rw [at144]
  rfl
theorem gammaAfter670 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  rfl
theorem gammaAfter671 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) = d0 p := by
  change bonus 188 _ = _
  rw [at188]
  rfl
theorem gammaAfter672 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter673 (p : Pattern) : bonus (HazardPattern.nextHero (.push 146 (.stay 124))) (HazardPattern.afterPattern 10000 p (.push 146 (.stay 124))) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  change d0 (u148 p) = d0 p
  exact allUpdate88 p
theorem gammaAfter674 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  rfl
theorem gammaAfter675 (p : Pattern) : bonus (HazardPattern.nextHero (.push 190 (.stay 212))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 212))) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  change d0 (u233 p) = d0 p
  exact allUpdate139 p
theorem gammaAfter676 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter677 (p : Pattern) : bonus (HazardPattern.nextHero (.push 169 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 170))) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  change d0 (u202 p) = d0 p
  exact allUpdate118 p
theorem gammaAfter678 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter679 (p : Pattern) : bonus (HazardPattern.nextHero (.push 167 (.stay 166))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 166))) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  change d0 (u193 p) = d0 p
  exact allUpdate109 p
theorem gammaAfter680 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter681 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 145)) (HazardPattern.afterPattern 10000 p (.walk 145)) = d0 p := by
  change bonus 145 _ = _
  rw [at145]
  rfl
theorem gammaAfter682 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  rfl
theorem gammaAfter683 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  rfl
theorem gammaAfter684 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter685 (p : Pattern) : bonus (HazardPattern.nextHero (.push 147 (.stay 125))) (HazardPattern.afterPattern 10000 p (.push 147 (.stay 125))) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  change d0 (u152 p) = d0 p
  exact allUpdate92 p
theorem gammaAfter686 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  rfl
theorem gammaAfter687 (p : Pattern) : bonus (HazardPattern.nextHero (.push 191 (.stay 213))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 213))) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  change d0 (u237 p) = d0 p
  exact allUpdate143 p
theorem gammaAfter688 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  rfl
theorem gammaAfter689 (p : Pattern) : bonus (HazardPattern.nextHero (.push 170 (.stay 171))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 171))) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  change d0 (u206 p) = d0 p
  exact allUpdate122 p
theorem gammaAfter690 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter691 (p : Pattern) : bonus (HazardPattern.nextHero (.push 168 (.stay 167))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 167))) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  change d0 (u197 p) = d0 p
  exact allUpdate113 p
theorem gammaAfter692 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter693 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 146)) (HazardPattern.afterPattern 10000 p (.walk 146)) = d0 p := by
  change bonus 146 _ = _
  rw [at146]
  rfl
theorem gammaAfter694 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) = d0 p := by
  change bonus 192 _ = _
  rw [at192]
  rfl
theorem gammaAfter695 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  rfl
theorem gammaAfter696 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter697 (p : Pattern) : bonus (HazardPattern.nextHero (.push 148 (.stay 126))) (HazardPattern.afterPattern 10000 p (.push 148 (.stay 126))) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  change d0 (u156 p) = d0 p
  exact allUpdate96 p
theorem gammaAfter698 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) = d0 p := by
  change bonus 192 _ = _
  rw [at192]
  rfl
theorem gammaAfter699 (p : Pattern) : bonus (HazardPattern.nextHero (.push 192 (.stay 214))) (HazardPattern.afterPattern 10000 p (.push 192 (.stay 214))) = d0 p := by
  change bonus 192 _ = _
  rw [at192]
  change d0 (u241 p) = d0 p
  exact allUpdate147 p
end NetHack.Soko22Hazard87
