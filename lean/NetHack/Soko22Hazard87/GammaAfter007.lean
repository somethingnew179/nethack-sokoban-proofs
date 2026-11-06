import NetHack.Soko22Hazard87.GammaAfter006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem gammaAfter700 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  rfl
theorem gammaAfter701 (p : Pattern) : bonus (HazardPattern.nextHero (.push 171 (.stay 172))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 172))) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  change d0 (u210 p) = d0 p
  exact allUpdate126 p
theorem gammaAfter702 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter703 (p : Pattern) : bonus (HazardPattern.nextHero (.push 169 (.stay 168))) (HazardPattern.afterPattern 10000 p (.push 169 (.stay 168))) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  change d0 (u201 p) = d0 p
  exact allUpdate117 p
theorem gammaAfter704 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter705 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 147)) (HazardPattern.afterPattern 10000 p (.walk 147)) = d0 p := by
  change bonus 147 _ = _
  rw [at147]
  rfl
theorem gammaAfter706 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) = d0 p := by
  change bonus 193 _ = _
  rw [at193]
  rfl
theorem gammaAfter707 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  rfl
theorem gammaAfter708 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter709 (p : Pattern) : bonus (HazardPattern.nextHero (.push 149 (.stay 127))) (HazardPattern.afterPattern 10000 p (.push 149 (.stay 127))) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  change d0 (u160 p) = d0 p
  exact allUpdate100 p
theorem gammaAfter710 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) = d0 p := by
  change bonus 193 _ = _
  rw [at193]
  rfl
theorem gammaAfter711 (p : Pattern) : bonus (HazardPattern.nextHero (.push 193 (.stay 215))) (HazardPattern.afterPattern 10000 p (.push 193 (.stay 215))) = d0 p := by
  change bonus 193 _ = _
  rw [at193]
  change d0 (u245 p) = d0 p
  exact allUpdate151 p
theorem gammaAfter712 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 172)) (HazardPattern.afterPattern 10000 p (.walk 172)) = d0 p := by
  change bonus 172 _ = _
  rw [at172]
  rfl
theorem gammaAfter713 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 170)) (HazardPattern.afterPattern 10000 p (.walk 170)) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  rfl
theorem gammaAfter714 (p : Pattern) : bonus (HazardPattern.nextHero (.push 170 (.stay 169))) (HazardPattern.afterPattern 10000 p (.push 170 (.stay 169))) = d0 p := by
  change bonus 170 _ = _
  rw [at170]
  change d0 (u205 p) = d0 p
  exact allUpdate121 p
theorem gammaAfter715 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  rfl
theorem gammaAfter716 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 148)) (HazardPattern.afterPattern 10000 p (.walk 148)) = d0 p := by
  change bonus 148 _ = _
  rw [at148]
  rfl
theorem gammaAfter717 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) = d0 p := by
  change bonus 194 _ = _
  rw [at194]
  rfl
theorem gammaAfter718 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 192)) (HazardPattern.afterPattern 10000 p (.walk 192)) = d0 p := by
  change bonus 192 _ = _
  rw [at192]
  rfl
theorem gammaAfter719 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 150)) (HazardPattern.afterPattern 10000 p (.walk 150)) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  rfl
theorem gammaAfter720 (p : Pattern) : bonus (HazardPattern.nextHero (.push 150 (.stay 128))) (HazardPattern.afterPattern 10000 p (.push 150 (.stay 128))) = d0 p := by
  change bonus 150 _ = _
  rw [at150]
  change d0 (u164 p) = d0 p
  exact allUpdate104 p
theorem gammaAfter721 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 194)) (HazardPattern.afterPattern 10000 p (.walk 194)) = d0 p := by
  change bonus 194 _ = _
  rw [at194]
  rfl
theorem gammaAfter722 (p : Pattern) : bonus (HazardPattern.nextHero (.push 194 (.stay 216))) (HazardPattern.afterPattern 10000 p (.push 194 (.stay 216))) = d0 p := by
  change bonus 194 _ = _
  rw [at194]
  change d0 (u247 p) = d0 p
  exact allUpdate153 p
theorem gammaAfter723 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 171)) (HazardPattern.afterPattern 10000 p (.walk 171)) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  rfl
theorem gammaAfter724 (p : Pattern) : bonus (HazardPattern.nextHero (.push 171 (.stay 170))) (HazardPattern.afterPattern 10000 p (.push 171 (.stay 170))) = d0 p := by
  change bonus 171 _ = _
  rw [at171]
  change d0 (u209 p) = d0 p
  exact allUpdate125 p
theorem gammaAfter725 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 149)) (HazardPattern.afterPattern 10000 p (.walk 149)) = d0 p := by
  change bonus 149 _ = _
  rw [at149]
  rfl
theorem gammaAfter726 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 193)) (HazardPattern.afterPattern 10000 p (.walk 193)) = d0 p := by
  change bonus 193 _ = _
  rw [at193]
  rfl
theorem gammaAfter727 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 155)) (HazardPattern.afterPattern 10000 p (.walk 155)) = d5849 p := by
  change bonus 155 _ = _
  rw [at155]
  rfl
theorem gammaAfter728 (p : Pattern) : bonus (HazardPattern.nextHero (.push 155 (.stay 133))) (HazardPattern.afterPattern 10000 p (.push 155 (.stay 133))) = d0 p := by
  change bonus 155 _ = _
  rw [at155]
  change d5849 (u166 p) = d0 p
  exact allUpdate5784 p
theorem gammaAfter729 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 199)) (HazardPattern.afterPattern 10000 p (.walk 199)) = d5849 p := by
  change bonus 199 _ = _
  rw [at199]
  rfl
theorem gammaAfter730 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 156)) (HazardPattern.afterPattern 10000 p (.walk 156)) = d5849 p := by
  change bonus 156 _ = _
  rw [at156]
  rfl
theorem gammaAfter731 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 200)) (HazardPattern.afterPattern 10000 p (.walk 200)) = d5849 p := by
  change bonus 200 _ = _
  rw [at200]
  rfl
theorem gammaAfter732 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter733 (p : Pattern) : bonus (HazardPattern.nextHero (.push 158 (.stay 136))) (HazardPattern.afterPattern 10000 p (.push 158 (.stay 136))) = d195382 p := by
  change bonus 158 _ = _
  rw [at158]
  change d13979 (u172 p) = d195382 p
  exact allUpdate11754 p
theorem gammaAfter734 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) = d27480 p := by
  change bonus 202 _ = _
  rw [at202]
  rfl
theorem gammaAfter735 (p : Pattern) : bonus (HazardPattern.nextHero (.push 202 (.stay 224))) (HazardPattern.afterPattern 10000 p (.push 202 (.stay 224))) = d204364 p := by
  change bonus 202 _ = _
  rw [at202]
  change d27480 (u253 p) = d204364 p
  exact allUpdate22722 p
theorem gammaAfter736 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) = d17560 p := by
  change bonus 181 _ = _
  rw [at181]
  rfl
theorem gammaAfter737 (p : Pattern) : bonus (HazardPattern.nextHero (.push 181 (.stay 182))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 182))) = d0 p := by
  change bonus 181 _ = _
  rw [at181]
  change d17560 (u219 p) = d0 p
  exact allUpdate17420 p
theorem gammaAfter738 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter739 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 157)) (HazardPattern.afterPattern 10000 p (.walk 157)) = d12224 p := by
  change bonus 157 _ = _
  rw [at157]
  rfl
theorem gammaAfter740 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 201)) (HazardPattern.afterPattern 10000 p (.walk 201)) = d25101 p := by
  change bonus 201 _ = _
  rw [at201]
  rfl
theorem gammaAfter741 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter742 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 182)) (HazardPattern.afterPattern 10000 p (.walk 182)) = d17560 p := by
  change bonus 182 _ = _
  rw [at182]
  rfl
theorem gammaAfter743 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 180)) (HazardPattern.afterPattern 10000 p (.walk 180)) = d23134 p := by
  change bonus 180 _ = _
  rw [at180]
  rfl
theorem gammaAfter744 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) = d17560 p := by
  change bonus 160 _ = _
  rw [at160]
  rfl
theorem gammaAfter745 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 158)) (HazardPattern.afterPattern 10000 p (.walk 158)) = d13979 p := by
  change bonus 158 _ = _
  rw [at158]
  rfl
theorem gammaAfter746 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) = d28738 p := by
  change bonus 204 _ = _
  rw [at204]
  rfl
theorem gammaAfter747 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 202)) (HazardPattern.afterPattern 10000 p (.walk 202)) = d27480 p := by
  change bonus 202 _ = _
  rw [at202]
  rfl
theorem gammaAfter748 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 160)) (HazardPattern.afterPattern 10000 p (.walk 160)) = d17560 p := by
  change bonus 160 _ = _
  rw [at160]
  rfl
theorem gammaAfter749 (p : Pattern) : bonus (HazardPattern.nextHero (.push 160 (.stay 138))) (HazardPattern.afterPattern 10000 p (.push 160 (.stay 138))) = d214541 p := by
  change bonus 160 _ = _
  rw [at160]
  change d17560 (u178 p) = d214541 p
  exact allUpdate14754 p
theorem gammaAfter750 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 204)) (HazardPattern.afterPattern 10000 p (.walk 204)) = d28738 p := by
  change bonus 204 _ = _
  rw [at204]
  rfl
theorem gammaAfter751 (p : Pattern) : bonus (HazardPattern.nextHero (.push 204 (.stay 226))) (HazardPattern.afterPattern 10000 p (.push 204 (.stay 226))) = d219218 p := by
  change bonus 204 _ = _
  rw [at204]
  change d28738 (u255 p) = d219218 p
  exact allUpdate23790 p
theorem gammaAfter752 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 181)) (HazardPattern.afterPattern 10000 p (.walk 181)) = d17560 p := by
  change bonus 181 _ = _
  rw [at181]
  rfl
theorem gammaAfter753 (p : Pattern) : bonus (HazardPattern.nextHero (.push 181 (.stay 180))) (HazardPattern.afterPattern 10000 p (.push 181 (.stay 180))) = d223957 p := by
  change bonus 181 _ = _
  rw [at181]
  change d17560 (u218 p) = d223957 p
  exact allUpdate16918 p
theorem gammaAfter754 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) = d18533 p := by
  change bonus 161 _ = _
  rw [at161]
  rfl
theorem gammaAfter755 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 159)) (HazardPattern.afterPattern 10000 p (.walk 159)) = d15965 p := by
  change bonus 159 _ = _
  rw [at159]
  rfl
theorem gammaAfter756 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) = d19737 p := by
  change bonus 162 _ = _
  rw [at162]
  rfl
theorem gammaAfter757 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) = d20891 p := by
  change bonus 185 _ = _
  rw [at185]
  rfl
theorem gammaAfter758 (p : Pattern) : bonus (HazardPattern.nextHero (.push 185 (.stay 186))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 186))) = d0 p := by
  change bonus 185 _ = _
  rw [at185]
  change d20891 (u223 p) = d0 p
  exact allUpdate20151 p
theorem gammaAfter759 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter760 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 161)) (HazardPattern.afterPattern 10000 p (.walk 161)) = d18533 p := by
  change bonus 161 _ = _
  rw [at161]
  rfl
theorem gammaAfter761 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter762 (p : Pattern) : bonus (HazardPattern.nextHero (.push 163 (.stay 141))) (HazardPattern.afterPattern 10000 p (.push 163 (.stay 141))) = d226708 p := by
  change bonus 163 _ = _
  rw [at163]
  change d20389 (u186 p) = d226708 p
  exact allUpdate19827 p
theorem gammaAfter763 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 186)) (HazardPattern.afterPattern 10000 p (.walk 186)) = d20891 p := by
  change bonus 186 _ = _
  rw [at186]
  rfl
theorem gammaAfter764 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 184)) (HazardPattern.afterPattern 10000 p (.walk 184)) = d20891 p := by
  change bonus 184 _ = _
  rw [at184]
  rfl
theorem gammaAfter765 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) = d20891 p := by
  change bonus 164 _ = _
  rw [at164]
  rfl
theorem gammaAfter766 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 162)) (HazardPattern.afterPattern 10000 p (.walk 162)) = d19737 p := by
  change bonus 162 _ = _
  rw [at162]
  rfl
theorem gammaAfter767 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 164)) (HazardPattern.afterPattern 10000 p (.walk 164)) = d20891 p := by
  change bonus 164 _ = _
  rw [at164]
  rfl
theorem gammaAfter768 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 185)) (HazardPattern.afterPattern 10000 p (.walk 185)) = d20891 p := by
  change bonus 185 _ = _
  rw [at185]
  rfl
theorem gammaAfter769 (p : Pattern) : bonus (HazardPattern.nextHero (.push 185 (.stay 184))) (HazardPattern.afterPattern 10000 p (.push 185 (.stay 184))) = d0 p := by
  change bonus 185 _ = _
  rw [at185]
  change d20891 (u222 p) = d0 p
  exact allUpdate20146 p
theorem gammaAfter770 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 163)) (HazardPattern.afterPattern 10000 p (.walk 163)) = d20389 p := by
  change bonus 163 _ = _
  rw [at163]
  rfl
theorem gammaAfter771 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  rfl
theorem gammaAfter772 (p : Pattern) : bonus (HazardPattern.nextHero (.push 166 (.stay 144))) (HazardPattern.afterPattern 10000 p (.push 166 (.stay 144))) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  change d0 (u190 p) = d0 p
  exact allUpdate106 p
theorem gammaAfter773 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) = d0 p := by
  change bonus 210 _ = _
  rw [at210]
  rfl
theorem gammaAfter774 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  rfl
theorem gammaAfter775 (p : Pattern) : bonus (HazardPattern.nextHero (.push 189 (.stay 190))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 190))) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  change d0 (u228 p) = d0 p
  exact allUpdate134 p
theorem gammaAfter776 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter777 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) = d0 p := by
  change bonus 211 _ = _
  rw [at211]
  rfl
theorem gammaAfter778 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter779 (p : Pattern) : bonus (HazardPattern.nextHero (.push 167 (.stay 145))) (HazardPattern.afterPattern 10000 p (.push 167 (.stay 145))) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  change d0 (u192 p) = d0 p
  exact allUpdate108 p
theorem gammaAfter780 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) = d0 p := by
  change bonus 211 _ = _
  rw [at211]
  rfl
theorem gammaAfter781 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 190)) (HazardPattern.afterPattern 10000 p (.walk 190)) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  rfl
theorem gammaAfter782 (p : Pattern) : bonus (HazardPattern.nextHero (.push 190 (.stay 191))) (HazardPattern.afterPattern 10000 p (.push 190 (.stay 191))) = d0 p := by
  change bonus 190 _ = _
  rw [at190]
  change d0 (u232 p) = d0 p
  exact allUpdate138 p
theorem gammaAfter783 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 188)) (HazardPattern.afterPattern 10000 p (.walk 188)) = d0 p := by
  change bonus 188 _ = _
  rw [at188]
  rfl
theorem gammaAfter784 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter785 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 166)) (HazardPattern.afterPattern 10000 p (.walk 166)) = d0 p := by
  change bonus 166 _ = _
  rw [at166]
  rfl
theorem gammaAfter786 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) = d0 p := by
  change bonus 212 _ = _
  rw [at212]
  rfl
theorem gammaAfter787 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 210)) (HazardPattern.afterPattern 10000 p (.walk 210)) = d0 p := by
  change bonus 210 _ = _
  rw [at210]
  rfl
theorem gammaAfter788 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 168)) (HazardPattern.afterPattern 10000 p (.walk 168)) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  rfl
theorem gammaAfter789 (p : Pattern) : bonus (HazardPattern.nextHero (.push 168 (.stay 146))) (HazardPattern.afterPattern 10000 p (.push 168 (.stay 146))) = d0 p := by
  change bonus 168 _ = _
  rw [at168]
  change d0 (u196 p) = d0 p
  exact allUpdate112 p
theorem gammaAfter790 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 212)) (HazardPattern.afterPattern 10000 p (.walk 212)) = d0 p := by
  change bonus 212 _ = _
  rw [at212]
  rfl
theorem gammaAfter791 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 191)) (HazardPattern.afterPattern 10000 p (.walk 191)) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  rfl
theorem gammaAfter792 (p : Pattern) : bonus (HazardPattern.nextHero (.push 191 (.stay 192))) (HazardPattern.afterPattern 10000 p (.push 191 (.stay 192))) = d0 p := by
  change bonus 191 _ = _
  rw [at191]
  change d0 (u236 p) = d0 p
  exact allUpdate142 p
theorem gammaAfter793 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 189)) (HazardPattern.afterPattern 10000 p (.walk 189)) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  rfl
theorem gammaAfter794 (p : Pattern) : bonus (HazardPattern.nextHero (.push 189 (.stay 188))) (HazardPattern.afterPattern 10000 p (.push 189 (.stay 188))) = d0 p := by
  change bonus 189 _ = _
  rw [at189]
  change d0 (u227 p) = d0 p
  exact allUpdate133 p
theorem gammaAfter795 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
theorem gammaAfter796 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 167)) (HazardPattern.afterPattern 10000 p (.walk 167)) = d0 p := by
  change bonus 167 _ = _
  rw [at167]
  rfl
theorem gammaAfter797 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 213)) (HazardPattern.afterPattern 10000 p (.walk 213)) = d0 p := by
  change bonus 213 _ = _
  rw [at213]
  rfl
theorem gammaAfter798 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 211)) (HazardPattern.afterPattern 10000 p (.walk 211)) = d0 p := by
  change bonus 211 _ = _
  rw [at211]
  rfl
theorem gammaAfter799 (p : Pattern) : bonus (HazardPattern.nextHero (.walk 169)) (HazardPattern.afterPattern 10000 p (.walk 169)) = d0 p := by
  change bonus 169 _ = _
  rw [at169]
  rfl
end NetHack.Soko22Hazard87
