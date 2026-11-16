import Owner1007.Upper188At18611
import Owner1007.UpperLocalPrice11
import Owner1007.HeroEndSubset11
import Owner1007.LoggedAppend11
namespace Owner1007.Upper189WestAt18611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem upper_eight {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 189 (.stay 188)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (tag188 : endGroup [188] before=[186]) (tag191 : endGroup [191] before=[189])
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before) :
 8≤energy soko1_1.initial final UpperBudget11.U6 (before++.push 189 (.stay 188)::after):=by
 have prefixSix:=Upper188At18611.upper_six first tag188 prefixPair
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have facts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have nested:=end_subset_selected first (by decide) [191] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
 have owner : 189∈endGroup UpperBudget11.U6 before:=nested (by rw [tag191];simp)
 have metadata : t.pushSource=some 189:=by rw [effect.2]
 have row:=UpperLocalPrice11.exit_row valid facts.1 facts.2 head effect
  ⟨189,owner,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
 have actual:=step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual _ facts.1 facts.2
 have nextInside:=GhostSubset.update_subset _ _ _ effect _ facts.1 facts.2
 have nextBound : (update (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188))).length≤18:=by
  have lenBefore:=endGroup_length_le UpperBudget11.U6 before
  have lenAfter:=update_length (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188))
  have six : UpperBudget11.U6.length=6:=rfl
  rw [six] at lenBefore
  omega
 have afterValid:=(groupCertificate 18).preserved _ _ _ valid head
 have tailNN:=HeroLedger.Logged.energy_nonnegative last (groupCertificate 18) afterValid _ nextUnique nextInside nextBound
 change 0≤energy t.state final (update (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188))) after at tailNN
 have split:=energy_append soko1_1.initial state final UpperBudget11.U6 before (.push 189 (.stay 188)::after)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final
  (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188)) after
 change energy state final (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188)::after)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188))+
   value t.state (update (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188)))-value state (endGroup UpperBudget11.U6 before)+
   energy t.state final (update (endGroup UpperBudget11.U6 before) (.push 189 (.stay 188))) after at one
 omega
#print axioms upper_eight
end Owner1007.Upper189WestAt18611
