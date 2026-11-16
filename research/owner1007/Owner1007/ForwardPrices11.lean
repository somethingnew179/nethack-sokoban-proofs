import Owner1007.Upper188TagPrice11
import Owner1007.PairStrict11
import Owner1007.LoggedEventGap11
import Owner1007.UpperBudget11
import Owner1007.HeroEnergySubset11
namespace Owner1007.ForwardPrices11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem pair_two {beforeDirs state beforePushes beforeMoves before t}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 190 (.stay 189)))
 (same : (endGroup TightSplit11.A before).Perm [139,190]) :
 2≤energy soko1_1.initial t.state TightSplit11.A (before++[.push 190 (.stay 189)]) := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected:=first.end_subset (by decide) TightSplit11.A (by decide) (by decide)
 have sourceEq : t.pushSource=some 190 := by rw [effect.2]
 have row:=PairStrict11.exit_row scalar rfl valid head effect selected.1 selected.2
  ⟨190,same.mem_iff.mpr (by decide),sourceEq,by simp [PairActor11.Exit]⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup TightSplit11.A before) (.push 190 (.stay 189))+
  value t.state (update (endGroup TightSplit11.A before) (.push 190 (.stay 189)))-value state (endGroup TightSplit11.A before) at row
 have bound:=logged_event_gap_le first head effect (Logged.nil _) TightSplit11.A (by decide) (by decide)
 omega
theorem upper_four {beforeDirs state beforePushes beforeMoves before t}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 190 (.stay 189)))
 (same : (endGroup TightSplit11.A before).Perm [139,190])
 (tag188 : endGroup [188] before=[187]) :
 4≤energy soko1_1.initial t.state UpperBudget11.U6 (before++[.push 190 (.stay 189)]) := by
 have pair:=pair_two first head effect same
 let headLogged : Logged soko1_1.board state [.west] t.state t.pushCost 1 [.push 190 (.stay 189)] :=
  .cons head effect (.nil _)
 let lead:=first.append headLogged
 have next188 : endGroup [188] (before++[.push 190 (.stay 189)])=[187] := by
  rw [endGroup_append,tag188]
  simp [endGroup,update,move]
 have other:=Upper188TagPrice11.at187_two lead next188
 have partition:=energy_split lead TightSplit11.A [188] (by decide) (by decide)
 have bound:=energy_subset (Trace.nil soko1_1.initial) lead (TightSplit11.A++[188]) UpperBudget11.U6
  (by decide) (by decide) (by decide) (by decide) (by decide)
 change energy soko1_1.initial t.state (TightSplit11.A++[188]) (before++[.push 190 (.stay 189)])=
  energy soko1_1.initial t.state TightSplit11.A (before++[.push 190 (.stay 189)])+
  energy soko1_1.initial t.state [188] (before++[.push 190 (.stay 189)]) at partition
 change energy soko1_1.initial t.state (TightSplit11.A++[188]) (before++[.push 190 (.stay 189)])≤
  energy soko1_1.initial t.state UpperBudget11.U6 (before++[.push 190 (.stay 189)]) at bound
 omega
def S : List Cell := UpperBudget11.U6++[186]
theorem tail_cap {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes)
 (capUpper : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (capLeft : energy soko1_1.initial final [186] (before++outcomes)≤2)
 (prefixUpper : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (prefixLeft : 2≤energy soko1_1.initial state [186] before)
 (small : List Cell) (unique : small.Nodup) (inside : small⊆endGroup S before) :
 energy state final small outcomes≤2 := by
 let logged:=first.append last
 have fullSplit:=energy_split logged UpperBudget11.U6 [186] (by decide) (by decide)
 have beforeSplit:=energy_split first UpperBudget11.U6 [186] (by decide) (by decide)
 change energy soko1_1.initial final S (before++outcomes)=
  energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)+energy soko1_1.initial final [186] (before++outcomes) at fullSplit
 change energy soko1_1.initial state S before=
  energy soko1_1.initial state UpperBudget11.U6 before+energy soko1_1.initial state [186] before at beforeSplit
 have split:=energy_append soko1_1.initial state final S before outcomes
 have facts:=first.end_subset (by decide) S (by decide) (by decide)
 have len:=endGroup_length_le S before
 have bound:=energy_subset first.trace last small (endGroup S before) unique facts.1 inside facts.2 (by change (endGroup S before).length≤7 at len;omega)
 omega
#print axioms pair_two
#print axioms upper_four
#print axioms tail_cap
end Owner1007.ForwardPrices11
