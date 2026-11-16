import Owner1007.RightParkedReady11
import Owner1007.PrefixPaidUpper11
import Owner1007.TaggedSix11
import Owner1007.Q190Upper11Bound
import Owner1007.Upper190SixTwo11
import Owner1007.Gate139EastImpossible11
import Owner1007.First137RestAnywhere11
import Owner1007.Left184Pocket11
import Owner1007.Left239BeforeRest11
namespace Owner1007.RightParkedReady11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem selected {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (ready : Ready first logged i) :
 [137,139,u i,189]⊆endGroup UpperBudget11.U6 before:=by
 exact (TaggedSix11.owned first logged ready.completed ready.upper ready.left186 ready.left212 ready.zero137 ready.zero139
  184 (marker i) (u i) 189 ready.tag186 ready.tag212 ready.tag188 ready.tag191).2.2.2

theorem six_at186 {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (ready : Ready first logged i) (at186 : u i=186) :
 6≤energy soko1_1.initial state UpperBudget11.U6 before:=by
 exact Upper188At18611.upper_six first (by simpa only [at186] using ready.tag188) ready.pairTwo

theorem paid_absurd {beforeDirs state beforePushes beforeMoves before dir t outcome dirs final pushes moves outcomes i source}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i)
 (at186 : u i=186) (owner : source∈[137,139,u i,189])
 (metadata : t.pushSource=some source) (paidHead : UpperLocalPrice11.paid source dir) : False:=by
 have prefixSix:=six_at186 first _ ready at186
 have lower:=PrefixPaidUpper11.plus_two first head effect last source ((selected first _ ready) owner) metadata paidHead
 have cap:=ready.upper
 omega

theorem frozen_absurd {beforeDirs state beforePushes beforeMoves before dir t outcome dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i)
 (pair : List Cell) (locked : Locked soko1_1.board pair)
 (a : Cell) (member : a∈pair) (inside : pair⊆update (locks i) outcome) : False:=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have actual:=step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual (locks i) (unique i) ready.physical
 have nextInside:=GhostSubset.update_subset _ _ _ effect (locks i) (unique i) ready.physical
 have gone : endGroup (update (locks i) outcome) outcomes=[]:=ready.gone
 have reached:=first.trace.append (Trace.cons head (Trace.nil _))
 exact Upper216Eight11.frozen_absurd last (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
  nextUnique nextInside locked (List.Subset.trans inside nextInside) member (inside member) gone

theorem outward137_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 137 (.stay 136)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) : False:=by
 have two:=First137RestAnywhere11.rest_two first head effect last ready.completed ready.zero137
 have cap:=ready.rest
 omega

theorem outward139_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 139 (.stay 140)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) : False:=by
 exact Gate139EastImpossible11.impossible first head effect last ready.completed (by have cap:=ready.upper;omega) ready.zero139

theorem q_east_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 189 (.stay 190)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) : False:=by
 let one : Logged soko1_1.board state [.east] t.state t.pushCost 1 [.push 189 (.stay 190)]:=.cons head effect (.nil _)
 let next:=first.append one
 have sequence : (before++[.push 189 (.stay 190)])++outcomes=before++.push 189 (.stay 190)::outcomes:=by
  simp only [List.append_assoc,List.singleton_append]
 have afterUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++[.push 189 (.stay 190)])++outcomes)≤8:=by
  rw [sequence];have cap:=ready.upper;omega
 have afterRest : energy soko1_1.initial final UpperBudget11.Rest ((before++[.push 189 (.stay 190)])++outcomes)≤4:=by
  rw [sequence];have cap:=ready.rest;omega
 have afterZero (cell : Cell) (isGate : cell=137∨cell=139) : ownPushes [cell] (before++[.push 189 (.stay 190)])=0:=by
  have z : ownPushes [cell] before=0:=by rcases isGate with rfl|rfl;exact ready.zero137;exact ready.zero139
  rw [ownPushes_append,no_push_unchanged _ _ z,z]
  have notOwner : (189:Cell)∉[cell]:=by rcases isGate with rfl|rfl<;>decide
  simp [ownPushes,ownPush,notOwner]
 have facts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have initialSelected:=selected first _ ready
 have lifted:=update_mono [137,139,u i,189] (endGroup UpperBudget11.U6 before) (by
  have simple:=unique i
  exact simple.sublist (by
   change [137,139,u i,189].Sublist [137,139,184,u i,189,marker i]
   simp))
  initialSelected (.push 189 (.stay 190))
 have afterSelected : [137,139,u i,190]⊆endGroup UpperBudget11.U6 (before++[.push 189 (.stay 190)]):=by
  rw [endGroup_append]
  change _⊆update (endGroup UpperBudget11.U6 before) (.push 189 (.stay 190))
  apply List.Subset.trans (l₂:=update [137,139,u i,189] (.push 189 (.stay 190))) _ lifted
  have checked : ∀i:Fin 4,[137,139,u i,190]⊆update [137,139,u i,189] (.push 189 (.stay 190)):=by decide +kernel
  exact checked i
 have prefixFour:=prefix_energy_le first one UpperBudget11.U6 (by decide) (by decide)
 have upCases : u i=187∨u i=186:=by unfold u;split<;>simp
 rcases upCases with at187|at186
 ·have afterHero : t.state.player∈Q190Upper11.region 0:=by rw [effect.2];change (189:Cell)∈Q190Upper11.region 0;decide +kernel
  have small : Q190Upper11.locks 0⊆endGroup UpperBudget11.U6 (before++[.push 189 (.stay 190)]):=by
   have eq : Q190Upper11.locks 0=[137,139,187,190]:=rfl
   rw [eq]
   simpa only [at187] using afterSelected
  have eight:=Q190Upper11.upper_eight next last ready.completed afterUpper afterRest
   (afterZero 137 (Or.inl rfl)) (afterZero 139 (Or.inr rfl))
   (by have cap:=ready.upperFour;omega) 0 small afterHero
  rw [sequence] at eight
  have cap:=ready.upper;omega
 ·have prefixSix:=six_at186 first _ ready at186
  have small : [137,139,190]⊆endGroup UpperBudget11.U6 (before++[.push 189 (.stay 190)]):=
   List.Subset.trans (by simp) afterSelected
  have afterHero : t.state.player∈UpperZero11.region 12:=by rw [effect.2];change (189:Cell)∈UpperZero11.region 12;decide +kernel
  have eight:=Upper190SixTwo11.upper_eight next last ready.completed (by omega) small afterHero
  rw [sequence] at eight
  have cap:=ready.upper;omega
#print axioms q_east_absurd
#print axioms paid_absurd
end Owner1007.RightParkedReady11
