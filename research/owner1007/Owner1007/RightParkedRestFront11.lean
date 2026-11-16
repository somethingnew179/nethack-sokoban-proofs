import Owner1007.RightParkedRestLeaves11
namespace Owner1007.RightParkedRestReady11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem q_west_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 189 (.stay 188)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) : False:=by
 have upCases : u i=187∨u i=186:=by unfold u;split<;>simp
 rcases upCases with up187|up186
 ·apply frozen_absurd first head effect last ready [187,188] (locked_of_check _ [187,188] (by decide +kernel)) 188 (by decide)
  change [187,188]⊆update (locks i) (.push 189 (.stay 188))
  have shift : ∀i:Fin 4,u i=187→[187,188]⊆update (locks i) (.push 189 (.stay 188)):=by decide +kernel
  exact shift i up187
 ·exact paid_absurd (source:=189) first head effect last ready up186 (by simp) (by rw [effect.2])
   (by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources])

theorem u_west_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 186 (.stay 185)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) (up186 : u i=186) : False:=by
 apply frozen_absurd first head effect last ready [184,185] (locked_of_check _ [184,185] (by decide +kernel)) 185 (by decide)
 change [184,185]⊆update (locks i) (.push 186 (.stay 185))
 have shift : ∀i:Fin 4,u i=186→[184,185]⊆update (locks i) (.push 186 (.stay 185)):=by decide +kernel
 exact shift i up186

theorem front_west_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 213 (.stay 212)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) (front213 : marker i=213) : False:=by
 let one : Logged soko1_1.board state [.west] t.state t.pushCost 1 [.push 213 (.stay 212)]:=.cons head effect (.nil _)
 have actual:=step_boulders_nodup _ _ _ _ (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual (locks i) (unique i) ready.physical
 have nextInside:=GhostSubset.update_subset _ _ _ effect (locks i) (unique i) ready.physical
 have upCases : u i=187∨u i=186:=by unfold u;split<;>simp
 obtain ⟨j,upSame⟩ : ∃j:Fin 2,Left184Pocket11.locks j=[184,u i,212]:=by
  rcases upCases with up187|up186
  ·exact ⟨0,by simpa only [up187] using (show Left184Pocket11.locks 0=[184,187,212] by rfl)⟩
  ·exact ⟨1,by simpa only [up186] using (show Left184Pocket11.locks 1=[184,186,212] by rfl)⟩
 have selected : Left184Pocket11.locks j⊆update (locks i) (.push 213 (.stay 212)):=by
  rw [upSame]
  have all : ∀i:Fin 4,marker i=213→[184,u i,212]⊆update (locks i) (.push 213 (.stay 212)):=by decide +kernel
  exact all i front213
 have hero : t.state.player∈Left184Pocket11.region j:=by
  rw [effect.2]
  have all : ∀j:Fin 2,(213:Cell)∈Left184Pocket11.region j:=by decide +kernel
  exact all j
 have gone : endGroup (update (locks i) (.push 213 (.stay 212))) outcomes=[]:=ready.gone
 exact Left184Pocket11.impossible_gone (first.append one).trace last _ nextUnique nextInside ⟨j,hero,selected⟩ gone

theorem front_south_absurd {beforeDirs state beforePushes beforeMoves before t dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .south=some t) (effect : Matches state t (.push 213 (.stay 239)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes)
 (ready : Ready first (Logged.cons head effect last) i) (front213 : marker i=213) : False:=by
 let one : Logged soko1_1.board state [.south] t.state t.pushCost 1 [.push 213 (.stay 239)]:=.cons head effect (.nil _)
 let next:=first.append one
 have sequence : (before++[.push 213 (.stay 239)])++outcomes=before++.push 213 (.stay 239)::outcomes:=by
  simp only [List.append_assoc,List.singleton_append]
 have upper : energy soko1_1.initial final UpperBudget11.Rest ((before++[.push 213 (.stay 239)])++outcomes)<2:=by
  rw [sequence];exact ready.rest
 have left212 : energy soko1_1.initial final [212] ((before++[.push 213 (.stay 239)])++outcomes)<4:=by
  rw [sequence];have cap:=ready.left212;omega
 have noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest (beforeDirs++[.south]) (before++[.push 213 (.stay 239)])=0:=by
  rw [PaidCount11.append first]
  have noPaid : ¬PaidCount11.owned FirstRest18711.paid (endGroup UpperBudget11.Rest before) .south (.push 213 (.stay 239)):=by
   simp [PaidCount11.owned,FirstRest18711.paid]
  simp only [PaidCount11.count,if_neg noPaid,Nat.add_zero,ready.noRest]
 have tag : endGroup [212] (before++[.push 213 (.stay 239)])=[239]:=by
  rw [endGroup_append,ready.tag212,front213]
  decide
 have hero : t.state.player∈Pure212Above11.region 1:=by rw [effect.2];change (213:Cell)∈Pure212Above11.region 1;decide +kernel
 exact Left239BeforeRest11.impossible next last ready.completed (by have cap:=ready.cheap;change beforePushes+t.pushCost+pushes<335;change beforePushes+(t.pushCost+pushes)<335 at cap;omega)
  upper left212 noRest tag hero
#print axioms q_west_absurd
#print axioms front_west_absurd
#print axioms front_south_absurd
end Owner1007.RightParkedRestReady11
