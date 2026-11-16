import Owner1007.Upper216Eight11
import Owner1007.LoggedAppend11
namespace Owner1007.Later216Eight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem reserve_eight {state final : State} {t : Transition}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 216 (.stay 217)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (stationary191 : ownPushes [191] before=0) (owns216 : 216∈endGroup U6 before) :
 8≤energy soko1_1.initial final U6 (before++.push 216 (.stay 217)::after) := by
 let logged := first.append (Logged.cons head effect last)
 by_cases enough : 8≤energy soko1_1.initial final U6 (before++.push 216 (.stay 217)::after)
 · exact enough
 · have cheap : energy soko1_1.initial final U6 (before++.push 216 (.stay 217)::after)<8 := by omega
   have full193:=UpperEightBudget11.cheap_others_six logged completed cheap 193 (by decide)
   have prefix193:=prefix_energy_le first (Logged.cons head effect last) [193] (by decide) (by decide)
   have guarded:=StationaryGuardsSix11.guard193 first stationary191 (by omega)
   have beforeFacts:=first.end_subset (by decide) U6 (by decide) (by decide)
   have before193:=first.end_subset (by decide) [193] (by decide) (by decide)
   have before191:=first.end_subset (by decide) [191] (by decide) (by decide)
   have tag191:=no_push_unchanged [191] before stationary191
   have selected191:=first.end_mono (by decide) [191] U6 (by decide) (by decide) (by decide)
   have owns191 : 191∈endGroup U6 before:=selected191 (by rw [tag191];simp)
   have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
   have afterActual:=step_boulders_nodup _ _ _ _ valid.1 head
   have afterReached:=first.trace.append (Trace.cons head (Trace.nil t.state))
   let current:=update (endGroup U6 before) (.push 216 (.stay 217))
   have nextUnique : current.Nodup:=GhostSubset.update_unique _ _ _ effect afterActual _ beforeFacts.1 beforeFacts.2
   have nextInside : current⊆t.state.boulders:=GhostSubset.update_subset _ _ _ effect _ beforeFacts.1 beforeFacts.2
   have beforeLength:=endGroup_length_le U6 before
   change (endGroup U6 before).length≤6 at beforeLength
   have nextLength : current.length≤18:=by
     have shrink:=update_length (endGroup U6 before) (.push 216 (.stay 217))
     change (update (endGroup U6 before) (.push 216 (.stay 217))).length≤18
     omega
   have wholeGone:=Upper216Eight11.all_gone_eight logged completed cheap
   have gone : endGroup current after=[]:=by rw [endGroup_append] at wholeGone;exact wholeGone
   have pair : [191,217]⊆current:=by
     intro c h
     change c∈update (endGroup U6 before) (.push 216 (.stay 217))
     simp only [update,move,if_pos owns216,post,List.mem_cons]
     rcases List.mem_cons.mp h with rfl|later
     · exact Or.inr ((List.mem_erase_of_ne (by decide :191≠216)).mpr owns191)
     · have same : c=217:=List.mem_singleton.mp later
       subst c;exact Or.inl rfl
   have hero : t.state.player=216:=by rw [effect.2]
   have selected193:=first.end_mono (by decide) [193] U6 (by decide) (by decide) (by decide)
   have next193:=update_mono (endGroup [193] before) (endGroup U6 before) before193.1 selected193 (.push 216 (.stay 217))
   have metadata : t.pushSource=some 216:=by rw [effect.2]
   have row:=CutStrict11.exit_row scalar rfl valid head effect beforeFacts.1 beforeFacts.2
     ⟨216,owns216,metadata,by simp [CutActor11.Exit]⟩
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup U6 before) (.push 216 (.stay 217))+
     value t.state current-value state (endGroup U6 before) at row
   have prefixNN:=energy_nonnegative first U6 (by decide) (by decide)
   have append:=energy_append soko1_1.initial state final U6 before (.push 216 (.stay 217)::after)
   have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final
     (endGroup U6 before) (.push 216 (.stay 217)) after
   change energy state final (endGroup U6 before) (.push 216 (.stay 217)::after)=
     charge NetHack.Soko11Hero315.holeWeight (endGroup U6 before) (.push 216 (.stay 217))+
     value t.state current-value state (endGroup U6 before)+energy t.state final current after at one
   rcases guarded with normal|shifted
   · have owns193 : 193∈current:=next193 (by rw [normal];decide)
     have triple : [191,193,217]⊆current:=by
       intro c h
       simp only [List.mem_cons,List.not_mem_nil,or_false] at h
       rcases h with rfl|rfl|rfl
       · exact pair (by decide)
       · exact owns193
       · exact pair (by decide)
     have good : OwnedCorral11.Good RightFour11.locks3 RightFour11.region3 t.state current:=by
       refine ⟨0,?_,triple⟩
       rw [hero];decide +kernel
     have tail:=Upper216Eight11.future_six afterReached last current nextUnique nextInside nextLength good gone
     omega
   · have physical192 : 192∈t.state.boulders:=by
       have present192 : 192∈state.boulders:=before193.2 (by rw [shifted];simp)
       rw [effect.2]
       exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :192≠216)).mpr present192)
     have physical : [191,192]⊆t.state.boulders:=by
       intro c h
       rcases List.mem_cons.mp h with rfl|later
       · exact nextInside (pair (by decide))
       · have same : c=192:=List.mem_singleton.mp later
         subst c;exact physical192
     exact False.elim (Upper216Eight11.frozen_absurd last afterActual nextUnique nextInside
       (Owner1007.locked_of_check _ [191,192] (by decide +kernel)) physical (show 191∈[191,192] by decide)
       (pair (show 191∈[191,217] by decide)) gone)
#print axioms reserve_eight
end Owner1007.Later216Eight11

