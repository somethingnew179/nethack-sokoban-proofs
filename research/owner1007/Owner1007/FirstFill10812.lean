import Owner1007.FirstFill10812Data
namespace Owner1007.FirstFill10812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem avoid_holes {state dir t outcome group i}
 (hero : state.player∈region i) (inside : locks i⊆group)
 (checked : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬PaidOutcome paid dir group outcome)
 (holes : state.holes⊆soko1_2.initial.holes) :
 t.state.holes=state.holes := by
 cases outcome with
 | walk target => exact congrArg (fun x : Transition=>x.state.holes) effect
 | push source ending =>
   cases ending with
   | stay dest => exact congrArg (fun x : Transition=>x.state.holes) effect.2
   | fill hole =>
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have floor := step_player_floor soko1_2.board state dir t checked
     rw [matches_hero state t (.push source (.fill hole)) effect] at floor
     have target := DeadCorridor12.effect_targets checked effect
     have forbidden := fill_guard i state.player hero dir source floor adjacent
       hole target (holes effect.2.1)
     exact False.elim (avoid ⟨inside forbidden.1,forbidden.2⟩)

theorem event_or_holes {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 4} (hero : state.player∈region i) (inside : locks i⊆group)
 (same : state.holes=soko1_2.initial.holes) :
 EventLog locks region paid group state dirs final pushes moves outcomes ∨
 final.holes=soko1_2.initial.holes := by
 classical
 induction logged generalizing history past pastMoves group i with
 | nil current => exact Or.inr same
 | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
   by_cases pays : PaidOutcome paid dir group outcome
   · exact Or.inl (.head i hero inside checked effect pays tail)
   · have actualUnique := reached.boulders_nodup (by decide +kernel)
     obtain ⟨j,nextHero,nextInside⟩ := owned_step_good_except closed unique
       state actualUnique reached.holes_sublist.subset
       (RightEnergy12.trace_disjoint reached RightEnergy12.initial_disjoint)
       group gUnique subset hero inside dir t checked outcome effect pays
     have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
     have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group gUnique subset
     have nextSubset := GhostSubset.update_subset state t outcome effect group gUnique subset
     have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
     have unchanged := avoid_holes hero inside checked effect pays reached.holes_sublist.subset
     have nextSame : t.state.holes=soko1_2.initial.holes := unchanged.trans same
     rcases ih nextReached (update group outcome) nextUnique nextSubset nextHero nextInside nextSame with event|terminal
     · exact Or.inl (.tail i hero inside checked effect pays event)
     · exact Or.inr terminal

theorem split_holes {group state dirs final pushes moves outcomes}
 (event : EventLog locks region paid group state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (same : state.holes=soko1_2.initial.holes) :
 ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after
   afterDirs afterPushes afterMoves, ∃ i : Fin 4,
   outcomes=before++outcome::after ∧
   Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
   step soko1_2.board middle dir=some t ∧ Matches middle t outcome ∧
   Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
   middle.player∈region i ∧ locks i⊆endGroup group before ∧
   PaidOutcome paid dir (endGroup group before) outcome ∧
   middle.holes=soko1_2.initial.holes := by
 induction event generalizing history past pastMoves with
 | @head group state dir t rest final pushes moves outcome outcomes i hero inside checked effect pays tail =>
   exact ⟨[],0,0,[],state,dir,t,outcome,outcomes,rest,pushes,moves,i,
     rfl,.nil state,checked,effect,tail,hero,inside,pays,same⟩
 | @tail group state dir t rest final pushes moves outcome outcomes i hero inside checked effect avoid later ih =>
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group gUnique subset
   have nextSubset := GhostSubset.update_subset state t outcome effect group gUnique subset
   have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
   have unchanged := avoid_holes hero inside checked effect avoid reached.holes_sublist.subset
   obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,one,effectOne,last,heroOne,locksOne,pays,holesOne⟩ :=
     ih nextReached nextUnique nextSubset (unchanged.trans same)
   refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
     middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,
     .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays,holesOne⟩
   simp only [List.cons_append,shape]

theorem push30_eval (state : State) (holes : state.holes=soko1_2.initial.holes) :
 pushBoulder soko1_2.board state 30 .east =
 if state.boulders.contains 31 then none else
 if (state.boulders.erase 30).contains 31 then none else
 if (state.boulders.erase 30).contains 32 then none else
 some {boulders:=state.boulders.erase 30,filled:=some 32,landing:=32} := by
 cases state with
 | mk player boxes hs =>
   simp only at holes
   subst hs
   rfl

theorem push30_fill {state t ending}
 (checked : step soko1_2.board state .east=some t)
 (effect : Matches state t (.push 30 ending))
 (holes : state.holes=soko1_2.initial.holes) : ending=.fill 32 := by
 obtain ⟨result,push,same⟩ := push_effect_result checked effect
 rw [push30_eval state holes] at push
 split at push
 · contradiction
 split at push
 · contradiction
 split at push
 · contradiction
 have actual := Option.some.inj push
 rw [←actual] at same
 exact same

theorem singleton_eq {group : List Cell} {cell : Cell}
 (short : group.length≤1) (member : cell∈group) : group=[cell] := by
 cases group with
 | nil => simp only [List.not_mem_nil] at member
 | cons c rest =>
   have empty : rest=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at short; omega)
   subst rest
   have same : cell=c := List.mem_singleton.mp member
   exact congrArg (fun n=>[n]) same.symm

theorem original_first_fill {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
 (completed : Goal final) :
 ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
 outcomes=before++(.push 30 (.fill 32))::after ∧
 Logged soko1_2.board soko1_2.initial beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .east=some t ∧ Matches middle t (.push 30 (.fill 32)) ∧
 Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
 middle.holes=soko1_2.initial.holes ∧ middle.boulders.length=20 ∧
 endGroup [108] before=[30] ∧
 endGroup [108] (before++[.push 30 (.fill 32)])=[] := by
 have start : locks 0⊆([108]:List Cell) := by decide +kernel
 have event : EventLog locks region paid [108] soko1_2.initial dirs final pushes moves outcomes := by
   rcases event_or_holes logged (Trace.nil _) [108] (by decide +kernel)
     (by decide +kernel) initial_hero start rfl with found|unchanged
   · exact found
   · have empty : final.holes=[] := completed
     rw [empty] at unchanged
     have nonempty : soko1_2.initial.holes≠[] := by decide +kernel
     exact False.elim (nonempty unchanged.symm)
 obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
   afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,hero,inside,pays,holes⟩ :=
   split_holes event (Trace.nil _) (by decide +kernel) (by decide +kernel) rfl
 cases outcome with
 | walk target => exact False.elim pays
 | push source ending =>
   obtain ⟨owner,rfl,rfl⟩ := pays
   have actual := push30_fill checked effect holes
   subst ending
   have short : (endGroup [108] before).length≤1 := by
     have bound := endGroup_length_le [108] before
     simpa using bound
   have token := singleton_eq short owner
   have disappeared : endGroup [108] (before++[.push 30 (.fill 32)])=[] := by
     rw [endGroup_append,token]
     rfl
   have conserved := first.trace.conservation
   rw [holes] at conserved
   change 20+18=middle.boulders.length+18 at conserved
   have count : middle.boulders.length=20 := by omega
   exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,after,
     afterDirs,afterPushes,afterMoves,shape,first,checked,effect,last,holes,count,token,disappeared⟩
#print axioms avoid_holes
#print axioms original_first_fill
end Owner1007.FirstFill10812
