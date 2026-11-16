import Owner1007.FirstFill10812
namespace Owner1007.FirstFill10812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem split_chronological {group state dirs final pushes moves outcomes}
 (event : EventLog locks region paid group state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (same : state.holes=soko1_2.initial.holes) :
 ∃ beforeDirs beforePushes beforeMoves before middle dir t outcome after
   afterDirs afterPushes afterMoves, ∃ i : Fin 4,
   dirs=beforeDirs++dir::afterDirs ∧
   pushes=beforePushes+t.pushCost+afterPushes ∧ moves=beforeMoves+1+afterMoves ∧
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
     rfl,by omega,by omega,rfl,.nil state,checked,effect,tail,hero,inside,pays,same⟩
 | @tail group state dir t rest final pushes moves outcome outcomes i hero inside checked effect avoid later ih =>
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group gUnique subset
   have nextSubset := GhostSubset.update_subset state t outcome effect group gUnique subset
   have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
   have unchanged := avoid_holes hero inside checked effect avoid reached.holes_sublist.subset
   obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,payDir,u,payOutcome,after,
     afterDirs,afterPushes,afterMoves,j,dirsEq,pushesEq,movesEq,shape,first,one,effectOne,last,heroOne,locksOne,pays,holesOne⟩ :=
     ih nextReached nextUnique nextSubset (unchanged.trans same)
   refine ⟨dir::beforeDirs,t.pushCost+beforePushes,1+beforeMoves,outcome::before,
     middle,payDir,u,payOutcome,after,afterDirs,afterPushes,afterMoves,j,?_,?_,?_,?_,
     .cons checked effect first,one,effectOne,last,heroOne,locksOne,pays,holesOne⟩
   · simp only [List.cons_append,dirsEq]
   · omega
   · omega
   · simp only [List.cons_append,shape]

theorem first_fill_trace {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
 (completed : Goal final) :
 ∃ beforeDirs beforePushes beforeMoves before middle t afterDirs afterPushes afterMoves,
 dirs=beforeDirs++.east::afterDirs ∧
 pushes=beforePushes+1+afterPushes ∧ moves=beforeMoves+1+afterMoves ∧
 Logged soko1_2.board soko1_2.initial beforeDirs middle beforePushes beforeMoves before ∧
 step soko1_2.board middle .east=some t ∧ Matches middle t (.push 30 (.fill 32)) ∧
 Trace soko1_2.board t.state afterDirs final afterPushes afterMoves ∧
 middle.holes=soko1_2.initial.holes ∧ middle.boulders.length=20 ∧
 endGroup [108] before=[30] := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
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
   afterDirs,afterPushes,afterMoves,i,dirsEq,pushesEq,movesEq,shape,first,checked,effect,last,hero,inside,pays,holes⟩ :=
   split_chronological event (Trace.nil _) (by decide +kernel) (by decide +kernel) rfl
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
   have conserved := first.trace.conservation
   rw [holes] at conserved
   change 20+18=middle.boulders.length+18 at conserved
   have count : middle.boulders.length=20 := by omega
   have headCost : t.pushCost=1 := by
     rw [effect.2.2]
     rfl
   rw [headCost] at pushesEq
   exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,afterDirs,afterPushes,afterMoves,
     dirsEq,pushesEq,movesEq,first,checked,effect,last.trace,holes,count,token⟩
#print axioms first_fill_trace
end Owner1007.FirstFill10812
