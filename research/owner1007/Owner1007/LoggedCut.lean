import Owner1007.LoggedAppend11
namespace Owner1007.LoggedCut
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem transition_unique {state t u outcome}
 (first : Matches state t outcome) (second : Matches state u outcome) : t=u := by
 cases outcome with
 | walk target => exact first.trans second.symm
 | push source ending =>
   cases ending with
   | stay target => exact first.2.trans second.2.symm
   | fill hole => exact first.2.2.trans second.2.2.symm

theorem end_unique {board state dirs1 final1 pushes1 moves1 dirs2 final2 pushes2 moves2 outcomes}
 (first : Logged board state dirs1 final1 pushes1 moves1 outcomes)
 (second : Logged board state dirs2 final2 pushes2 moves2 outcomes) :
 final1=final2 ∧pushes1=pushes2 ∧moves1=moves2 := by
 induction first generalizing dirs2 final2 pushes2 moves2 with
 | nil => cases second;exact ⟨rfl,rfl,rfl⟩
 | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
   cases second with
   | @cons _ dir2 u rest2 final2 pushes2 moves2 _ _ checked2 effect2 tail2 =>
     have same := transition_unique effect effect2
     cases same
     obtain ⟨sameFinal,samePushes,sameMoves⟩ := ih tail2
     exact ⟨sameFinal,by omega,by omega⟩

theorem split_outcomes {board state dirs final pushes moves}
 {before after : List Outcome}
 (logged : Logged board state dirs final pushes moves (before++after)) :
 ∃ beforeDirs middle beforePushes beforeMoves afterDirs afterPushes afterMoves,
 dirs=beforeDirs++afterDirs ∧pushes=beforePushes+afterPushes ∧moves=beforeMoves+afterMoves ∧
 Logged board state beforeDirs middle beforePushes beforeMoves before ∧
 Logged board middle afterDirs final afterPushes afterMoves after := by
 induction before generalizing state dirs pushes moves with
 | nil => exact ⟨[],state,0,0,dirs,pushes,moves,rfl,(by omega),(by omega),.nil _,logged⟩
 | cons outcome rest ih =>
   cases logged with
   | @cons _ dir t ds _ ps ms _ _ checked effect tail =>
     obtain ⟨bd,middle,bp,bm,ad,ap,am,dirsEq,pushesEq,movesEq,first,last⟩ := ih tail
     refine ⟨dir::bd,middle,t.pushCost+bp,1+bm,ad,ap,am,?_,?_,?_,.cons checked effect first,last⟩
     · simp only [dirsEq,List.cons_append]
     · omega
     · omega
#print axioms transition_unique
#print axioms end_unique
#print axioms split_outcomes
end Owner1007.LoggedCut
