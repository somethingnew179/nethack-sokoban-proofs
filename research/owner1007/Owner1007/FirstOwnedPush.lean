import Owner1007.HeroEnergyTrace11
namespace Owner1007.FirstOwnedPush
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
/-- Extract the first initiated push of an original tracked group; no search. -/
theorem first_push {board state dirs final pushes moves outcomes}
 (logged : Logged board state dirs final pushes moves outcomes)
 (group : List Cell) (moved : 0<ownPushes group outcomes) :
 ∃ beforeDirs beforePushes beforeMoves before middle dir t source ending after afterDirs afterPushes afterMoves,
 outcomes=before++.push source ending::after ∧
 Logged board state beforeDirs middle beforePushes beforeMoves before ∧
 step board middle dir=some t ∧Matches middle t (.push source ending) ∧
 Logged board t.state afterDirs final afterPushes afterMoves after ∧
 ownPushes group before=0 ∧source∈group := by
 induction logged generalizing group with
 | nil => simp only [ownPushes] at moved;omega
 | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
   by_cases zero : ownPush group outcome=0
   · have same := ownPush_zero_update group outcome zero
     have later : 0<ownPushes group outcomes := by
       simpa only [ownPushes,zero,same,Nat.zero_add] using moved
     obtain ⟨bd,bp,bm,before,middle,payDir,u,source,ending,after,ad,ap,am,shape,first,head,matchOne,last,stationary,member⟩ := ih group later
     refine ⟨dir::bd,t.pushCost+bp,1+bm,outcome::before,middle,payDir,u,source,ending,after,ad,ap,am,?_,
       .cons checked effect first,head,matchOne,last,?_,member⟩
     · simp only [shape,List.cons_append]
     · simpa only [ownPushes,zero,same,Nat.zero_add] using stationary
   · cases outcome with
     | walk target => exact False.elim (zero rfl)
     | push source ending =>
       have member : source∈group := by
         apply Classical.byContradiction
         intro absent
         exact zero (by simp only [ownPush,if_neg absent])
       exact ⟨[],0,0,[],state,dir,t,source,ending,outcomes,rest,pushes,moves,rfl,.nil _,checked,effect,tail,rfl,member⟩
#print axioms first_push
end Owner1007.FirstOwnedPush
