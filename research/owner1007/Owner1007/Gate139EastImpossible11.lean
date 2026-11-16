import Owner1007.Mate141Before13911
namespace Owner1007.Gate139EastImpossible11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
theorem impossible {state final : State} {t : Transition}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 139 (.stay 140)))
 (last : Logged soko1_1.board t.state dirs final pushes moves outcomes) (completed : Goal final)
 (cap : energy soko1_1.initial final U6 (before++.push 139 (.stay 140)::outcomes)≤8)
 (fixed139 : ownPushes [139] before=0) : False := by
 have fixed141 := Mate141Before13911.stationary first (Logged.cons head effect last) completed cap fixed139
 have tag139 := no_push_unchanged [139] before fixed139
 have tag141 := no_push_unchanged [141] before fixed141
 have mono139 := first.end_mono (by decide) [139] U6 (by decide) (by decide) (by decide)
 have mono141 := first.end_mono (by decide) [141] U6 (by decide) (by decide) (by decide)
 rw [tag139] at mono139
 rw [tag141] at mono141
 have pairBefore : [139,141]⊆endGroup U6 before := by
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   · exact mono139 (by simp)
   · have same : c=141 := List.mem_singleton.mp later
     subst c
     exact mono141 (by simp)
 have transported := update_mono [139,141] (endGroup U6 before) (by decide) pairBefore (.push 139 (.stay 140))
 let one : Logged soko1_1.board state [.east] t.state t.pushCost 1 [.push 139 (.stay 140)] := .cons head effect (.nil _)
 have selected : [140,141]⊆endGroup U6 (before++[.push 139 (.stay 140)]) := by
   rw [endGroup_append]
   exact transported
 have capHead : energy soko1_1.initial final U6 ((before++[.push 139 (.stay 140)])++outcomes)≤8 := by
   simpa only [List.append_assoc,List.singleton_append] using cap
 exact UpperNoFrozen11.excluded (first.append one) last completed capHead [140,141]
   (locked_of_check _ [140,141] (by decide +kernel)) 140 (by simp) selected
#print axioms impossible
end Owner1007.Gate139EastImpossible11
