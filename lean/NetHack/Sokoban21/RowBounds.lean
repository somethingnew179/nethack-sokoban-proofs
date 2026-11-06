/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.RowBoundsChunks23
import NetHack.Sokoban21.Range
set_option maxRecDepth 10000
namespace NetHack.Sokoban21
open NetHack.Sokoban
private theorem append_holds {α : Type} {p : α → Prop} {xs ys : List α}
    (left : ∀ x ∈ xs, p x) (right : ∀ x ∈ ys, p x) : ∀ x ∈ xs ++ ys, p x := by
  intro x member
  rcases List.mem_append.mp member with first | second
  · exact left x first
  · exact right x second
theorem all_walk0 : ∀ edge ∈ walkEdges, WalkBound edge 0 := by
  exact (append_holds walkGroup00_bound0 (append_holds walkGroup01_bound0 (append_holds walkGroup02_bound0 (append_holds walkGroup03_bound0 (append_holds walkGroup04_bound0 (append_holds walkGroup05_bound0 (append_holds walkGroup06_bound0 (append_holds walkGroup07_bound0 (append_holds walkGroup08_bound0 (append_holds walkGroup09_bound0 (append_holds walkGroup10_bound0 (append_holds walkGroup11_bound0 (append_holds walkGroup12_bound0 (append_holds walkGroup13_bound0 (append_holds walkGroup14_bound0 (append_holds walkGroup15_bound0 (append_holds walkGroup16_bound0 (by intro value member; cases member))))))))))))))))))
theorem all_walk1 : ∀ edge ∈ walkEdges, WalkBound edge 1 := by
  exact (append_holds walkGroup00_bound1 (append_holds walkGroup01_bound1 (append_holds walkGroup02_bound1 (append_holds walkGroup03_bound1 (append_holds walkGroup04_bound1 (append_holds walkGroup05_bound1 (append_holds walkGroup06_bound1 (append_holds walkGroup07_bound1 (append_holds walkGroup08_bound1 (append_holds walkGroup09_bound1 (append_holds walkGroup10_bound1 (append_holds walkGroup11_bound1 (append_holds walkGroup12_bound1 (append_holds walkGroup13_bound1 (append_holds walkGroup14_bound1 (append_holds walkGroup15_bound1 (append_holds walkGroup16_bound1 (by intro value member; cases member))))))))))))))))))
theorem all_walk2 : ∀ edge ∈ walkEdges, WalkBound edge 2 := by
  exact (append_holds walkGroup00_bound2 (append_holds walkGroup01_bound2 (append_holds walkGroup02_bound2 (append_holds walkGroup03_bound2 (append_holds walkGroup04_bound2 (append_holds walkGroup05_bound2 (append_holds walkGroup06_bound2 (append_holds walkGroup07_bound2 (append_holds walkGroup08_bound2 (append_holds walkGroup09_bound2 (append_holds walkGroup10_bound2 (append_holds walkGroup11_bound2 (append_holds walkGroup12_bound2 (append_holds walkGroup13_bound2 (append_holds walkGroup14_bound2 (append_holds walkGroup15_bound2 (append_holds walkGroup16_bound2 (by intro value member; cases member))))))))))))))))))
theorem all_walk3 : ∀ edge ∈ walkEdges, WalkBound edge 3 := by
  exact (append_holds walkGroup00_bound3 (append_holds walkGroup01_bound3 (append_holds walkGroup02_bound3 (append_holds walkGroup03_bound3 (append_holds walkGroup04_bound3 (append_holds walkGroup05_bound3 (append_holds walkGroup06_bound3 (append_holds walkGroup07_bound3 (append_holds walkGroup08_bound3 (append_holds walkGroup09_bound3 (append_holds walkGroup10_bound3 (append_holds walkGroup11_bound3 (append_holds walkGroup12_bound3 (append_holds walkGroup13_bound3 (append_holds walkGroup14_bound3 (append_holds walkGroup15_bound3 (append_holds walkGroup16_bound3 (by intro value member; cases member))))))))))))))))))
theorem walk_bounds (edge : WalkEdge) (member : edge ∈ walkEdges) (dead : Nat) (limited : dead ≤ 3) :
    WalkBound edge dead := by
  have cases : dead = 0 ∨ dead = 1 ∨ dead = 2 ∨ dead = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact all_walk0 edge member
  · exact all_walk1 edge member
  · exact all_walk2 edge member
  · exact all_walk3 edge member
theorem all_push0 : ∀ edge ∈ pushEdges, PushBound edge 0 := by
  exact (append_holds pushGroup00_bound0 (append_holds pushGroup01_bound0 (append_holds pushGroup02_bound0 (append_holds pushGroup03_bound0 (append_holds pushGroup04_bound0 (append_holds pushGroup05_bound0 (append_holds pushGroup06_bound0 (by intro value member; cases member))))))))
theorem all_push1 : ∀ edge ∈ pushEdges, PushBound edge 1 := by
  exact (append_holds pushGroup00_bound1 (append_holds pushGroup01_bound1 (append_holds pushGroup02_bound1 (append_holds pushGroup03_bound1 (append_holds pushGroup04_bound1 (append_holds pushGroup05_bound1 (append_holds pushGroup06_bound1 (by intro value member; cases member))))))))
theorem all_push2 : ∀ edge ∈ pushEdges, PushBound edge 2 := by
  exact (append_holds pushGroup00_bound2 (append_holds pushGroup01_bound2 (append_holds pushGroup02_bound2 (append_holds pushGroup03_bound2 (append_holds pushGroup04_bound2 (append_holds pushGroup05_bound2 (append_holds pushGroup06_bound2 (by intro value member; cases member))))))))
theorem all_push3 : ∀ edge ∈ pushEdges, PushBound edge 3 := by
  exact (append_holds pushGroup00_bound3 (append_holds pushGroup01_bound3 (append_holds pushGroup02_bound3 (append_holds pushGroup03_bound3 (append_holds pushGroup04_bound3 (append_holds pushGroup05_bound3 (append_holds pushGroup06_bound3 (by intro value member; cases member))))))))
theorem push_bounds (edge : PushEdge) (member : edge ∈ pushEdges) (dead : Nat) (limited : dead ≤ 3) :
    PushBound edge dead := by
  have cases : dead = 0 ∨ dead = 1 ∨ dead = 2 ∨ dead = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact all_push0 edge member
  · exact all_push1 edge member
  · exact all_push2 edge member
  · exact all_push3 edge member
theorem all_consume0 : ∀ edge ∈ pushEdges, edge.landing ∈ soko2_1.initial.holes → edge.sourceDead = false → ConsumeBound edge 0 := by
  exact (append_holds pushGroup00_consume0 (append_holds pushGroup01_consume0 (append_holds pushGroup02_consume0 (append_holds pushGroup03_consume0 (append_holds pushGroup04_consume0 (append_holds pushGroup05_consume0 (append_holds pushGroup06_consume0 (by intro value member; cases member))))))))
theorem all_consume1 : ∀ edge ∈ pushEdges, edge.landing ∈ soko2_1.initial.holes → edge.sourceDead = false → ConsumeBound edge 1 := by
  exact (append_holds pushGroup00_consume1 (append_holds pushGroup01_consume1 (append_holds pushGroup02_consume1 (append_holds pushGroup03_consume1 (append_holds pushGroup04_consume1 (append_holds pushGroup05_consume1 (append_holds pushGroup06_consume1 (by intro value member; cases member))))))))
theorem all_consume2 : ∀ edge ∈ pushEdges, edge.landing ∈ soko2_1.initial.holes → edge.sourceDead = false → ConsumeBound edge 2 := by
  exact (append_holds pushGroup00_consume2 (append_holds pushGroup01_consume2 (append_holds pushGroup02_consume2 (append_holds pushGroup03_consume2 (append_holds pushGroup04_consume2 (append_holds pushGroup05_consume2 (append_holds pushGroup06_consume2 (by intro value member; cases member))))))))
theorem all_consume3 : ∀ edge ∈ pushEdges, edge.landing ∈ soko2_1.initial.holes → edge.sourceDead = false → ConsumeBound edge 3 := by
  exact (append_holds pushGroup00_consume3 (append_holds pushGroup01_consume3 (append_holds pushGroup02_consume3 (append_holds pushGroup03_consume3 (append_holds pushGroup04_consume3 (append_holds pushGroup05_consume3 (append_holds pushGroup06_consume3 (by intro value member; cases member))))))))
theorem consume_bounds (edge : PushEdge) (member : edge ∈ pushEdges) (dead : Nat) (limited : dead ≤ 3)
    (original : edge.landing ∈ soko2_1.initial.holes) (live : edge.sourceDead = false) :
    ConsumeBound edge dead := by
  have cases : dead = 0 ∨ dead = 1 ∨ dead = 2 ∨ dead = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact all_consume0 edge member original live
  · exact all_consume1 edge member original live
  · exact all_consume2 edge member original live
  · exact all_consume3 edge member original live
end NetHack.Sokoban21
