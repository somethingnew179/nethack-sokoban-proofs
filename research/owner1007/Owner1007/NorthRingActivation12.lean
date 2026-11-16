import Owner1007.NorthForcedRing12
import Owner1007.CageFour12
namespace Owner1007.NorthRingActivation12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem activation_table : ∀ i : Fin 10, PreCage12.northTag i=291 →
 ∃ j : Fin 4, PreCage12.ringLocks j⊆290::(PreCage12.northLocks i).erase 291 ∧
   (291 : Cell)∈PreCage12.ringRegion j := by decide +kernel
theorem source_member : ∀ i : Fin 10, PreCage12.northTag i=291 →
 (291 : Cell)∈PreCage12.northLocks i := by decide +kernel

theorem activation {middle : State} {t : Transition} {group : List Cell}
 (effect : Matches middle t (.push 291 (.stay 290))) (i : Fin 10)
 (current : PreCage12.northTag i=291) (inside : PreCage12.northLocks i⊆group) :
 ∃ j : Fin 4, t.state.player∈PreCage12.ringRegion j ∧
   PreCage12.ringLocks j⊆update group (.push 291 (.stay 290)) := by
 obtain ⟨j,nextK,nextHero⟩ := activation_table i current
 have owner : (291 : Cell)∈group := inside (source_member i current)
 have kept := CageFour12.shifted_inside (PreCage12.north_unique i) inside owner nextK
 exact ⟨j,by rw [matches_hero middle t (.push 291 (.stay 290)) effect]; exact nextHero,kept⟩
#print axioms activation
end Owner1007.NorthRingActivation12
