import Owner1007.LowerTrap31819Geometry
import Owner1007.LowerTrap31819Proof
import Owner1007.ModeC264Mass11
namespace Owner1007.OtherTrap31811
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.ModeC264Mass11 (Other)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem impossible {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 317 (.stay 318)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (zero : energy soko1_1.initial final Other (before++.push 317 (.stay 318)::after)=0)
 (owns : ([266,268,293,317,321] : List Cell)⊆endGroup Other before) : False := by
 let one : Logged soko1_1.board state [.east] t.state t.pushCost 1 [.push 317 (.stay 318)] := .cons head effect (.nil _)
 let toAfter := first.append one
 let effects := before++[.push 317 (.stay 318)]
 let group := endGroup Other effects
 have facts := toAfter.end_subset (by decide) Other (by decide) (by decide)
 have owner317 : 317∈endGroup Other before := owns (by decide)
 have selected : LowerTrap31819.locks 0⊆group := by
  change ([266,268,293,318,321] : List Cell)⊆endGroup Other (before++[.push 317 (.stay 318)])
  rw [endGroup_append]
  change ([266,268,293,318,321] : List Cell)⊆update (endGroup Other before) (.push 317 (.stay 318))
  simp only [update,move,if_pos owner317,post]
  intro c h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :266≠317)).mpr (owns (by decide)))
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :268≠317)).mpr (owns (by decide)))
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :293≠317)).mpr (owns (by decide)))
  ·exact List.mem_cons_self
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :321≠317)).mpr (owns (by decide)))
 have hero : t.state.player=317 := by rw [effect.2]
 have good : OwnedCorral11.Good LowerTrap31819.locks LowerTrap31819.region t.state group :=
  ⟨0,by rw [hero];decide +kernel,selected⟩
 have bound := endGroup_length_le Other effects
 change group.length≤9 at bound
 have cost := LowerTrap31819.future_two LowerTrap31819.closed toAfter.trace last completed group facts.1 facts.2 (by omega) good
 have prefixNN := energy_nonnegative toAfter Other (by decide) (by decide)
 change 0≤energy soko1_1.initial t.state Other effects at prefixNN
 have split := energy_append soko1_1.initial t.state final Other effects after
 have shape : effects++after=before++.push 317 (.stay 318)::after := by simp only [effects,List.append_assoc,List.singleton_append]
 rw [shape,zero] at split
 change 2≤energy t.state final (endGroup Other effects) after at cost
 omega
#print axioms impossible
end Owner1007.OtherTrap31811
