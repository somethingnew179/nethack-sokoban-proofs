import Owner1007.Lower141
import Owner1007.Witness32_141
import NetHack.Sokoban.InitialIntervalTypes

namespace Owner1007.Optimal32_141
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Exact push minimum on the full pinned original map, canonical start,
and unchanged rolling/hole Model: universal lower bound AND attained witness. -/
theorem exact_interval : PushInterval soko3_2 141 141 :=
  ⟨fun _ _ _ _ trace completed => Lower141.pushes_lower_bound trace completed,
    ⟨Witness32_141.path, Witness32_141.finalState, 610, Witness32_141.solution⟩⟩

theorem lower_bound : ∀ directions final pushes moves,
    Trace soko3_2.board soko3_2.initial directions final pushes moves → Goal final → 141 ≤ pushes :=
  exact_interval.lower_bound

theorem winning_witness : Trace soko3_2.board soko3_2.initial Witness32_141.path
    Witness32_141.finalState 141 610 ∧ Goal Witness32_141.finalState := Witness32_141.solution

theorem minimum_push_count :
    (∀ directions final pushes moves,
      Trace soko3_2.board soko3_2.initial directions final pushes moves → Goal final → 141 ≤ pushes) ∧
    (∃ directions final moves,
      Trace soko3_2.board soko3_2.initial directions final 141 moves ∧ Goal final) :=
  ⟨exact_interval.lower_bound, exact_interval.upper_bound⟩

theorem source_pin : soko3_2.id = "soko3-2" ∧
    soko3_2.sourceSHA256 = "d6d810b284cb7ba41c2ce5c3d16521010c88d89bca0ac0e64365824c7e114cd7" :=
  ⟨rfl,rfl⟩

#check @lower_bound
#check @winning_witness
#check @minimum_push_count
#print axioms exact_interval
#print axioms lower_bound
#print axioms winning_witness
#print axioms minimum_push_count
#print axioms source_pin
end Owner1007.Optimal32_141
