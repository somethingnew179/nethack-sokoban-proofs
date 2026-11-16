import Owner1007.Lower141
import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Sokoban.Generated.Soko32Macro147M764Solution

namespace Owner1007.Interval32_141
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

theorem interval : PushInterval soko3_2 141 147 :=
  ⟨fun _ _ _ _ trace completed => Lower141.pushes_lower_bound trace completed,
    ⟨Generated.soko3_2Macro147M764Path, Generated.soko3_2Macro147M764FinalState, 764,
      Generated.soko3_2_macro147_m764_trace, Generated.soko3_2_macro147_m764_goal⟩⟩

theorem lower_bound : ∀ directions final pushes moves,
    Trace soko3_2.board soko3_2.initial directions final pushes moves → Goal final → 141 ≤ pushes :=
  interval.lower_bound

theorem upper_bound : ∃ directions final moves,
    Trace soko3_2.board soko3_2.initial directions final 147 moves ∧ Goal final :=
  interval.upper_bound

#check @lower_bound
#check @upper_bound
#print axioms interval
#print axioms lower_bound
#print axioms upper_bound
end Owner1007.Interval32_141
