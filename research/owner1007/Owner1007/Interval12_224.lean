import Owner1007.Lower224
import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Sokoban.Generated.Soko12Macro235M578Solution

namespace Owner1007.Interval12_224
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

theorem interval : PushInterval soko1_2 224 235 :=
  ⟨fun _ _ _ _ trace completed => Lower224.pushes_lower_bound trace completed,
    ⟨Generated.soko1_2Macro235M578Path, Generated.soko1_2Macro235M578FinalState, 578,
      Generated.soko1_2_macro235_m578_trace, Generated.soko1_2_macro235_m578_goal⟩⟩

theorem lower_bound : ∀ directions final pushes moves,
    Trace soko1_2.board soko1_2.initial directions final pushes moves → Goal final → 224 ≤ pushes :=
  interval.lower_bound

theorem upper_bound : ∃ directions final moves,
    Trace soko1_2.board soko1_2.initial directions final 235 moves ∧ Goal final :=
  interval.upper_bound

theorem source_pin : soko1_2.id = "soko1-2" ∧ soko1_2.sourceFile = "dat/soko1-2.lua" ∧
    soko1_2.sourceSHA256 = "0fcdc3d01c24c8277e06d83b8cfd0aa3409ac8a4531e11d6bfeba7166938f561" :=
  ⟨rfl,rfl,rfl⟩

#check @lower_bound
#check @upper_bound
#print axioms interval
#print axioms lower_bound
#print axioms upper_bound
#print axioms source_pin
end Owner1007.Interval12_224
