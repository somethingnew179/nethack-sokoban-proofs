import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks18
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Path : List Dir := soko1_2Macro235M578Prefix18
def soko1_2Macro235M578FinalState : State := soko1_2Macro235M578State578
theorem soko1_2_macro235_m578_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Path = some ⟨soko1_2Macro235M578FinalState,235,578⟩ := soko1_2Macro235M578_prefix18_checked
theorem soko1_2_macro235_m578_goal : Goal soko1_2Macro235M578FinalState := rfl
theorem soko1_2_macro235_m578_trace : Trace soko1_2.board soko1_2.initial soko1_2Macro235M578Path soko1_2Macro235M578FinalState 235 578 := run_sound _ _ _ _ soko1_2_macro235_m578_checked
theorem soko1_2_macro235_m578_solution : Trace soko1_2.board soko1_2.initial soko1_2Macro235M578Path soko1_2Macro235M578FinalState 235 578 ∧ Goal soko1_2Macro235M578FinalState := ⟨soko1_2_macro235_m578_trace,soko1_2_macro235_m578_goal⟩
end NetHack.Sokoban.Generated
