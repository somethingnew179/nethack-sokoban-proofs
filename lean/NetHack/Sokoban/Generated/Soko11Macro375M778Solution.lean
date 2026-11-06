import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks24
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Path : List Dir := soko1_1Macro375M778Prefix24
def soko1_1Macro375M778FinalState : State := soko1_1Macro375M778State778
theorem soko1_1_macro375_m778_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Path = some ⟨soko1_1Macro375M778FinalState,375,778⟩ := soko1_1Macro375M778_prefix24_checked
theorem soko1_1_macro375_m778_goal : Goal soko1_1Macro375M778FinalState := rfl
theorem soko1_1_macro375_m778_trace : Trace soko1_1.board soko1_1.initial soko1_1Macro375M778Path soko1_1Macro375M778FinalState 375 778 := run_sound _ _ _ _ soko1_1_macro375_m778_checked
theorem soko1_1_macro375_m778_solution : Trace soko1_1.board soko1_1.initial soko1_1Macro375M778Path soko1_1Macro375M778FinalState 375 778 ∧ Goal soko1_1Macro375M778FinalState := ⟨soko1_1_macro375_m778_trace,soko1_1_macro375_m778_goal⟩
end NetHack.Sokoban.Generated
