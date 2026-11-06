import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks23
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Path : List Dir := soko3_2Macro147M764Prefix23
def soko3_2Macro147M764FinalState : State := soko3_2Macro147M764State764
theorem soko3_2_macro147_m764_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Path = some ⟨soko3_2Macro147M764FinalState,147,764⟩ := soko3_2Macro147M764_prefix23_checked
theorem soko3_2_macro147_m764_goal : Goal soko3_2Macro147M764FinalState := rfl
theorem soko3_2_macro147_m764_trace : Trace soko3_2.board soko3_2.initial soko3_2Macro147M764Path soko3_2Macro147M764FinalState 147 764 := run_sound _ _ _ _ soko3_2_macro147_m764_checked
theorem soko3_2_macro147_m764_solution : Trace soko3_2.board soko3_2.initial soko3_2Macro147M764Path soko3_2Macro147M764FinalState 147 764 ∧ Goal soko3_2Macro147M764FinalState := ⟨soko3_2_macro147_m764_trace,soko3_2_macro147_m764_goal⟩
end NetHack.Sokoban.Generated
