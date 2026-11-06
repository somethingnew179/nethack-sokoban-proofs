import NetHack.Soko31Witness136.Soko31Macro136M270Blocks08
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Path : List Dir := soko3_1Macro136M270Prefix8
def soko3_1Macro136M270FinalState : State := soko3_1Macro136M270State270
theorem soko3_1_macro136_m270_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Path = some ⟨soko3_1Macro136M270FinalState,136,270⟩ := soko3_1Macro136M270_prefix8_checked
theorem soko3_1_macro136_m270_goal : Goal soko3_1Macro136M270FinalState := rfl
theorem soko3_1_macro136_m270_trace : Trace soko3_1.board soko3_1.initial soko3_1Macro136M270Path soko3_1Macro136M270FinalState 136 270 := run_sound _ _ _ _ soko3_1_macro136_m270_checked
theorem soko3_1_macro136_m270_solution : Trace soko3_1.board soko3_1.initial soko3_1Macro136M270Path soko3_1Macro136M270FinalState 136 270 ∧ Goal soko3_1Macro136M270FinalState := ⟨soko3_1_macro136_m270_trace,soko3_1_macro136_m270_goal⟩
end NetHack.Sokoban.Generated
