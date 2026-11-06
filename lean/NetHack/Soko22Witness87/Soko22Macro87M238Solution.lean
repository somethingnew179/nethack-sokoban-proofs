import NetHack.Soko22Witness87.Soko22Macro87M238Blocks07
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Path : List Dir := soko2_2Macro87M238Prefix7
def soko2_2Macro87M238FinalState : State := soko2_2Macro87M238State238
theorem soko2_2_macro87_m238_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Path = some ⟨soko2_2Macro87M238FinalState,87,238⟩ := soko2_2Macro87M238_prefix7_checked
theorem soko2_2_macro87_m238_goal : Goal soko2_2Macro87M238FinalState := rfl
theorem soko2_2_macro87_m238_trace : Trace soko2_2.board soko2_2.initial soko2_2Macro87M238Path soko2_2Macro87M238FinalState 87 238 := run_sound _ _ _ _ soko2_2_macro87_m238_checked
theorem soko2_2_macro87_m238_solution : Trace soko2_2.board soko2_2.initial soko2_2Macro87M238Path soko2_2Macro87M238FinalState 87 238 ∧ Goal soko2_2Macro87M238FinalState := ⟨soko2_2_macro87_m238_trace,soko2_2_macro87_m238_goal⟩
end NetHack.Sokoban.Generated
