import Owner1007.Lower326
import Owner1007.Witness11_342
import NetHack.Sokoban.InitialIntervalTypes
namespace Owner1007.Interval11_326
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals
theorem interval : PushInterval soko1_1 326 342 :=
 ⟨fun _ _ _ _ trace completed => Lower326.pushes_lower_bound trace completed,
   ⟨Witness11_342.path,Witness11_342.finalState,714,Witness11_342.solution⟩⟩
theorem lower_bound : ∀ directions final pushes moves,
 Trace soko1_1.board soko1_1.initial directions final pushes moves → Goal final → 326≤pushes := interval.lower_bound
theorem upper_bound : ∃ directions final moves,
 Trace soko1_1.board soko1_1.initial directions final 342 moves ∧ Goal final := interval.upper_bound
theorem source_pin : soko1_1.id="soko1-1" ∧ soko1_1.sourceFile="dat/soko1-1.lua" ∧
 soko1_1.sourceSHA256="b6197437573a59c1301e423cde20c49884ae9fcce478a02f4ea8e806f517a4ff" := ⟨rfl,rfl,rfl⟩
#print axioms interval
#print axioms lower_bound
#print axioms upper_bound
#print axioms source_pin
end Owner1007.Interval11_326
