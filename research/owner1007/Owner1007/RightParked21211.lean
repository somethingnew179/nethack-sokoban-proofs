import Owner1007.TaggedFour11
import Owner1007.Left212BeforeRest11
import Owner1007.Left239BeforeRest11
import Owner1007.Left184Pocket11
namespace Owner1007.RightParked21211
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem two_cells {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (upper : energy soko1_1.initial final UpperBudget11.U6 (outcomes++last)≤6)
 (left186 : energy soko1_1.initial final [186] (outcomes++last)≤4)
 (left212 : energy soko1_1.initial final [212] (outcomes++last)≤2)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (u : Cell) (uCases : u=186∨u=187)
 (tag186 : endGroup [186] outcomes=[184]) (tag188 : endGroup [188] outcomes=[u])
 (tag191 : endGroup [191] outcomes=[189]) (hero190 : state.player=190) :
 ∃cell,(cell=213∨cell=214) ∧endGroup [212] outcomes=[cell] ∧
   Left212TwoWord11.rank cell≤energy soko1_1.initial state [212] outcomes := by
 obtain ⟨cell,member,tag212,rankBound⟩:=Left212BeforeRest11.word first suffix completed cheap rest noRest (by omega)
 obtain ⟨unique,inside,gone⟩:=TaggedFour11.owned first suffix completed upper left186 left212 184 cell u 189 tag186 tag212 tag188 tag191
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl
 ·have good : OwnedCorral11.Good LeftDeadSplit11.locks LeftDeadSplit11.region state [184,211,u,189]:=by
   refine ⟨1,?_,?_⟩
   ·rw [hero190];decide +kernel
   ·change ([184,211]:List Cell)⊆[184,211,u,189]
    simp
  exact False.elim (LeftDeadSplit11.impossible_gone first.trace suffix [184,211,u,189] unique inside good gone)
 ·rcases uCases with rfl|rfl
  ·have good : OwnedCorral11.Good Left184Pocket11.locks Left184Pocket11.region state [184,212,186,189]:=by
    refine ⟨1,?_,?_⟩
    ·rw [hero190];decide +kernel
    ·change ([184,186,212]:List Cell)⊆[184,212,186,189]
     decide
   exact False.elim (Left184Pocket11.impossible_gone first.trace suffix [184,212,186,189] unique inside good gone)
  ·have good : OwnedCorral11.Good Left184Pocket11.locks Left184Pocket11.region state [184,212,187,189]:=by
    refine ⟨0,?_,?_⟩
    ·rw [hero190];decide +kernel
    ·change ([184,187,212]:List Cell)⊆[184,212,187,189]
     decide
   exact False.elim (Left184Pocket11.impossible_gone first.trace suffix [184,212,187,189] unique inside good gone)
 ·exact ⟨213,Or.inl rfl,tag212,rankBound⟩
 ·exact ⟨214,Or.inr rfl,tag212,rankBound⟩
 ·have above : state.player∈Pure212Above11.region 1:=by rw [hero190];decide +kernel
  exact False.elim (Left239BeforeRest11.impossible first suffix completed cheap rest (by omega) noRest tag212 above)
#print axioms two_cells
end Owner1007.RightParked21211
