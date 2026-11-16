import Owner1007.Inward214Pipe11Spec
import Owner1007.Dead21421511
namespace Owner1007.Inward214Pipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def deadIndex (i : Fin 8) : Fin 3:=if u i=187 then 0 else 1
theorem terminal_same : ∀i,(phase i).val=3→locks i=Dead21421511.locks (deadIndex i):=by decide +kernel
theorem terminal_region : ∀i,(phase i).val=3→region i⊆Dead21421511.region (deadIndex i):=by decide +kernel
theorem impossible {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (i : Fin 8) (tag188 : endGroup [188] before=[u i]) (tag191 : endGroup [191] before=[189])
 (inside : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone : endGroup (locks i) outcomes=[]) : False:=by
 apply ShiftedPipe11.impossible spec _ first logged upperCap prefixPair i tag188 tag191 inside hero gone
 intro state final history dirs past pastMoves pushes moves outcomes reached tail j terminal physical player gone
 have term : (phase j).val=3:=by simpa only [spec,decide_eq_true_eq] using terminal
 have same:=terminal_same j term
 have sub:=terminal_region j term
 change locks j⊆state.boulders at physical
 change state.player∈region j at player
 change endGroup (locks j) outcomes=[] at gone
 exact Dead21421511.impossible_gone reached tail (deadIndex j)
  (by rw [←same];exact physical) (sub player) (by rw [←same];exact gone)
#print axioms impossible
end Owner1007.Inward214Pipe11
