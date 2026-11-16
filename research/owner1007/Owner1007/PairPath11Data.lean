import Owner1007.PricedCorral11
import Owner1007.ShaftCorral11
import Owner1007.ZeroWord11
namespace Owner1007.PairPath11
open NetHack.Sokoban
def patterns : List (List Cell) :=
  [[139,191],[138,191],[164,191],[190,191],[216,191],
   [139,190],[139,164],[139,138],[139,112]]
def locks (i : Fin 9) : List Cell := patterns[i.val]?.getD []
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def U : List Cell := ShaftCorral11.region ⟨0,by decide⟩
def B : List Cell := ZeroWord11.lowerTwo
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def region (i : Fin 9) : List Cell :=
  match i.val with
  | 0 => without H [139,191]
  | 1 => without U [138,164]
  | 2 => without U [164]
  | 3 => U
  | 4 => without H [191,192,193,194,216,217,218,219,220]
  | 5 => without B [190]
  | 6 => B
  | 7 => B ++ [164]
  | _ => without H [112,113,114,115,116,139,140,141,142]
def paid (source : Cell) (dir : Dir) : Prop :=
  (source = 139 ∧ dir = .east) ∨ (source = 191 ∧ dir = .east) ∨
  (source = 190 ∧ (dir = .east ∨ dir = .west)) ∨
  (source = 138 ∧ (dir = .east ∨ dir = .west)) ∨
  (source = 112 ∧ dir = .east) ∨ (source = 216 ∧ dir = .east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by
  unfold paid
  infer_instance
def nodeCheck (i : Fin 9) : Bool :=
  (region i).all fun hero => allDirs.all fun dir =>
    Corral11.walkCheck soko1_1.board locks region i hero dir &&
      (locks i).all fun source => decide (advance soko1_1.board hero dir ≠ some source ∨
        BlockedPush soko1_1.board (locks i) source dir ∨ paid source dir ∨
          Corral11.Shift soko1_1.board soko1_1.initial.holes locks region i source dir)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique (i : Fin 9) : (locks i).Nodup := by
  have all : (List.finRange 9).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin 9) : (locks i).length = 2 := by
  have all : (List.finRange 9).all (fun i => decide ((locks i).length = 2)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem initial_good : Corral11.Good locks region soko1_1.initial := by
  refine ⟨⟨0,by decide⟩,?_,?_⟩ <;> decide +kernel
#print axioms initial_good
end Owner1007.PairPath11
