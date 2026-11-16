import Owner1007.OwnedEventsMore12
import Owner1007.TwoReserves12
namespace Owner1007.LowCoreGate12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Core : Fin 6 → List Cell
 | 0 => [262,237,238,263,291]
 | 1 => [262,237,264,263,265]
 | 2 => [262,238,264,263,265]
 | 3 => [236,237,263,264,291]
 | 4 => [236,237,263,265,290]
 | 5 => [210,237,263,265,290]
def locks (i : Fin 6) : List Cell := Core i++[213]
-- Only walking cells were generated; all six boulder footprints were prescribed.
def region : Fin 6 → List Cell
 | 0 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,210,211,212,232,236,258,284,310,336]
 | 1 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,210,211,212,232,236,238,239,258,284,310,336]
 | 2 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,210,211,212,232,236,237,258,284,310,336]
 | 3 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,210,211,212,232,238,239,258,265,284,310,336]
 | 4 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,210,211,212,232,238,239,258,264,284,310,336]
 | 5 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,211,212,232,238,239,258,264,284,310,336]
def paid (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes∧(2:Int)≤1+p.boulder dest-p.boulder source
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem large : ∀ i,2<(locks i).length := by decide +kernel
theorem hero187 : ∀ i,(187:Cell)∈region i := by decide +kernel
theorem energy_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 6)
 (hero : state.player∈region i) (subset : locks i⊆state.boulders)
 (zero187 : energy p [213] outcomes=0) :2≤energy p (Core i) outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have bound := closedExcept_energy closed unique large 2 (fun _ _ h=>h)
   logged reached (locks i) (unique i) subset completed hero (fun _ h=>h)
 change 2≤energy p (locks i) outcomes at bound
 have split := logged.energy_split (reached.boulders_nodup (by decide +kernel)) p (Core i) [213] (unique i) subset
 change energy p (locks i) outcomes=energy p (Core i) outcomes+energy p [213] outcomes at split
 omega
#print axioms matrix
#print axioms energy_two
end Owner1007.LowCoreGate12
