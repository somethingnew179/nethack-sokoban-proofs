import Owner1007.NorthPrepared12
import Owner1007.FastCorral11
namespace Owner1007.North18712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def upper : List Cell := [108,158,159,186,161]
def locks : Fin 5 → List Cell
 | 0 => [210,237,238,263,265,318,345,108,158,159,186,161,212]
 | 1 => [210,237,238,263,265,318,319,108,158,159,186,161,212]
 | 2 => [210,237,238,263,265,318,293,108,158,159,186,161,212]
 | 3 => [210,237,238,263,265,318,292,108,158,159,186,161,212]
 | 4 => [210,237,238,263,265,318,291,108,158,159,186,161,212]
def region : Fin 5 → List Cell
 | 0 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,296,297,322,348,370,371,372,373,374,396,397,399,400]
 | 1 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,296,297,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 4 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,292,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (dir : Dir) : Prop := NorthEvents12.paid source dir ∨
 (source=186 ∧ dir=.west) ∨ (source=161 ∧ dir=.north) ∨ (source=212 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem checked : ∀ i, FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true := by decide +kernel
theorem floors : ∀ i, region i ⊆ soko1_2.board.floor := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ PreCage12.reverse_checked floors checked
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=13 := by decide +kernel
def fixed : List Cell := [210,237,238,263,265,318,108,158,159,186,161,212]
theorem fixed_inside : ∀ i, fixed ⊆ locks i := by decide +kernel
def guardCheck (i : Fin 5) : Bool :=
 fixed.all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 | none=>true
 | some hero=>decide (hero∉region i ∨ BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir)
theorem guardChecked : ∀ i, guardCheck i=true := by decide +kernel
theorem fixed_guard : ∀ i hero, hero∈region i → ∀ dir source, source∈fixed →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
 intro i hero h dir source member adjacent
 have behind := Geometry.reverseCheck_sound soko1_2.board PreCage12.reverse_checked hero (floors i h) dir source adjacent
 have row := List.all_eq_true.mp (List.all_eq_true.mp (guardChecked i) source member) dir (Geometry.all_directions dir)
 simp only [guardCheck,behind] at row
 exact (of_decide_eq_true row).resolve_left (fun outside=>outside h)
theorem start_activation : ∀ i : Fin 10, PreCage12.northS i=212 →
 locks (NorthPrepared12.oldIndex i) ⊆ 161::(PreCage12.northLocks i).erase 187 ∧
 187∈region (NorthPrepared12.oldIndex i) := by decide +kernel
theorem old_region : ∀ i, region i ⊆ NorthEvents12.region i := by decide +kernel
theorem old_inside : ∀ i, NorthEvents12.locks i ⊆ locks i := by decide +kernel
theorem gate_activation : ∀ i, PriceTrap12Gate.locks 0 ⊆ 185::(locks i).erase 186 := by decide +kernel
theorem gate_hero : 186∈PriceTrap12Gate.region 0 := by decide +kernel
theorem s_activation : ∀ i, NorthEvents12.locks i++[211] ⊆ 211::(locks i).erase 212 ∧
 212∈(NorthEvents12.region i).filter (fun c=>c != 211) := by decide +kernel
def ringFrame : List Cell := [108,158,159,186,161,210,237,238,263,290,212,265]
theorem ring_activation : ∀ i, 291∈locks i → ringFrame ⊆ 290::(locks i).erase 291 := by decide +kernel

theorem has_event {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group ⊆ state.boulders)
 (completed : Goal final) {i : Fin 5}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 EventLog locks region paid group state dirs final pushes moves outcomes := by
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · exact event
 · obtain ⟨j,_,kept⟩ := terminal
   have finalInside := logged.end_subset (reached.boulders_nodup (by decide +kernel)) group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
   have amount := size j
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms closed
#print axioms has_event
end Owner1007.North18712
