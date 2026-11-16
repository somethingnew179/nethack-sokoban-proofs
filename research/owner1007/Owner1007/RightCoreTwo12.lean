import Owner1007.RightPrice4
namespace Owner1007.RightCoreTwo12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 7 → List Cell
 | 0 => [141,167,168,194]
 | 1 => [167,168,194]
 | 2 => [193,168,194]
 | 3 => [193,167,194]
 | 4 => [193,166,194]
 | 5 => [193,192,194]
 | 6 => []
def region (i : Fin 7) : List Cell := soko1_2.board.floor.filter fun c => !(locks i).contains c
def credit : Fin 7 → Int
 | 0 => 2
 | 1 => 1
 | 2 => 1
 | 3 => 1
 | 4 => 1
 | 5 => 1
 | 6 => 0
def target (i : Fin 7) (source : Cell) (dir : Dir) : Fin 7 :=
  match i.val,source,dir with
  | 0,141,_ => 1
  | 1,167,.south => 2
  | 2,168,.west => 3
  | 3,167,.west => 4
  | 4,166,.south => 5
  | _,_,_ => 6
def ShiftAt (i : Fin 7) (source : Cell) (dir : Dir) : Prop :=
  ∃ dest ∈ pushTargets soko1_2.board source dir,
    pushTargets soko1_2.board source dir=[dest] ∧ dest∉soko1_2.initial.holes ∧
    locks (target i source dir) ⊆ dest::(locks i).erase source ∧
    source∈region (target i source dir) ∧
    credit i ≤ 1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i : Fin 7) (source : Cell) (dir : Dir) : Decidable (ShiftAt i source dir) := by
  unfold ShiftAt
  infer_instance
def pushCheck (i : Fin 7) (hero : Cell) (dir : Dir) : Bool :=
  match advance soko1_2.board hero dir with
  | none => true
  | some source => !(locks i).contains source ||
    decide (BlockedPush soko1_2.board (locks i) source dir ∨ ShiftAt i source dir)
def matrixNode (i : Fin 7) : Bool := (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir && pushCheck i hero dir
theorem row0 : matrixNode 0=true := by decide +kernel
theorem row1 : matrixNode 1=true := by decide +kernel
theorem row2 : matrixNode 2=true := by decide +kernel
theorem row3 : matrixNode 3=true := by decide +kernel
theorem row4 : matrixNode 4=true := by decide +kernel
theorem row5 : matrixNode 5=true := by decide +kernel
theorem row6 : matrixNode 6=true := by decide +kernel
theorem matrix_rows : ∀ i, matrixNode i=true := by
  intro i
  obtain ⟨v,bound⟩ := i
  have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6 := by omega
  rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
  constructor
  · intro i hero heroInside dir cell adjacent floor door notLock clear
    have row := List.all_eq_true.mp (List.all_eq_true.mp (matrix_rows i) hero heroInside) dir (Geometry.all_directions dir)
    have numeric := (Bool.and_eq_true_iff.mp row).1
    simp only [Corral11.walkCheck,adjacent] at numeric
    exact of_decide_eq_true numeric ⟨floor,door,notLock,clear⟩
  · intro i hero heroInside dir source sourceInside adjacent
    have row := List.all_eq_true.mp (List.all_eq_true.mp (matrix_rows i) hero heroInside) dir (Geometry.all_directions dir)
    have numeric := (Bool.and_eq_true_iff.mp row).2
    simp only [pushCheck,adjacent,List.contains_iff_mem.mpr sourceInside,Bool.not_true,Bool.false_or] at numeric
    rcases of_decide_eq_true numeric with blocked | shifted
    · exact Or.inl blocked
    · exact Or.inr ⟨target i source dir,shifted⟩
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem phase_size : ∀ i, i.val<6 → 2<(locks i).length := by decide +kernel
theorem energy_two {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) (hero : state.player∈region 0) (inside : locks 0⊆group) :
    2 ≤ energy p group outcomes := by
  obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique
    logged reached group groupUnique subset hero inside
  have finalInside := logged.end_subset (reached.boulders_nodup (by decide +kernel)) group groupUnique subset
  have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
  have conserved := (reached.append logged.trace).conservation
  have empty : final.holes=[] := completed
  change 20+final.holes.length=final.boulders.length+18 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  have finalSmall : final.boulders.length≤2 := by omega
  have ending : j.val=6 := by
    by_cases small : j.val<6
    · have large := phase_size j small
      omega
    · have bound := j.isLt
      omega
  have same : j=(6:Fin 7) := Fin.ext ending
  subst j
  have terminalCredit : credit (6:Fin 7)=0 := rfl
  rw [terminalCredit] at price
  change 2 ≤ ownSlack p group outcomes+0 at price
  have debt := NonlinearFacts.weightSum_nonnegative (fun c=> -p.boulder c)
    (endGroup group outcomes) (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
  change 0≤debtOf p (endGroup group outcomes) at debt
  unfold energy
  omega
#print axioms closed
#print axioms energy_two
end Owner1007.RightCoreTwo12
