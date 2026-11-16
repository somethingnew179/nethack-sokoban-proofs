import Owner1007.PostCuts11
import Owner1007.CutStrict11
import Owner1007.OwnedCorralBound11
import Owner1007.Hero315Frame11
namespace Owner1007.PostEnergy11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)
def locks (right : Bool) : Fin 1 → List Cell := if right then PostCuts11.rightLocks else PostCuts11.entryLocks
def region (right : Bool) : Fin 1 → List Cell := if right then PostCuts11.rightRegion else PostCuts11.entryRegion
def paid (right : Bool) : Cell → Dir → Prop := if right then PostCuts11.rightPaid else PostCuts11.entryPaid
theorem closed (right : Bool) : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
 (locks right) (region right) (paid right) := by
 cases right
 · exact PostCuts11.entry_closed
 · exact PostCuts11.right_closed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀ right i, (locks right i).Nodup := by decide +kernel
theorem size : ∀ right i, (locks right i).length=2 := by decide +kernel
def debtCheck (phase : Nat) : Bool := [false,true].all fun right =>
 (region right 0).all fun hero => decide
   (hero∈NetHack.SokobanLinearPhases.Map11.certificate.heroes phase →
    weightSum (NetHack.Soko11Hero315.weight phase hero) (locks right 0)≤-2)
theorem debts_checked : (List.range 16).all debtCheck=true := by decide +kernel
theorem debt_row (phase : Nat) (active : phase<16) (right : Bool) (hero : Cell)
 (inside : hero∈region right 0)
 (phaseHero : hero∈NetHack.SokobanLinearPhases.Map11.certificate.heroes phase) :
 weightSum (NetHack.Soko11Hero315.weight phase hero) (locks right 0)≤-2 := by
 have row := List.all_eq_true.mp debts_checked phase (List.mem_range.mpr active)
 have choice : right∈[false,true] := by cases right <;> simp
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row right choice) hero inside) phaseHero

theorem canonical_group (i : Fin 1) (right : Bool) (group : List Cell)
 (groupUnique : group.Nodup) (bounded : group.length≤2) (inside : locks right i⊆group) :
 group.Perm (locks right i) := by
 apply (List.perm_ext_iff_of_nodup groupUnique (unique right i)).mpr
 intro cell
 constructor
 · intro member
   by_cases known : cell∈locks right i
   · exact known
   · have all : cell::locks right i⊆group := by
       intro c found
       rcases List.mem_cons.mp found with rfl|later
       · exact member
       · exact inside later
     have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨known,unique right i⟩) all
     simp only [List.length_cons,size] at card
     omega
 · exact fun h => inside h

theorem is_exit (right : Bool) (source : Cell) (dir : Dir) (pays : paid right source dir) :
 CutActor11.Exit source dir := by
 cases right <;> change (_∨_)∧_ at pays <;>
   rcases pays with ⟨rfl|rfl,rfl⟩ <;> simp [CutActor11.Exit]

theorem future_energy (right : Bool)
 {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (active : phaseOf soko1_1.initial.holes state<16)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤2)
 (good : OwnedCorral11.Good (locks right) (region right) state group) :
 2≤energy state final group outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have groupSize : group.length=2 := by
   obtain ⟨i,_,subset⟩ := good
   have card := List.Nodup.length_le_of_subset (unique right i) subset
   rw [size right i] at card
   omega
 have debt : (groupCertificate 2).groupValue state group≤-(2:Int) := by
   obtain ⟨i,hero,subset⟩ := good
   have perm := canonical_group i right group groupUnique bounded subset
   have same : i=0 := Fin.ext (by omega)
   rw [same] at hero perm
   have sum := StatePermutation.weightSum_permutation (weightAt state) perm
   change weightSum (weightAt state) group≤-2
   rw [sum]
   obtain ⟨phase,atIndex⟩ := valid.2
   have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
   have phaseHero : state.player∈NetHack.SokobanLinearPhases.Map11.certificate.heroes
       (phaseOf soko1_1.initial.holes state) := by rw [←phaseEq]; exact atIndex.2.2.1
   exact debt_row _ active right state.player hero phaseHero
 have priced : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤2 →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep (paid right) group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome +
      (groupCertificate 2).groupValue t.state (update group outcome) -
      (groupCertificate 2).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded checked effect pays
   obtain ⟨source,owner,metadata,pays⟩ := pays
   exact CutStrict11.exit_row scalar rfl valid checked effect unique inside
     ⟨source,owner,metadata,is_exit right source dir pays⟩
 exact OwnedCorral11.energy_bound (closed right) (unique right) (size right) (groupCertificate 2) 2
   priced logged valid group groupUnique inside groupSize good reached.holes_sublist.subset debt
   (goal_value_zero completed _)
#print axioms debts_checked
#print axioms future_energy
end Owner1007.PostEnergy11
