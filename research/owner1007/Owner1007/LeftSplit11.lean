import Owner1007.LeftWestCount11
import Owner1007.OwnedCorralAny11
import Owner1007.LoggedAppend11
import Owner1007.UpperConsumedFuture11
namespace Owner1007.LeftSplit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def locks (_ : Fin 1) : List Cell := [185,211]
def region (_ : Fin 1) : List Cell := LeftPair11.H.filter fun c => ![183,184,185,209,210,211].contains c
theorem matrix : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region LeftPair11.paid 0=true := by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have row : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp row c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region LeftPair11.paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0 := Fin.ext (by omega)
 simpa only [same] using matrix

theorem priced : ∀ state dir t outcome group,
 HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
 group.Nodup → group⊆state.boulders → group.length≤18 →
 step soko1_1.board state dir=some t → Matches state t outcome →
 OwnedCorral11.PaidStep LeftPair11.paid group dir t →
 2≤charge (groupCertificate 18).holeWeight group outcome+
   (groupCertificate 18).groupValue t.state (update group outcome)-(groupCertificate 18).groupValue state group := by
 intro state dir t outcome group valid unique inside bounded checked effect pays
 exact LeftStrict11.exit_row scalar rfl valid checked effect unique inside pays

theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) (gone : endGroup group outcomes=[]) :
 2≤energy state final group outcomes := by
 exact OwnedCorralAny11.energy_if_empty closed (by decide +kernel) (by decide +kernel)
   (groupCertificate 18) 2 priced logged (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached)
   group unique inside bounded good reached.holes_sublist.subset gone

theorem six_of_split {state final : State}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after)
 (completed : Goal final)
 (same : (endGroup [186,212] before).Perm [185,211]) (hero : state.player∈region 0)
 (cash : 2≤PaidCount11.count LeftPair11.paid [186,212] beforeDirs before) :
 6≤energy soko1_1.initial final [186,212] (before++after) := by
 by_cases enough : 6≤energy soko1_1.initial final [186,212] (before++after)
 · exact enough
 · have cheap : energy soko1_1.initial final [186,212] (before++after)<6 := by omega
   let logged := first.append last
   have gone : endGroup [186,212] (before++after)=[] := by
     have dead : ∀c∈([186,212] : List Cell), endGroup [c] (before++after)=[] := by
       intro c member
       apply Classical.byContradiction
       intro survives
       have sub : [c]⊆([186,212] : List Cell) := by
         intro x h
         have eq : x=c := List.mem_singleton.mp h
         exact eq ▸ member
       have bound := energy_subset (Trace.nil soko1_1.initial) logged [c] [186,212] (by simp) (by decide)
         sub (by decide) (by decide)
       have ledger := survivor_energy logged completed c survives
       have debt : value soko1_1.initial [c]≤-6 := by
         rcases List.mem_cons.mp member with rfl|later
         · decide +kernel
         · have eq : c=212:=List.mem_singleton.mp later
           subst c; decide +kernel
       have nn : (0:Int)≤Int.ofNat (ownPushes [c] (before++after)) := Int.natCast_nonneg _
       omega
     have count := logged.end_count_le (by decide) [186,212] (by decide) (by decide) (fun _=>false)
       (by intro c h _; exact dead c h)
     have zero : ([186,212].filter fun _=>false : List Cell)=[] := rfl
     rw [zero] at count
     exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at count; omega)
   have facts := first.end_subset (by decide) [186,212] (by decide) (by decide)
   have bounded := endGroup_length_le [186,212] before
   change (endGroup [186,212] before).length≤2 at bounded
   have currentGone : endGroup (endGroup [186,212] before) after=[] := by rw [←endGroup_append]; exact gone
   have good : OwnedCorral11.Good locks region state (endGroup [186,212] before) :=
     ⟨0,hero,fun c h=>same.mem_iff.mpr h⟩
   have tail := future_two first.trace last _ facts.1 facts.2 (by change (endGroup [186,212] before).length≤18; omega) good currentGone
   have prefixBound := PaidCount11.energy_bound priced first NetHack.SokobanLinearPhases.Map11.initial_good
     [186,212] (by decide) (by decide) (by decide)
   have split := energy_append soko1_1.initial state final [186,212] before after
   simp only [Int.ofNat_eq_natCast] at prefixBound
   omega
#print axioms matrix
#print axioms six_of_split
end Owner1007.LeftSplit11

