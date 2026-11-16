import Owner1007.Upper216Eight11
import Owner1007.UpperLocalPrice11
import Owner1007.LeftStrict11
namespace Owner1007.Arrival187Left21211
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell := [187,212]
def region (_ : Fin 1) : List Cell := LeftPair11.H.filter fun c=>
 !([183,184,185,186,187,209,210,211,212] : List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop := (source=187 ∨ source=212) ∧ dir=.west
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
theorem matrix : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have row : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp row c h)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 have same : i=0:=Fin.ext (by omega)
 simpa only [same] using matrix
theorem priced {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep paid group dir t) :
 2≤charge NetHack.Soko11Hero315.holeWeight group outcome+
   value t.state (update group outcome)-value state group:=by
 obtain ⟨source,owner,metadata,pays⟩:=pays
 rcases pays with ⟨rfl|rfl,rfl⟩
 · exact UpperLocalPrice11.exit_row valid unique inside head effect
     ⟨187,owner,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
 · exact LeftStrict11.exit_row scalar rfl valid head effect unique inside
     ⟨212,owner,metadata,by simp [LeftActor11.Exit]⟩

theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (inside : [187,212]⊆state.boulders) (hero : state.player∈region 0)
 (gone : endGroup [187,212] outcomes=[]) :
 2≤energy state final [187,212] outcomes := by
 have price : ∀ state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup →group⊆state.boulders →group.length≤2 →
   step soko1_1.board state dir=some t →Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge (groupCertificate 2).holeWeight group outcome+
     (groupCertificate 2).groupValue t.state (update group outcome)-(groupCertificate 2).groupValue state group:=by
   intro state dir t outcome group valid unique inside bounded head effect pays
   exact priced valid unique inside head effect pays
 exact OwnedCorralAny11.energy_if_empty closed (by decide +kernel) (by decide +kernel)
   (groupCertificate 2) 2 price logged (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached)
   [187,212] (by decide) inside (by decide) ⟨0,hero,fun _ h=>h⟩ reached.holes_sublist.subset gone

theorem left_two_if_rest_zero {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (inside : [187,212]⊆state.boulders) (hero : state.player∈region 0)
 (gone : endGroup [187,212] outcomes=[])
 (restZero : energy state final [187] outcomes=0) :
 2≤energy state final [212] outcomes := by
 have ticket:=future_two reached logged inside hero gone
 have split:=HeroLedger.Logged.energy_split logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1 weightAt NetHack.Soko11Hero315.holeWeight
   [187] [212] (by decide) inside
 change energy state final [187,212] outcomes=energy state final [187] outcomes+energy state final [212] outcomes at split
 omega
theorem hero213 : (213:Cell)∈region 0:=by decide +kernel
#print axioms future_two
#print axioms left_two_if_rest_zero
end Owner1007.Arrival187Left21211

