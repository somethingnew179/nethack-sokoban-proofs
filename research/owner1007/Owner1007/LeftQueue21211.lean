import Owner1007.LeftSplit11
namespace Owner1007.LeftQueue21211
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def locks (i : Fin 2) : List Cell := if i.val=0 then [185,210,212] else [209]
def region (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=> !(
 (if i.val=0 then [183,184,185,209,210,211,212] else [209] : List Cell).contains c)
def paid (source : Cell) (dir : Dir) : Prop := (source=185∨source=212)∧dir=.west
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1 := by omega
 rcases choices with rfl|rfl
 ·exact node0
 ·exact node1
theorem priced {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep paid group dir t) :
 2≤charge (groupCertificate 18).holeWeight group outcome+
   (groupCertificate 18).groupValue t.state (update group outcome)-(groupCertificate 18).groupValue state group := by
 obtain ⟨source,owner,metadata,⟨same,west⟩⟩ := pays
 apply LeftStrict11.exit_row scalar rfl valid head effect unique inside
 refine ⟨source,owner,metadata,?_,west⟩
 rcases same with rfl|rfl
 ·exact Or.inl rfl
 ·exact Or.inr (Or.inr (Or.inr rfl))
theorem future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) (gone : endGroup group outcomes=[]) :
 2≤energy state final group outcomes :=
 OwnedCorralAny11.energy_if_empty closed unique nonempty (groupCertificate 18) 2
   (fun _ _ _ _ _ valid unique inside bounded head effect pays=>priced valid unique inside bounded head effect pays)
   logged (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) group groupUnique inside bounded good
   reached.holes_sublist.subset gone
#print axioms closed
#print axioms future_two
end Owner1007.LeftQueue21211
