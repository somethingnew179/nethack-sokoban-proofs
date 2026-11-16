import Owner1007.LeftQuietIdentity11
import Owner1007.Arrival187Left21211
import Owner1007.LeftGateReserve11
namespace Owner1007.Arrival187Four11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def front (i : Fin 2) : Cell := if i.val=0 then 187 else 186
def locks (i : Fin 2) : List Cell := [front i,212]
def region (i : Fin 2) : List Cell := LeftPair11.H.filter fun c=> !(
 (if i.val=0 then [183,184,185,186,187,209,210,211,212] else [183,184,185,186,209,210,211,212] : List Cell).contains c)
def paid (i : Fin 2) (source : Cell) (dir : Dir) : Prop := (source=front i∨source=212)∧dir=.west
instance (i : Fin 2) (source : Cell) (dir : Dir) : Decidable (paid i source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes
 (fun _:Fin 1=>locks 0) (fun _:Fin 1=>region 0) (paid 0) 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes
 (fun _:Fin 1=>locks 1) (fun _:Fin 1=>region 1) (paid 1) 0=true := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have checked : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked i (by simp)) c member)
theorem unique (i : Fin 2) : (locks i).Nodup := by
 have checked : ∀i:Fin 2,(locks i).Nodup := by decide +kernel
 exact checked i

theorem closed (i : Fin 2) : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
 (fun _:Fin 1=>locks i) (fun _:Fin 1=>region i) (paid i) := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked (fun _=>floor i)
 intro j
 have same:j=0:=Fin.ext (by omega)
 subst j
 obtain ⟨v,bound⟩:=i
 have cases:v=0∨v=1:=by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1

def noMoveCheck (i : Fin 2) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i∨BlockedPush soko1_1.board (locks i) source dir∨paid i source dir)
theorem noMove_checked : (List.finRange 2).all noMoveCheck=true := by decide +kernel
theorem noMove (i : Fin 2) : ∀hero∈region i,∀source∈locks i,∀dir,
 advance soko1_1.board hero dir=some source→BlockedPush soko1_1.board (locks i) source dir∨paid i source dir := by
 intro hero member source owner dir adjacent
 have checked := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp noMove_checked i (by simp)) source owner) dir (Geometry.all_directions dir)
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floor i member) dir source adjacent
 simp only [noMoveCheck,behind] at checked
 exact (of_decide_eq_true checked).resolve_left (fun h=>h member)

theorem first_exit {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (i : Fin 2) (inside : locks i⊆state.boulders) (hero : state.player∈region i)
 (gone212 : endGroup [212] outcomes=[]) :
 ∃cut : FirstCut (paid i) state (locks i) dirs final pushes moves outcomes,
 ownPushes (locks i) cut.beforeOutcomes=0 := by
 rcases first_cut_or_quiet (paid:=paid i) logged (locks i) with found|quiet
 ·obtain ⟨cut⟩:=found
  have zero := LeftQuietIdentity11.quiet_zero_static (locks i) (region i) (paid i) (closed i)
    (unique i) (noMove i) cut.before inside (.refl _) hero reached.holes_sublist.subset
  exact ⟨cut,zero.1⟩
 ·have zero := LeftQuietIdentity11.quiet_zero_static (locks i) (region i) (paid i) (closed i)
    (unique i) (noMove i) quiet inside (.refl _) hero reached.holes_sublist.subset
  have one := LeftQuietIdentity11.subset_zero [212] (locks i) outcomes (by simp [locks]) zero.1
  have fixed := no_push_unchanged [212] outcomes one
  rw [gone212] at fixed
  contradiction
#print axioms closed
#print axioms first_exit
end Owner1007.Arrival187Four11
