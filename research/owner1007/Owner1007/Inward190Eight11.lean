import Owner1007.Upper216Eight11
import Owner1007.LoggedAppend11
namespace Owner1007.Inward190Eight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def upper : List Cell:=PostCuts11.H.filter fun c=>decide (c<183∨c%26=24)
def locks (i : Fin 3) : List Cell:=match i.val with
 |0=>[138,139,190]
 |1=>[137,138,190]
 |_=>[164,190]
def region (i : Fin 3) : List Cell:=match i.val with
 |0=>PostCuts11.without upper [138,139,164]
 |1=>PostCuts11.without upper [137,138,164]
 |_=>PostCuts11.without upper [164]
def paid (_ : Cell) (_ : Dir) : Prop:=False
instance (c : Cell) (d : Dir) : Decidable (paid c d):=by unfold paid;infer_instance
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true:=by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true:=by decide +kernel
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor:=by
 have row : (List.finRange 3).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true:=by decide +kernel
 intro c h
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c h)
theorem unique : ∀i,(locks i).Nodup:=by decide +kernel
theorem nonempty : ∀i,locks i≠[]:=by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2:=by omega
 rcases cases with rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2

theorem reserve_eight {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (good : OwnedCorral11.Good locks region state (endGroup U6 before)) :
 8≤energy soko1_1.initial final U6 (before++outcomes):=by
 let logged:=first.append last
 by_cases enough : 8≤energy soko1_1.initial final U6 (before++outcomes)
 ·exact enough
 ·have cheap : energy soko1_1.initial final U6 (before++outcomes)<8:=by omega
  have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
  have facts:=first.end_subset (by decide) U6 (by decide) (by decide)
  have wholeGone:=Upper216Eight11.all_gone_eight logged completed cheap
  have gone : endGroup (endGroup U6 before) outcomes=[]:=by rw [←endGroup_append];exact wholeGone
  obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty last valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset gone
  obtain ⟨source,owner,metadata,impossible⟩:=cut.headPaid
  exact False.elim impossible
#print axioms reserve_eight
end Owner1007.Inward190Eight11

