import Owner1007.Left184Pocket11
import Owner1007.QuietFixed11
import Owner1007.Gate265Transport11Data
import Owner1007.Left188Pocket11
namespace Owner1007.Post214LeftTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Two prescribed footprints; only184East185 is a quiet owned push. -/
def locks (i : Fin 2) : List Cell := if i.val=0 then [184,187,189,214] else [185,187,189,214]
def region (i : Fin 2) : List Cell :=
 (if i.val=0 then [183,185,186,209,210,211,212,213,239] else [183,184,186,209,210,211,212,213,239])++Gate265Transport11.lower++[265]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=184∧dir=.west)∨source=185∨source=187∨source=189∨(source=214∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance

theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 have checked : (List.finRange 2).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨v,bound⟩:=i
 have cases:v=0∨v=1:=by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1

def allowed (source : Cell) (dir : Dir) : Prop :=
 (source=184∧dir=.west)∨(source=185∧(dir=.east∨dir=.west))∨(source=187∧dir=.east)∨(source=214∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (allowed c d) := by unfold allowed;infer_instance

theorem heads : ∀i : Fin 2, ∀source∈locks i,
 Left188Pocket11.headCheck locks region source (fun dir=>¬paid source dir∨allowed source dir) i=true := by decide +kernel

theorem price214 : (List.range 16).all (fun phase=>decide ((2:Int)≤ActorPrices11.price phase 213 214 215))=true := by decide +kernel

theorem frozen183 : Locked soko1_1.board [183] := locked_of_check _ _ (by decide +kernel)
theorem frozen186187 : Locked soko1_1.board [186,187] := locked_of_check _ _ (by decide +kernel)
theorem frozen188189 : Locked soko1_1.board [188,189] := locked_of_check _ _ (by decide +kernel)
#print axioms closed
#print axioms heads
#print axioms frozen183
end Owner1007.Post214LeftTwo11
