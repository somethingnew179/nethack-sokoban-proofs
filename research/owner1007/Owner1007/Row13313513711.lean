import Owner1007.Upper216Eight11
import Owner1007.PaidCount11
namespace Owner1007.Row13313513711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def locks (i : Fin 7) : List Cell := match i.val with
 |0=>[133,135,137] |1=>[133,136,137] |2=>[134,136,137]
 |3=>[132] |4=>[133,134] |5=>[134,135] |6=>[135,136] |_=>[]
def region (i : Fin 7) : List Cell := soko1_1.board.floor.filter fun c=>!(locks i).contains c
def paid (source : Cell) (_ : Dir) : Prop := source=137
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
theorem matrix0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem matrix1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem matrix2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true := by decide +kernel
theorem matrix3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true := by decide +kernel
theorem matrix4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 4=true := by decide +kernel
theorem matrix5 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 5=true := by decide +kernel
theorem matrix6 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 6=true := by decide +kernel
theorem checked (i : Fin 7) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩:=i
 have choices : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6:=by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact matrix0
 ·exact matrix1
 ·exact matrix2
 ·exact matrix3
 ·exact matrix4
 ·exact matrix5
 ·exact matrix6
theorem floor (i : Fin 7) : region i⊆soko1_1.board.floor := by
 intro c h
 exact (List.mem_filter.mp h).1
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
theorem unique : ∀i,(locks i).Nodup := by decide +kernel

theorem quiet_of_stationary {state dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (zero : ownPushes [137] outcomes=0) :
 UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes := by
 induction logged generalizing group with
 |nil=>exact .nil _ _
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
  have headZero : ownPush [137] outcome=0 := by simp only [ownPushes] at zero;omega
  have same := ownPush_zero_update [137] outcome headZero
  have tailZero : ownPushes [137] outcomes=0 := by simpa only [ownPushes,headZero,same,Nat.zero_add] using zero
  have avoid : ¬OwnedCorral11.PaidStep paid group dir t := by
   intro pays
   have owner := (PaidCount11.owned_iff effect).mpr pays
   cases outcome with
   |walk c=>exact owner
   |push source ending=>
    have eq : source=137 := owner.2
    subst source
    simp [ownPush] at headZero
  exact .cons head effect avoid (ih (update group outcome) tailZero)
#print axioms closed
#print axioms quiet_of_stationary
end Owner1007.Row13313513711
