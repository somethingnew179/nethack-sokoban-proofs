import Owner1007.UpperFirstCut11
namespace Owner1007.UpperReset11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.Corral11

def Reset (source : Cell) (dir : Dir) : Prop :=
  (source=138 ∧ (dir=.east ∨ dir=.west)) ∨ (source=190 ∧ dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (Reset source dir) := by unfold Reset; infer_instance
def useful (source : Cell) (dir : Dir) : Prop :=
  (source=137 ∧ dir=.west) ∨ (source=139 ∧ dir=.east) ∨ (source=191 ∧ dir=.east) ∨
  (source=190 ∧ dir=.west) ∨ (source=216 ∧ dir=.east)

def resetCheck (i : Fin 19) : Bool :=
  (UpperZero11.locks i).all fun source => allDirs.all fun dir =>
    if Reset source dir then
      match advance soko1_1.board source dir.opposite with
      | none => true
      | some hero => if hero∈UpperZero11.region i then
          decide (BlockedPush soko1_1.board (UpperZero11.locks i) source dir ∨
            Shift soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region i source dir)
        else true
    else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_checked : (List.finRange 19).all resetCheck=true := by decide +kernel

theorem reset_push (i : Fin 19) (hero : Cell) (heroInside : hero∈UpperZero11.region i)
    (heroFloor : hero∈soko1_1.board.floor) (source : Cell) (member : source∈UpperZero11.locks i)
    (dir : Dir) (reset : Reset source dir) (adjacent : advance soko1_1.board hero dir=some source) :
    BlockedPush soko1_1.board (UpperZero11.locks i) source dir ∨
      Shift soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region i source dir := by
  have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp all_checked i (by simp)) source member)
    dir (Geometry.all_directions dir)
  have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero heroFloor dir source adjacent
  simp only [resetCheck,if_pos reset,behind,if_pos heroInside] at row
  exact of_decide_eq_true row

theorem old_or_reset (source : Cell) (dir : Dir) (paid : UpperZero11.paid source dir) :
    useful source dir ∨ Reset source dir := by
  rcases paid with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,dirs⟩ | ⟨rfl,dirs⟩ | ⟨rfl,rfl⟩
  · exact Or.inl (by simp [useful])
  · exact Or.inl (by simp [useful])
  · exact Or.inl (by simp [useful])
  · exact Or.inr (Or.inl ⟨rfl,dirs⟩)
  · rcases dirs with rfl|rfl
    · exact Or.inr (Or.inr ⟨rfl,rfl⟩)
    · exact Or.inl (by simp [useful])
  · exact Or.inl (by simp [useful])

theorem reset_not_useful {source : Cell} {dir : Dir} (reset : Reset source dir) : ¬ useful source dir := by
  rcases reset with ⟨rfl,dirs⟩|⟨rfl,rfl⟩
  · rcases dirs with rfl|rfl <;> simp [useful]
  · simp [useful]

theorem useful_closed :
    PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region useful := by
  constructor
  · exact UpperZero11.closed.1
  · intro i hero heroInside dir source member adjacent
    rcases UpperZero11.closed.2 i hero heroInside dir source member adjacent with blocked|paid|shifted
    · exact Or.inl blocked
    · rcases old_or_reset source dir paid with useful | reset
      · exact Or.inr (Or.inl useful)
      · have floor : hero∈soko1_1.board.floor := UpperZero11.region_floor i heroInside
        rcases reset_push i hero heroInside floor source member dir reset adjacent with blocked|shifted
        · exact Or.inl blocked
        · exact Or.inr (Or.inr shifted)
    · exact Or.inr (Or.inr shifted)

open NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11

theorem FirstCut.after_reset {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (source : Cell) (sourceEq : cut.actor.pushSource=some source) (reset : Reset source cut.direction) :
    OwnedCorral11.Good UpperZero11.locks UpperZero11.region cut.actor.state
      (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome) := by
  have good := quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
    original_good (by simp)
  have selected := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
  have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
  change (endGroup originalGroup cut.beforeOutcomes).length≤3 at bounded
  have avoid : ¬ OwnedCorral11.PaidStep useful (endGroup originalGroup cut.beforeOutcomes) cut.direction cut.actor := by
    rintro ⟨other,_,metadata,paid⟩
    have same : other=source := Option.some.inj (metadata.symm.trans sourceEq)
    exact reset_not_useful reset (same ▸ paid)
  exact OwnedCorral11.step_good_except useful_closed UpperZero11.unique UpperZero11.size good
    selected.2 bounded cut.before.logged.trace.holes_sublist.subset cut.headChecked cut.headEffect avoid

#print axioms useful_closed
#print axioms FirstCut.after_reset
end Owner1007.UpperReset11
