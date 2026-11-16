import Owner1007.Hero315Frame11
import Owner1007.OwnedStrict11
import Owner1007.ActorPrices11
import Owner1007.PairStrict11
import Owner1007.OwnedCorral11
import Owner1007.TokenPersistence
namespace Owner1007.StationaryGuardsSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

def guardCheck (fixed : Cell) (cells : List Cell) (phase : Nat) : Bool :=
 cells.all fun source => allDirs.all fun dir =>
  match advance soko1_1.board source dir.opposite with
  | none => true
  | some hero =>
   if hero∉soko1_1.board.floor then true else
   if hero=fixed then true else
   if BlockedPush soko1_1.board [fixed] source dir then true else
   (pushTargets soko1_1.board source dir).all fun dest =>
    decide (dest ∉ soko1_1.initial.holes ∧
      (dest ∈ cells ∨ 6 ≤ ActorPrices11.price phase hero source dest))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guards141 : (List.range 16).all (guardCheck 139 [141,140]) = true := by decide +kernel
theorem guards193 : (List.range 16).all (guardCheck 191 [193,192]) = true := by decide +kernel

theorem guard_row {fixed : Cell} {cells : List Cell}
 (matrix : (List.range 16).all (guardCheck fixed cells) = true)
 (phase : Nat) (active : phase<16) (source : Cell) (member : source∈cells)
 (hero : Cell) (floor : hero∈soko1_1.board.floor) (different : hero≠fixed) (dir : Dir)
 (behind : advance soko1_1.board source dir.opposite = some hero)
 (unblocked : ¬ BlockedPush soko1_1.board [fixed] source dir)
 (dest : Cell) (target : dest∈pushTargets soko1_1.board source dir) :
 dest ∉ soko1_1.initial.holes ∧ (dest∈cells ∨ 6≤ActorPrices11.price phase hero source dest) := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp
   (List.all_eq_true.mp matrix phase (List.mem_range.mpr active)) source member)
   dir (Geometry.all_directions dir)
 simp only [guardCheck,behind,if_neg (not_not_intro floor),if_neg different,if_neg unblocked] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)

theorem one_step {fixed box : Cell} {cells : List Cell}
 (matrix : (List.range 16).all (guardCheck fixed cells) = true)
 {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
 (fixedPresent : fixed∈state.boulders) (present : box∈state.boulders) (member : box∈cells)
 (cheap : charge NetHack.Soko11Hero315.holeWeight [box] outcome +
   value t.state (update [box] outcome) - value state [box] < 6) :
 ∃ next, next∈cells ∧ update [box] outcome=[next] := by
 cases outcome with
 | walk target => exact ⟨box,member,rfl⟩
 | push source ending =>
  by_cases same : source=box
  · subst source
    have sourceEq : t.pushSource=some box := by
      cases ending with
      | stay landing => simp only [effect.2]
      | fill hole => simp only [effect.2.2]
    rcases step_cases_full _ _ _ _ checked with walked | pushed
    · obtain ⟨target,_,_,_,_,shape⟩ := walked
      simp only [shape] at sourceEq
      contradiction
    · obtain ⟨other,result,adjacent,_,_,push,shape⟩ := pushed
      have same : other=box := by simpa only [shape,Option.some.injEq] using sourceEq
      subst other
      have clear := step_player_clear _ _ _ _ checked
      have different : state.player≠fixed := by intro h; exact clear.2.2.1 (h ▸ fixedPresent)
      have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked
        state.player clear.1 dir box adjacent
      have first := push_first_clear _ _ _ _ _ push
      have unblocked : ¬ BlockedPush soko1_1.board [fixed] box dir := by
        intro blocked
        rcases blocked with diagonal | blocked
        · simp only [first.1] at diagonal
          contradiction
        · obtain ⟨dest,next,floor,door,empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | doorway | locked
          · exact wall floor
          · exact door doorway
          · have eq : dest=fixed := by simpa only [List.mem_singleton] using locked
            exact empty (eq ▸ fixedPresent)
      obtain ⟨phase,atIndex⟩ := valid.2
      have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
      have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
          (phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq]; exact atIndex
      have active : phaseOf soko1_1.initial.holes state<16 :=
        HazardPhaseCountedCorrection.active_of_step _ state within dir t checked
      have spec := pushBoulder_spec _ _ _ _ _ push
      have row := guard_row matrix _ active box member state.player clear.1 different dir behind unblocked result.landing spec.2
      have holesInside : state.holes⊆soko1_1.initial.holes := by
        rw [atIndex.2.1]
        exact (List.drop_sublist phase _).subset
      have unfilled : result.filled=none := by
        rcases spec.1 with stay | fill
        · exact stay.1
        · exact False.elim (row.1 (holesInside fill.2.1))
      have landed : t.landing=some result.landing := by simp only [shape]
      have noFill : t.filled=none := by simpa only [shape] using unfilled
      have outcomeEq := PairStrict11.outcome_stay effect sourceEq landed noFill
      cases outcomeEq
      rcases row.2 with inside | priced
      · exact ⟨result.landing,inside,by simp [update,move,post]⟩
      · have actor : 6≤1+scalar.weight (phaseOf soko1_1.initial.holes state) box result.landing -
           scalar.weight (phaseOf soko1_1.initial.holes state) state.player box := priced
        have bound := OwnedStrict11.owned_stay_bound scalar state dir t valid checked box result.landing
          effect [box] (by simp) (by simpa using present) (by simp) 6 actor
        change 6≤charge NetHack.Soko11Hero315.holeWeight [box] (.push box (.stay result.landing)) +
          value t.state (update [box] (.push box (.stay result.landing))) - value state [box] at bound
        omega
  · have absent : source∉[box] := by simp [same]
    exact ⟨box,member,by simp only [update,move,if_neg absent]⟩

theorem guard_logged {fixed box : Cell} {cells : List Cell}
 (matrix : (List.range 16).all (guardCheck fixed cells) = true)
 {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (fixedPresent : fixed∈state.boulders) (present : box∈state.boulders) (member : box∈cells)
 (stationary : ownPushes [fixed] outcomes=0)
 (cheap : energy state final [box] outcomes<6) :
 ∃ next, next∈cells ∧ endGroup [box] outcomes=[next] := by
 induction logged generalizing box with
 | nil => exact ⟨box,member,rfl⟩
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   let cert := groupCertificate 1
   have nextValid := cert.preserved state dir t valid head
   have actual := step_boulders_nodup _ _ _ _ valid.1 head
   have ownZero : ownPush [fixed] outcome=0 := by
     simp only [ownPushes] at stationary
     omega
   have fixedSame := ownPush_zero_update [fixed] outcome ownZero
   have stationaryTail : ownPushes [fixed] outcomes=0 := by
     simpa only [ownPushes,ownZero,fixedSame,Nat.zero_add] using stationary
   have fixedSubset : [fixed] ⊆ state.boulders := by simpa using fixedPresent
   have nextFixedSubset := GhostSubset.update_subset state t outcome effect [fixed] (by simp) fixedSubset
   have nextFixed : fixed∈t.state.boulders := by
     rw [fixedSame] at nextFixedSubset
     exact nextFixedSubset (by simp)
   have subset : [box] ⊆ state.boulders := by simpa using present
   have nextUnique := GhostSubset.update_unique state t outcome effect actual [box] (by simp) subset
   have nextSubset := GhostSubset.update_subset state t outcome effect [box] (by simp) subset
   have nextSize : (update [box] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
   have nonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextValid
     (update [box] outcome) nextUnique nextSubset nextSize
   have one := cert.row state dir t outcome [box] valid (by simp) subset (by simp) head effect
   change value state [box] ≤ charge NetHack.Soko11Hero315.holeWeight [box] outcome +
     value t.state (update [box] outcome) at one
   have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight
     state t.state final [box] outcome outcomes
   change energy state final [box] (outcome :: outcomes) =
     charge NetHack.Soko11Hero315.holeWeight [box] outcome + value t.state (update [box] outcome) -
       value state [box] + energy t.state final (update [box] outcome) outcomes at decomposition
   change 0≤energy t.state final (update [box] outcome) outcomes at nonnegative
   have firstCheap : charge NetHack.Soko11Hero315.holeWeight [box] outcome +
     value t.state (update [box] outcome) - value state [box]<6 := by omega
   obtain ⟨next,nextMember,updated⟩ := one_step matrix valid head effect fixedPresent present member firstCheap
   have nextPresent : next∈t.state.boulders := nextSubset (by rw [updated]; simp)
   have tailCheap : energy t.state final [next] outcomes<6 := by rw [←updated]; omega
   obtain ⟨last,lastMember,lastGroup⟩ := ih nextValid nextFixed nextPresent nextMember stationaryTail tailCheap
   exact ⟨last,lastMember,by simpa only [endGroup,updated] using lastGroup⟩

theorem guard141 {dirs state pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary : ownPushes [139] outcomes=0)
 (cheap : energy soko1_1.initial state [141] outcomes<6) :
 endGroup [141] outcomes=[141] ∨ endGroup [141] outcomes=[140] := by
 obtain ⟨next,member,group⟩ := guard_logged guards141 first NetHack.SokobanLinearPhases.Map11.initial_good
   (by decide +kernel) (by decide +kernel) (by simp) stationary cheap
 rcases List.mem_cons.mp member with rfl | later
 · exact Or.inl group
 · have same : next=140 := by simpa only [List.mem_singleton] using later
   exact Or.inr (by simpa only [same] using group)

theorem guard193 {dirs state pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (stationary : ownPushes [191] outcomes=0)
 (cheap : energy soko1_1.initial state [193] outcomes<6) :
 endGroup [193] outcomes=[193] ∨ endGroup [193] outcomes=[192] := by
 obtain ⟨next,member,group⟩ := guard_logged guards193 first NetHack.SokobanLinearPhases.Map11.initial_good
   (by decide +kernel) (by decide +kernel) (by simp) stationary cheap
 rcases List.mem_cons.mp member with rfl | later
 · exact Or.inl group
 · have same : next=192 := by simpa only [List.mem_singleton] using later
   exact Or.inr (by simpa only [same] using group)

#print axioms guards141
#print axioms guards193
#print axioms guard_row
#print axioms one_step
#print axioms guard141
#print axioms guard193
end Owner1007.StationaryGuardsSix11
