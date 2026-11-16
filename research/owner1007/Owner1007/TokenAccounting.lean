import Owner1007.FrozenDebt32
import NetHack.Sokoban.GhostSubset
import NetHack.Sokoban.GhostShadow
import NetHack.Sokoban.GhostOracleFacts

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection

/-- A log records effects of ORIGINAL steps. It adds bookkeeping only;
every original Trace with distinct stones has such a log. -/
inductive Logged (board : Board) : State → List Dir → State → Nat → Nat → List Outcome → Prop where
  | nil (state) : Logged board state [] state 0 0 []
  | cons {state dir t rest final pushes moves outcome outcomes}
      (checked : step board state dir = some t)
      (effect : Matches state t outcome)
      (tail : Logged board t.state rest final pushes moves outcomes) :
      Logged board state (dir :: rest) final (t.pushCost + pushes) (1 + moves) (outcome :: outcomes)

theorem Logged.trace {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes) :
    Trace board initial dirs final pushes moves := by
  induction logged with
  | nil => exact .nil _
  | cons head effect tail ih => exact .cons head ih

theorem log_exists {board initial dirs final pushes moves}
    (trace : Trace board initial dirs final pushes moves) (unique : initial.boulders.Nodup) :
    ∃ outcomes, Logged board initial dirs final pushes moves outcomes := by
  induction trace with
  | nil => exact ⟨[], .nil _⟩
  | cons head tail ih =>
    obtain ⟨outcome, _, effect⟩ := stepOracle_covers _ _ unique _ _ head
    obtain ⟨outcomes, rest⟩ := ih (step_boulders_nodup _ _ _ _ unique head)
    exact ⟨outcome :: outcomes, .cons head effect rest⟩

def endGroup (group : List Cell) : List Outcome → List Cell
  | [] => group
  | outcome :: rest => endGroup (update group outcome) rest

def ownSlack (potential : Potential) (group : List Cell) : List Outcome → Int
  | [] => 0
  | outcome :: rest => slack potential (projectedOutcome group outcome) +
      ownSlack potential (update group outcome) rest

def ownPush (group : List Cell) : Outcome → Nat
  | .walk _ => 0
  | .push source _ => if source ∈ group then 1 else 0

def ownPushes (group : List Cell) : List Outcome → Nat
  | [] => 0
  | outcome :: rest => ownPush group outcome + ownPushes (update group outcome) rest

def ownCredit (potential : Potential) (group : List Cell) : Outcome → Int
  | .push source (.fill hole) => if source ∈ group then potential.hole hole else 0
  | _ => 0

def ownCredits (potential : Potential) (group : List Cell) : List Outcome → Int
  | [] => 0
  | outcome :: rest => ownCredit potential group outcome + ownCredits potential (update group outcome) rest

theorem one_step_ledger (potential : Potential) (group : List Cell) (outcome : Outcome) :
    debtOf potential group + Int.ofNat (ownPush group outcome) =
      slack potential (projectedOutcome group outcome) +
        debtOf potential (update group outcome) + ownCredit potential group outcome := by
  cases outcome with
  | walk target => simp [ownPush, projectedOutcome, slack, update, ownCredit]
  | push source result =>
    by_cases owner : source ∈ group
    · have erased := weightSum_erase (fun c => -potential.boulder c) group source owner
      change debtOf potential group = -potential.boulder source +
        debtOf potential (group.erase source) at erased
      cases result <;>
        simp only [ownPush, ownCredit, projectedOutcome, update, move, if_pos owner, post,
          slack, Int.ofNat_eq_natCast, Int.natCast_one]
      · change debtOf potential group + 1 =
          (1 + potential.boulder _ - potential.boulder source) +
            (-potential.boulder _ + debtOf potential (group.erase source)) + 0
        omega
      · omega
    · cases result <;>
        simp [ownPush, ownCredit, projectedOutcome, update, move, owner, slack]

/-- If a token survives, the consumption credit vanishes: its energy is
initial debt plus number of its own pushes. No path-finding assumption occurs. -/
theorem group_ledger (potential : Potential) (group : List Cell) (outcomes : List Outcome) :
    debtOf potential group + Int.ofNat (ownPushes group outcomes) =
      ownSlack potential group outcomes + debtOf potential (endGroup group outcomes) +
        ownCredits potential group outcomes := by
  induction outcomes generalizing group with
  | nil => simp [ownPushes, ownSlack, endGroup, ownCredits]
  | cons outcome rest ih =>
    have one := one_step_ledger potential group outcome
    have tail := ih (update group outcome)
    simp only [ownPushes, ownSlack, endGroup, ownCredits, Int.ofNat_eq_natCast, Int.natCast_add] at *
    omega

theorem Logged.end_subset {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (initialUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) :
    (endGroup group outcomes).Nodup ∧ endGroup group outcomes ⊆ final.boulders := by
  induction logged generalizing group with
  | nil => exact ⟨unique, subset⟩
  | cons head effect tail ih =>
    have nextUnique := step_boulders_nodup _ _ _ _ initialUnique head
    exact ih nextUnique (update group _) (GhostSubset.update_unique _ _ _ effect nextUnique group unique subset)
      (GhostSubset.update_subset _ _ _ effect group unique subset)

theorem logged_step_slack_nonnegative {board state dir t outcome}
    {potential : Potential} (valid : Valid board potential)
    (checked : step board state dir = some t) (effect : Matches state t outcome) :
    0 ≤ slack potential outcome := by
  have delta := matches_delta potential state t outcome effect
  have bound := valid.stepBound state dir t checked
  omega

theorem projected_slack_nonnegative (potential : Potential) (group : List Cell) (outcome : Outcome)
    (nonnegative : 0 ≤ slack potential outcome) : 0 ≤ slack potential (projectedOutcome group outcome) := by
  cases outcome with
  | walk target => exact nonnegative
  | push source result =>
    by_cases owner : source ∈ group
    · simpa only [projectedOutcome, if_pos owner] using nonnegative
    · simp only [projectedOutcome, if_neg owner, slack]; omega

theorem Logged.ownSlack_nonnegative {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential) (group : List Cell) :
    0 ≤ ownSlack potential group outcomes := by
  induction logged generalizing group with
  | nil => exact Int.le_refl 0
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have one := projected_slack_nonnegative potential group outcome (logged_step_slack_nonnegative valid head effect)
    have rest := ih (update group outcome)
    change 0 ≤ _ + _
    omega

#print axioms group_ledger
#print axioms log_exists
end Owner1007.TokenAccounting
