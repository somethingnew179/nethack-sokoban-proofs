/- Sound projection of actual boulder-list changes to the finite nine-cell
certificate. Duplicate input boulders are handled by monotone containment,
not by silently assuming that erasing one occurrence clears its cell. -/
import NetHack.Sokoban.PatternBase
import NetHack.Sokoban.NonlinearFacts

namespace NetHack.Sokoban.PatternProjection
open PatternCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem known_ofBoxes_eq (boxes : List Cell) (cell : Cell) :
    known (ofBoxes boxes) cell = (support.contains cell && boxes.contains cell) := by
  by_cases h35 : cell = 35 <;> simp_all [known, ofBoxes, support]
  by_cases h36 : cell = 36 <;> simp_all [known, ofBoxes, support]
  by_cases h51 : cell = 51 <;> simp_all [known, ofBoxes, support]
  by_cases h52 : cell = 52 <;> simp_all [known, ofBoxes, support]
  by_cases h37 : cell = 37 <;> simp_all [known, ofBoxes, support]
  by_cases h127 : cell = 127 <;> simp_all [known, ofBoxes, support]
  by_cases h128 : cell = 128 <;> simp_all [known, ofBoxes, support]
  by_cases h129 : cell = 129 <;> simp_all [known, ofBoxes, support]
  by_cases h130 : cell = 130 <;> simp_all [known, ofBoxes, support]

theorem known_ofBoxes_true (boxes : List Cell) (cell : Cell) :
    known (ofBoxes boxes) cell = true ↔ cell ∈ support ∧ cell ∈ boxes := by
  simp [known_ofBoxes_eq]

theorem known_erase_eq (pattern : Nine) (source cell : Cell) :
    known (erase pattern source) cell = (known pattern cell && decide (source ≠ cell)) := by
  by_cases h35 : cell = 35 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h36 : cell = 36 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h51 : cell = 51 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h52 : cell = 52 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h37 : cell = 37 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h127 : cell = 127 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h128 : cell = 128 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h129 : cell = 129 <;> simp_all [known, PatternCertificate.erase, support]
  by_cases h130 : cell = 130 <;> simp_all [known, PatternCertificate.erase, support]

theorem known_insert_eq (pattern : Nine) (destination cell : Cell) :
    known (insert pattern destination) cell =
      (known pattern cell || (support.contains cell && decide (destination = cell))) := by
  by_cases h35 : cell = 35 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h36 : cell = 36 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h51 : cell = 51 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h52 : cell = 52 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h37 : cell = 37 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h127 : cell = 127 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h128 : cell = 128 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h129 : cell = 129 <;> simp_all [known, PatternCertificate.insert, support]
  by_cases h130 : cell = 130 <;> simp_all [known, PatternCertificate.insert, support]

theorem erase_project_subset (boxes : List Cell) (source : Cell) :
    Subset (erase (ofBoxes boxes) source) (ofBoxes (boxes.erase source)) := by
  intro cell member
  rw [known_erase_eq] at member
  rcases Bool.and_eq_true_iff.mp member with ⟨old, different⟩
  rcases (known_ofBoxes_true boxes cell).mp old with ⟨supported, present⟩
  apply (known_ofBoxes_true (boxes.erase source) cell).mpr
  exact ⟨supported, (List.mem_erase_of_ne (Ne.symm (of_decide_eq_true different))).mpr present⟩

theorem insert_subset (left right : Nine) (included : Subset left right) (destination : Cell) :
    Subset (insert left destination) (insert right destination) := by
  intro cell member
  rw [known_insert_eq] at member ⊢
  rcases Bool.or_eq_true_iff.mp member with old | inserted
  · exact Bool.or_eq_true_iff.mpr (Or.inl (included cell old))
  · exact Bool.or_eq_true_iff.mpr (Or.inr inserted)

theorem insert_project_eq (boxes : List Cell) (destination : Cell) :
    insert (ofBoxes boxes) destination = ofBoxes (destination :: boxes) := by
  simp [PatternCertificate.insert, ofBoxes, List.contains_cons, Bool.or_comm, beq_iff_eq, eq_comm]

theorem occupied_ofBoxes (boxes : List Cell) :
    occupied (ofBoxes boxes) = NonlinearFacts.occupied support boxes := by
  unfold occupied NonlinearFacts.occupied
  apply List.filter_congr
  intro cell member
  simp [known_ofBoxes_eq, member]

private theorem and_mono {a b c d : Bool}
    (left : a = true → c = true) (right : b = true → d = true) :
    (a && b) = true → (c && d) = true := by
  intro present
  rcases Bool.and_eq_true_iff.mp present with ⟨ha, hb⟩
  exact Bool.and_eq_true_iff.mpr ⟨left ha, right hb⟩

private theorem or_mono {a b c d : Bool}
    (left : a = true → c = true) (right : b = true → d = true) :
    (a || b) = true → (c || d) = true := by
  intro present
  rcases Bool.or_eq_true_iff.mp present with ha | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl (left ha))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (right hb))

private theorem one_mono {a b : Bool} (included : a = true → b = true) : one a ≤ one b := by
  cases a <;> cases b <;> simp_all [one]

theorem bonus_mono (left right : Nine) (included : Subset left right) : bonus left ≤ bonus right := by
  have ha : left.a = true → right.a = true := by
    intro present
    have result := included 35 (by simpa [known] using present)
    simpa [known] using result
  have hb : left.b = true → right.b = true := by
    intro present
    have result := included 36 (by simpa [known] using present)
    simpa [known] using result
  have hc : left.c = true → right.c = true := by
    intro present
    have result := included 51 (by simpa [known] using present)
    simpa [known] using result
  have hd : left.d = true → right.d = true := by
    intro present
    have result := included 52 (by simpa [known] using present)
    simpa [known] using result
  have he : left.e = true → right.e = true := by
    intro present
    have result := included 37 (by simpa [known] using present)
    simpa [known] using result
  have hf : left.f = true → right.f = true := by
    intro present
    have result := included 127 (by simpa [known] using present)
    simpa [known] using result
  have hg : left.g = true → right.g = true := by
    intro present
    have result := included 128 (by simpa [known] using present)
    simpa [known] using result
  have hh : left.h = true → right.h = true := by
    intro present
    have result := included 129 (by simpa [known] using present)
    simpa [known] using result
  have hi : left.i = true → right.i = true := by
    intro present
    have result := included 130 (by simpa [known] using present)
    simpa [known] using result
  have top := one_mono (and_mono (and_mono (and_mono ha hb) hc) (or_mono hd he))
  have first := one_mono (and_mono hf hg)
  have second := one_mono (and_mono hh hi)
  change one (gate left) ≤ one (gate right) at top
  change one (leftPair left) ≤ one (leftPair right) at first
  change one (rightPair left) ≤ one (rightPair right) at second
  unfold bonus
  omega

theorem known_support (pattern : Nine) (cell : Cell) (present : known pattern cell = true) :
    cell ∈ support := by
  by_cases h35 : cell = 35 <;> simp_all [known, support]
  by_cases h36 : cell = 36 <;> simp_all [known, support]
  by_cases h51 : cell = 51 <;> simp_all [known, support]
  by_cases h52 : cell = 52 <;> simp_all [known, support]
  by_cases h37 : cell = 37 <;> simp_all [known, support]
  by_cases h127 : cell = 127 <;> simp_all [known, support]
  by_cases h128 : cell = 128 <;> simp_all [known, support]
  by_cases h129 : cell = 129 <;> simp_all [known, support]

theorem outside_erase_subset (pattern : Nine) (source : Cell) (outside : source ∉ support) :
    Subset pattern (PatternCertificate.erase pattern source) := by
  intro cell present
  rw [known_erase_eq]
  have supported := known_support pattern cell present
  have different : source ≠ cell := by
    intro same
    exact outside (by simpa [same] using supported)
  exact Bool.and_eq_true_iff.mpr ⟨present, by simpa only [decide_eq_true_eq] using different⟩

theorem insert_superset (pattern : Nine) (destination : Cell) :
    Subset pattern (PatternCertificate.insert pattern destination) := by
  intro cell present
  rw [known_insert_eq]
  exact Bool.or_eq_true_iff.mpr (Or.inl present)

/-- Outside the nine tracked cells, erasing a boulder cannot decrease the
bonus. This justifies checking only the active finite source rows. -/
theorem outside_bonus_bounds (pattern : Nine) (source landing : Cell) (outside : source ∉ support) :
    bonus pattern ≤ bonus (PatternCertificate.erase pattern source) ∧
    bonus pattern ≤ bonus (PatternCertificate.insert (PatternCertificate.erase pattern source) landing) := by
  have erased := bonus_mono pattern (PatternCertificate.erase pattern source)
    (outside_erase_subset pattern source outside)
  have inserted := bonus_mono (PatternCertificate.erase pattern source)
    (PatternCertificate.insert (PatternCertificate.erase pattern source) landing)
    (insert_superset (PatternCertificate.erase pattern source) landing)
  exact ⟨erased, Int.le_trans erased inserted⟩

/-- Exact finite numerical obligations, discharged by PatternCertificate's
independent kernel-checked mask/edge table. Kept as an explicit premise so
this semantic projection can be checked independently of table computation. -/
def LocalBounds : Prop :=
  ∀ (pattern : Nine) (player source : Cell) (direction : Dir) (landing : Cell),
    player ∈ soko4_2.board.floor → source ∈ soko4_2.board.floor →
    advance soko4_2.board player direction = some source →
    landing ∈ pushTargets soko4_2.board source direction →
    known pattern player = false →
    (∀ first, advance soko4_2.board source direction = some first → known pattern first = false) →
    (landing = source ∨ known pattern landing = false) →
    (bonus pattern ≤ (1 + Generated.soko4_2Potential.boulder landing - Generated.soko4_2Potential.boulder source) +
      bonus (PatternCertificate.insert (PatternCertificate.erase pattern source) landing)) ∧
    (bonus pattern ≤ (1 - Generated.soko4_2Potential.boulder source - Generated.soko4_2Potential.hole landing) +
      bonus (PatternCertificate.erase pattern source))

/-- Transfer a finite pattern delta to the actual boulder-list delta. Extra
copies left by List.erase only increase the actual monotone occupancy bonus. -/
theorem bonus_push_bounds (numeric : LocalBounds) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (playerFloor : state.player ∈ soko4_2.board.floor)
    (playerClear : state.player ∉ state.boulders)
    (sourceFloor : source ∈ soko4_2.board.floor)
    (adjacent : advance soko4_2.board state.player direction = some source)
    (checked : pushBoulder soko4_2.board state source direction = some result) :
    (bonusOfBoxes state.boulders ≤
      (1 + Generated.soko4_2Potential.boulder result.landing - Generated.soko4_2Potential.boulder source) +
        bonusOfBoxes (result.landing :: state.boulders.erase source)) ∧
    (bonusOfBoxes state.boulders ≤
      (1 - Generated.soko4_2Potential.boulder source - Generated.soko4_2Potential.hole result.landing) +
        bonusOfBoxes (state.boulders.erase source)) := by
  have spec := pushBoulder_spec soko4_2.board state source direction result checked
  have playerFalse : known (ofBoxes state.boulders) state.player = false := by
    simp [known_ofBoxes_eq, playerClear]
  have firstFalse : ∀ first, advance soko4_2.board source direction = some first →
      known (ofBoxes state.boulders) first = false := by
    rcases NonlinearFacts.pushBoulder_first_clear soko4_2.board state source direction result checked with
      ⟨destination, firstEq, _, _, clear⟩
    intro first adjacentFirst
    have same : first = destination := Option.some.inj (adjacentFirst.symm.trans firstEq)
    subst first
    simp [known_ofBoxes_eq, clear]
  have landingFalse : result.landing = source ∨ known (ofBoxes state.boulders) result.landing = false := by
    rcases NonlinearFacts.pushBoulder_landing_old_clear_or_source soko4_2.board state source direction result checked with same | clear
    · exact Or.inl same
    · exact Or.inr (by simp [known_ofBoxes_eq, clear])
  have bounds := numeric (ofBoxes state.boulders) state.player source direction result.landing
    playerFloor sourceFloor adjacent spec.2 playerFalse firstFalse landingFalse
  have erasedMono := bonus_mono _ _ (erase_project_subset state.boulders source)
  have insertedMono := bonus_mono _ _ (insert_subset _ _
    (erase_project_subset state.boulders source) result.landing)
  rw [insert_project_eq] at insertedMono
  unfold bonusOfBoxes
  constructor <;> omega

end NetHack.Sokoban.PatternProjection
