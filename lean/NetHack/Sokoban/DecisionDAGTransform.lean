/- Checked decision-diagram substitutions and physical-cube restrictions.
All tables/readers are untrusted. Their equations are proved by induction on
checked proof-row indices, using the original ordinary-kernel DAG evaluator.
No theorem in this helper asserts a numerical puzzle bound. -/
import NetHack.Sokoban.DecisionDAG

namespace NetHack.Sokoban.DecisionDAGTransform
open DecisionDAG
abbrev Bindings := List (Cell × Bool)

def lookup : Bindings → Cell → Option Bool
  | [], _ => none
  | (cell, bit) :: tail, testCell => if cell = testCell then some bit else lookup tail testCell

def update (p : Pattern) (bindings : Bindings) : Pattern :=
  fun cell => (lookup bindings cell).getD (p cell)

def Satisfies (bindings : Bindings) (p : Pattern) : Prop :=
  ∀ binding ∈ bindings, p binding.1 = binding.2

theorem update_some (p : Pattern) (bindings : Bindings) (cell : Cell) (bit : Bool)
    (found : lookup bindings cell = some bit) : update p bindings cell = bit := by
  simp [update, found]

theorem update_none (p : Pattern) (bindings : Bindings) (cell : Cell)
    (absent : lookup bindings cell = none) : update p bindings cell = p cell := by
  simp [update, absent]

theorem update_of_satisfies (p : Pattern) (bindings : Bindings)
    (satisfied : Satisfies bindings p) : update p bindings = p := by
  funext cell
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head.1 = cell
    · have selected := satisfied head (by simp)
      simpa [update, lookup, same] using selected.symm
    · have rest : Satisfies tail p := fun binding member => satisfied binding (List.mem_cons_of_mem head member)
      simpa [update, lookup, same] using ih rest

def Supported (read : Nat → Node) (support : List Cell) : Prop :=
  ∀ root cell low high, read root = .branch cell low high → cell ∈ support

theorem eval_congr (read : Nat → Node) (support : List Cell) (supported : Supported read support)
    (p q : Pattern) (agree : ∀ cell ∈ support, p cell = q cell) (root : Nat) :
    eval read p root = eval read q root := by
  induction root using Nat.strongRecOn with
  | ind root ih =>
    cases code : read root with
    | literal value => rw [eval_literal code p, eval_literal code q]
    | branch cell low high =>
      by_cases edges : low < root ∧ high < root
      · rw [eval_branch code edges p, eval_branch code edges q, agree cell (supported root cell low high code)]
        cases q cell <;> first | exact ih low edges.1 | exact ih high edges.2
      · rw [eval, code, eval, code]
        simp only [dif_neg edges]

theorem eval_range (read : Nat → Node) (lower upper : Int) (zero : lower ≤ 0 ∧ 0 ≤ upper)
    (literals : ∀ root value, read root = .literal value → lower ≤ value ∧ value ≤ upper)
    (p : Pattern) (root : Nat) : lower ≤ eval read p root ∧ eval read p root ≤ upper := by
  induction root using Nat.strongRecOn with
  | ind root ih =>
    cases code : read root with
    | literal value => rw [eval_literal code p]; exact literals root value code
    | branch cell low high =>
      by_cases edges : low < root ∧ high < root
      · rw [eval_branch code edges p]
        cases p cell <;> first | exact ih low edges.1 | exact ih high edges.2
      · rw [eval, code]
        simpa only [dif_neg edges] using zero

theorem lookup_none_of_absent (bindings : Bindings) (cell : Cell)
    (absent : ∀ binding ∈ bindings, binding.1 ≠ cell) : lookup bindings cell = none := by
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
    have different := absent head (by simp)
    have rest := ih (fun binding member => absent binding (List.mem_cons_of_mem head member))
    simp only [lookup, if_neg different, rest]

theorem eval_update_outside (read : Nat → Node) (support : List Cell) (supported : Supported read support)
    (p : Pattern) (bindings : Bindings) (disjoint : ∀ binding ∈ bindings, binding.1 ∉ support)
    (root : Nat) : eval read p root = eval read (update p bindings) root := by
  apply eval_congr read support supported p (update p bindings)
  intro cell member
  have absent : lookup bindings cell = none := lookup_none_of_absent bindings cell (by
    intro binding present same
    exact disjoint binding present (same ▸ member))
  exact (update_none p bindings cell absent).symm

def Above (read : Nat → Node) (root threshold : Nat) : Prop :=
  ∀ cell low high, read root = .branch cell low high → threshold ≤ cell

def Ordered (read : Nat → Node) : Prop :=
  ∀ root cell low high, read root = .branch cell low high →
    Above read low (cell + 1) ∧ Above read high (cell + 1)

theorem eval_congr_above (read : Nat → Node) (support : List Cell)
    (supported : Supported read support) (ordered : Ordered read) (threshold : Nat)
    (p q : Pattern) (agree : ∀ cell ∈ support, threshold ≤ cell → p cell = q cell)
    (root : Nat) (above : Above read root threshold) : eval read p root = eval read q root := by
  induction root using Nat.strongRecOn with
  | ind root ih =>
    cases code : read root with
    | literal value => rw [eval_literal code p, eval_literal code q]
    | branch cell low high =>
      by_cases edges : low < root ∧ high < root
      · have level := above cell low high code
        have children := ordered root cell low high code
        have lower : Above read low threshold := by
          intro c l h childCode
          have bound := children.1 c l h childCode
          omega
        have upper : Above read high threshold := by
          intro c l h childCode
          have bound := children.2 c l h childCode
          omega
        rw [eval_branch code edges p, eval_branch code edges q,
          agree cell (supported root cell low high code) level]
        cases q cell <;> first | exact ih low edges.1 lower | exact ih high edges.2 upper
      · rw [eval, code, eval, code]
        simp only [dif_neg edges]

theorem eval_update_prefix (read : Nat → Node) (support : List Cell)
    (supported : Supported read support) (ordered : Ordered read) (threshold : Nat)
    (p : Pattern) (bindings : Bindings)
    (disjoint : ∀ binding ∈ bindings, binding.1 ∉ support ∨ binding.1 < threshold)
    (root : Nat) (above : Above read root threshold) :
    eval read p root = eval read (update p bindings) root := by
  apply eval_congr_above read support supported ordered threshold p (update p bindings) _ root above
  intro cell member lower
  have absent : lookup bindings cell = none := lookup_none_of_absent bindings cell (by
    intro binding present same
    rcases disjoint binding present with outside | earlier
    · exact outside (same ▸ member)
    · rw [same] at earlier
      exact (Nat.not_lt_of_ge lower) earlier)
  exact (update_none p bindings cell absent).symm

def aboveCheck (read : Nat → Node) (root threshold : Nat) : Bool :=
  match read root with
  | .literal _ => true
  | .branch cell _ _ => decide (threshold ≤ cell)

theorem aboveCheck_sound (read : Nat → Node) (root threshold : Nat)
    (checked : aboveCheck read root threshold = true) : Above read root threshold := by
  intro cell low high code
  simpa only [aboveCheck, code, decide_eq_true_eq] using checked

def orderCheck (read : Nat → Node) (root : Nat) : Bool :=
  match read root with
  | .literal _ => true
  | .branch cell low high => aboveCheck read low (cell + 1) && aboveCheck read high (cell + 1)

theorem orderCheck_sound (read : Nat → Node)
    (checked : ∀ root, orderCheck read root = true) : Ordered read := by
  intro root cell low high code
  have row := checked root
  simp only [orderCheck, code, Bool.and_eq_true_iff] at row
  exact ⟨aboveCheck_sound read low _ row.1, aboveCheck_sound read high _ row.2⟩

def joinCheck (read : Nat → Node) (output cell low high : Nat) : Bool :=
  decide (output = low ∧ output = high) ||
    match read output with
    | .literal _ => false
    | .branch testCell left right => decide
      (testCell = cell ∧ left = low ∧ right = high ∧ low < output ∧ high < output)

theorem join_sound (read : Nat → Node) (output cell low high : Nat)
    (checked : joinCheck read output cell low high = true) (p : Pattern) :
    eval read p output = if p cell then eval read p high else eval read p low := by
  rcases Bool.or_eq_true_iff.mp checked with same | branch
  · have eqs : output = low ∧ output = high := of_decide_eq_true same
    rw [← eqs.1, ← eqs.2]
    cases p cell <;> rfl
  · cases code : read output with
    | literal value => simp [code] at branch
    | branch testCell left right =>
      have facts : testCell = cell ∧ left = low ∧ right = high ∧ low < output ∧ high < output := by
        simpa only [code, decide_eq_true_eq] using branch
      rcases facts with ⟨rfl, rfl, rfl, lower, upper⟩
      exact eval_branch code ⟨lower, upper⟩ p

structure UpdateClaim where
  bindings : Bindings
  original : Nat
  output : Nat
  deriving DecidableEq, Repr

def UpdateHolds (read : Nat → Node) (claim : UpdateClaim) : Prop :=
  ∀ p, eval read p claim.output = eval read (update p claim.bindings) claim.original

inductive UpdateRule where
  | literal
  | selected (child : Nat)
  | branch (low high : Nat)
  | independent
  | independentPrefix
  deriving DecidableEq, Repr

structure UpdateRow where
  claim : UpdateClaim
  rule : UpdateRule
  deriving DecidableEq, Repr

def updateCheck (read : Nat → Node) (support : List Cell) (rows : Nat → UpdateRow) (index : Nat) : Bool :=
  let claim := (rows index).claim
  match (rows index).rule, read claim.original with
  | .independentPrefix, .branch cell _ _ => decide (claim.output = claim.original ∧
      ∀ binding ∈ claim.bindings, binding.1 ∉ support ∨ binding.1 < cell)
  | .independent, _ => decide (claim.output = claim.original ∧
      ∀ binding ∈ claim.bindings, binding.1 ∉ support)
  | .literal, .literal value => decide (read claim.output = .literal value)
  | .selected child, .branch cell low high =>
    match lookup claim.bindings cell with
    | none => false
    | some bit => decide (low < claim.original ∧ high < claim.original ∧ child < index ∧
        (rows child).claim.bindings = claim.bindings ∧
        (rows child).claim.original = (if bit then high else low) ∧
        (rows child).claim.output = claim.output)
  | .branch left right, .branch cell low high =>
    decide (low < claim.original ∧ high < claim.original ∧ lookup claim.bindings cell = none ∧
      left < index ∧ right < index ∧
      (rows left).claim = ⟨claim.bindings, low, (rows left).claim.output⟩ ∧
      (rows right).claim = ⟨claim.bindings, high, (rows right).claim.output⟩) &&
      joinCheck read claim.output cell (rows left).claim.output (rows right).claim.output
  | _, _ => false

theorem updates_checked_sound (read : Nat → Node) (support : List Cell) (supported : Supported read support)
    (ordered : Ordered read)
    (rows : Nat → UpdateRow) (count : Nat)
    (checked : ∀ index, index < count → updateCheck read support rows index = true)
    (index : Nat) (inside : index < count) : UpdateHolds read (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have checkedRow := checked index inside
    intro p
    cases rule : (rows index).rule with
    | independentPrefix =>
      cases code : read (rows index).claim.original with
      | literal value => simp [updateCheck, rule, code] at checkedRow
      | branch cell low high =>
        have data : (rows index).claim.output = (rows index).claim.original ∧
            ∀ binding ∈ (rows index).claim.bindings, binding.1 ∉ support ∨ binding.1 < cell := by
          simpa only [updateCheck, rule, code, decide_eq_true_eq] using checkedRow
        rw [data.1]
        apply eval_update_prefix read support supported ordered cell p _ data.2
        intro c l h other
        have same : c = cell := by have := code.symm.trans other; cases this; rfl
        omega
    | independent =>
      have data : (rows index).claim.output = (rows index).claim.original ∧
          ∀ binding ∈ (rows index).claim.bindings, binding.1 ∉ support := by
        simpa only [updateCheck, rule, decide_eq_true_eq] using checkedRow
      rw [data.1]
      exact eval_update_outside read support supported p _ data.2 _
    | literal =>
      cases code : read (rows index).claim.original with
      | branch cell low high => simp [updateCheck, rule, code] at checkedRow
      | literal value =>
        have output : read (rows index).claim.output = .literal value := by
          simpa only [updateCheck, rule, code, decide_eq_true_eq] using checkedRow
        rw [eval_literal output p, eval_literal code (update p (rows index).claim.bindings)]
    | selected child =>
      cases code : read (rows index).claim.original with
      | literal value => simp [updateCheck, rule, code] at checkedRow
      | branch cell low high =>
        cases selected : lookup (rows index).claim.bindings cell with
        | none => simp [updateCheck, rule, code, selected] at checkedRow
        | some bit =>
          have data : low < (rows index).claim.original ∧ high < (rows index).claim.original ∧ child < index ∧
              (rows child).claim.bindings = (rows index).claim.bindings ∧
              (rows child).claim.original = (if bit then high else low) ∧
              (rows child).claim.output = (rows index).claim.output := by
            simpa only [updateCheck, rule, code, selected, decide_eq_true_eq] using checkedRow
          have childProof := ih child data.2.2.1 (Nat.lt_trans data.2.2.1 inside) p
          rw [data.2.2.2.1, data.2.2.2.2.1, data.2.2.2.2.2] at childProof
          rw [eval_branch code ⟨data.1, data.2.1⟩ (update p (rows index).claim.bindings),
            update_some p _ cell bit selected]
          cases bit <;> simpa using childProof
    | branch left right =>
      cases code : read (rows index).claim.original with
      | literal value => simp [updateCheck, rule, code] at checkedRow
      | branch cell low high =>
        have rowBody := checkedRow
        simp only [updateCheck, rule, code] at rowBody
        have combined := Bool.and_eq_true_iff.mp rowBody
        have data : low < (rows index).claim.original ∧ high < (rows index).claim.original ∧
            lookup (rows index).claim.bindings cell = none ∧ left < index ∧ right < index ∧
            (rows left).claim = ⟨(rows index).claim.bindings, low, (rows left).claim.output⟩ ∧
            (rows right).claim = ⟨(rows index).claim.bindings, high, (rows right).claim.output⟩ := by
          simpa only [updateCheck, rule, code, decide_eq_true_eq] using combined.1
        have lower := ih left data.2.2.2.1 (Nat.lt_trans data.2.2.2.1 inside) p
        have upper := ih right data.2.2.2.2.1 (Nat.lt_trans data.2.2.2.2.1 inside) p
        have loBind := congrArg UpdateClaim.bindings data.2.2.2.2.2.1
        have loRoot := congrArg UpdateClaim.original data.2.2.2.2.2.1
        have hiBind := congrArg UpdateClaim.bindings data.2.2.2.2.2.2
        have hiRoot := congrArg UpdateClaim.original data.2.2.2.2.2.2
        rw [loBind, loRoot] at lower
        rw [hiBind, hiRoot] at upper
        rw [join_sound read _ cell _ _ (by simpa only [updateCheck, rule, code] using combined.2) p,
          eval_branch code ⟨data.1, data.2.1⟩ (update p (rows index).claim.bindings),
          update_none p _ cell data.2.2.1, lower, upper]

def RestrictionHolds (read : Nat → Node) (claim : UpdateClaim) : Prop :=
  ∀ p, Satisfies claim.bindings p → eval read p claim.output = eval read p claim.original

inductive RestrictionRule where
  | same
  | selected (bit : Bool) (child : Nat)
  | branch (low high : Nat)
  deriving DecidableEq, Repr

structure RestrictionRow where
  claim : UpdateClaim
  rule : RestrictionRule
  deriving DecidableEq, Repr

def restrictionCheck (read : Nat → Node) (rows : Nat → RestrictionRow) (index : Nat) : Bool :=
  let claim := (rows index).claim
  match (rows index).rule with
  | .same => decide (claim.output = claim.original)
  | .selected bit child =>
    match read claim.original with
    | .literal _ => false
    | .branch cell low high => decide
      (low < claim.original ∧ high < claim.original ∧ child < index ∧
        (cell, bit) ∈ claim.bindings ∧ (rows child).claim.bindings ⊆ claim.bindings ∧
        (rows child).claim.original = (if bit then high else low) ∧
        (rows child).claim.output = claim.output)
  | .branch left right =>
    match read claim.original with
    | .literal _ => false
    | .branch cell low high => decide
      (low < claim.original ∧ high < claim.original ∧ left < index ∧ right < index ∧
        (rows left).claim.original = low ∧ (rows right).claim.original = high ∧
        (rows left).claim.bindings ⊆ claim.bindings ∧ (rows right).claim.bindings ⊆ claim.bindings) &&
      joinCheck read claim.output cell (rows left).claim.output (rows right).claim.output

theorem restrictions_checked_sound (read : Nat → Node) (rows : Nat → RestrictionRow) (count : Nat)
    (checked : ∀ index, index < count → restrictionCheck read rows index = true)
    (index : Nat) (inside : index < count) : RestrictionHolds read (rows index).claim := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    have checkedRow := checked index inside
    intro p satisfied
    cases rule : (rows index).rule with
    | same =>
      have same : (rows index).claim.output = (rows index).claim.original := by
        simpa only [restrictionCheck, rule, decide_eq_true_eq] using checkedRow
      rw [same]
    | selected bit child =>
      cases code : read (rows index).claim.original with
      | literal value => simp [restrictionCheck, rule, code] at checkedRow
      | branch cell low high =>
        have data : low < (rows index).claim.original ∧ high < (rows index).claim.original ∧ child < index ∧
            (cell, bit) ∈ (rows index).claim.bindings ∧
            (rows child).claim.bindings ⊆ (rows index).claim.bindings ∧
            (rows child).claim.original = (if bit then high else low) ∧
            (rows child).claim.output = (rows index).claim.output := by
          simpa only [restrictionCheck, rule, code, decide_eq_true_eq] using checkedRow
        rcases data with ⟨loEdge, hiEdge, childEarlier, selected, subset, original, output⟩
        have childProof := ih child childEarlier (Nat.lt_trans childEarlier inside) p
          (fun binding member => satisfied binding (subset member))
        rw [original, output] at childProof
        rw [eval_branch code ⟨loEdge, hiEdge⟩ p, satisfied (cell, bit) selected]
        cases bit <;> simpa using childProof
    | branch left right =>
      cases code : read (rows index).claim.original with
      | literal value => simp [restrictionCheck, rule, code] at checkedRow
      | branch cell low high =>
        have rowBody := checkedRow
        simp only [restrictionCheck, rule, code] at rowBody
        have combined := Bool.and_eq_true_iff.mp rowBody
        have data : low < (rows index).claim.original ∧ high < (rows index).claim.original ∧
            left < index ∧ right < index ∧ (rows left).claim.original = low ∧
            (rows right).claim.original = high ∧
            (rows left).claim.bindings ⊆ (rows index).claim.bindings ∧
            (rows right).claim.bindings ⊆ (rows index).claim.bindings := of_decide_eq_true combined.1
        rcases data with ⟨loEdge, hiEdge, leftEarlier, rightEarlier, leftRoot, rightRoot, leftSub, rightSub⟩
        have lower := ih left leftEarlier (Nat.lt_trans leftEarlier inside) p
          (fun binding member => satisfied binding (leftSub member))
        have upper := ih right rightEarlier (Nat.lt_trans rightEarlier inside) p
          (fun binding member => satisfied binding (rightSub member))
        rw [leftRoot] at lower
        rw [rightRoot] at upper
        rw [join_sound read _ cell _ _ combined.2 p, eval_branch code ⟨loEdge, hiEdge⟩ p,
          lower, upper]

end NetHack.Sokoban.DecisionDAGTransform
