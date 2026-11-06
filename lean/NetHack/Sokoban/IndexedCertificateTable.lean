/- A transparent finite tree of literal certificate rows. Lookup soundness
needs no trusted sorting/uniqueness generator: every selected entry is
checked at its actual key, and missing entries use a separately checked
default. This is data representation, not a Sokoban-state reduction. -/
namespace NetHack.Sokoban.IndexedCertificateTable

inductive Table (α : Type u) where
  | empty
  | entry (key : Nat) (value : α)
  | fork (cut : Nat) (left right : Table α)

def get (fallback : α) : Table α → Nat → α
  | .empty, _ => fallback
  | .entry key value, index => if index = key then value else fallback
  | .fork cut left right, index =>
      if index < cut then get fallback left index else get fallback right index

def all (test : Nat → α → Bool) : Table α → Bool
  | .empty => true
  | .entry key value => test key value
  | .fork _ left right => all test left && all test right

/-- A check over the literal leaves covers every actual lookup, even if an
external proposer supplied unsorted or duplicate entries. -/
theorem get_checked (fallback : α) (test : Nat → α → Bool)
    (defaultChecked : ∀ index, test index fallback = true) (table : Table α)
    (checked : all test table = true) : ∀ index, test index (get fallback table index) = true := by
  induction table with
  | empty => intro index; exact defaultChecked index
  | entry key value =>
    intro index
    by_cases same : index = key
    · subst index; simpa [get,all] using checked
    · simpa only [get,if_neg same] using defaultChecked index
  | fork cut left right ihLeft ihRight =>
    have parts : all test left = true ∧ all test right = true := Bool.and_eq_true_iff.mp checked
    intro index
    by_cases lower : index < cut
    · simpa only [get,if_pos lower] using ihLeft parts.1 index
    · simpa only [get,if_neg lower] using ihRight parts.2 index

end NetHack.Sokoban.IndexedCertificateTable
