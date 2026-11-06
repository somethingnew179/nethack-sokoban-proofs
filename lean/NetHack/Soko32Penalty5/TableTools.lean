/- Finite-index assembly and default-row coverage. No assumed sorting or
search-table completeness is required for the upper-key default theorem. -/
import NetHack.Sokoban.IndexedCertificateTable
import Init.Data.List.Nat.Range
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban.IndexedCertificateTable

theorem range_join (test : Nat → Bool) (start first second : Nat)
    (left : (List.range' start first).all test = true)
    (right : (List.range' (start+first) second).all test = true) :
    (List.range' start (first+second)).all test = true := by
  rw [←List.range'_append_1,List.all_append,left,right]
  rfl

theorem get_above (fallback : α) (table : Table α) (bound index : Nat)
    (keys : all (fun key _ => decide (key < bound)) table = true) (above : bound ≤ index) :
    get fallback table index = fallback := by
  induction table with
  | empty => rfl
  | entry key value =>
    have smaller : key < bound := of_decide_eq_true keys
    have different : index ≠ key := by omega
    simp only [NetHack.Sokoban.IndexedCertificateTable.get,if_neg different]
  | fork cut left right ihLeft ihRight =>
    have parts := Bool.and_eq_true_iff.mp keys
    unfold NetHack.Sokoban.IndexedCertificateTable.get
    split
    · exact ihLeft parts.1
    · exact ihRight parts.2

end NetHack.Soko32Penalty5
