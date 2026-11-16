import Owner1007.UpperQuiet11
import Owner1007.TokenPersistence
namespace Owner1007.UpperQuiet11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem Quiet.fixed {paid state group dirs final pushes moves outcomes cell}
 (quiet : Quiet paid state group dirs final pushes moves outcomes)
 (member : cell∈group) (pays : ∀dir, paid cell dir) :
 ownPushes [cell] outcomes=0 := by
 induction quiet with
 | nil => rfl
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have ownZero : ownPush [cell] outcome=0 := by
     cases outcome with
     | walk _ => rfl
     | push source ending =>
       by_cases same : source=cell
       · subst source
         have metadata : t.pushSource=some cell := by
           cases ending with
           | stay landing => rw [effect.2]
           | fill hole => rw [effect.2.2]
         exact False.elim (avoid ⟨cell,member,metadata,pays dir⟩)
       · have outside : source∉[cell] := by simpa only [List.mem_singleton] using same
         simp only [ownPush,if_neg outside]
   have unchanged := ownPush_zero_update [cell] outcome ownZero
   have smallSubset : [cell]⊆group := by simpa using member
   have nextSubset := update_mono [cell] group (by simp) smallSubset outcome
   rw [unchanged] at nextSubset
   have nextMember := nextSubset (by simp : cell∈[cell])
   have tailZero := ih nextMember
   simpa only [ownPushes,ownZero,unchanged,Nat.zero_add] using tailZero
#print axioms Quiet.fixed
end Owner1007.UpperQuiet11
