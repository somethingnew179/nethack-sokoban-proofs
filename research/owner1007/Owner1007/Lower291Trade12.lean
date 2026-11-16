import Owner1007.After26512
import Owner1007.OwnedEventsMore12
import Owner1007.EndGroupMono
namespace Owner1007.Lower291Trade12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def B (i : Fin 4) : List Cell := [318,After26512.current i]
theorem trade {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 4)
 (hero : state.player∈After26512.region i)
 (inside : After26512.locks i⊆state.boulders) :
 2≤energy p [291] outcomes ∨3≤energy p (B i) outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ After26512.matrix
 rcases event_or_good closed After26512.unique logged reached (After26512.locks i)
   (After26512.unique i) inside hero (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,locksOne,pays,fixed⟩ :=
     event.split_fixed After26512.fixed After26512.fixed_inside After26512.fixed_guard
       reached (After26512.unique i) inside
   have atReached := reached.append first.trace
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨_,headPaid⟩:=pays
     have price := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
       atReached.holes_sublist.subset
       (by
         intro dest member
         have sourceMember : source∈([291,318]:List Cell) := by
           rcases headPaid with ⟨rfl,_⟩|⟨rfl,_⟩ <;>decide +kernel
         have raw := After26512.paid_cost source sourceMember dir (Geometry.all_directions dir) headPaid dest member
         refine ⟨raw.1,?_⟩
         rw [raw.2]
         by_cases a : source=318 <;>by_cases b : dir=.south <;>simp [a,b]) checked effect
     rcases headPaid with ⟨rfl,choices⟩|⟨rfl,rfl⟩
     · have prior := fixed [291] (by decide +kernel)
       have bound := event_energy_le Generated.soko1_2_potential_valid [291] first last (.push 291 ending)
       rw [prior] at bound
       simp only [projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound
       rw [←shape] at bound
       change slack p (.push 291 ending)≤energy p [291] outcomes at bound
       have two : (2:Int)≤slack p (.push 291 ending) := by simpa using price
       exact Or.inl (by omega)
     · have singletonInside : ([318]:List Cell)⊆state.boulders := by
         have check : ∀ i,([318]:List Cell)⊆After26512.locks i := by decide +kernel
         exact List.Subset.trans (check i) inside
       have mono := first.end_mono actualUnique [318] (B i) (by decide +kernel) singletonInside (by simp [B])
       have prior := fixed [318] (by decide +kernel)
       have owner : (318:Cell)∈endGroup (B i) before := by
         apply mono
         rw [prior]
         simp
       have bound := event_energy_le Generated.soko1_2_potential_valid (B i) first last (.push 318 ending)
       simp only [projectedOutcome,if_pos owner] at bound
       rw [←shape] at bound
       change slack p (.push 318 ending)≤energy p (B i) outcomes at bound
       have three : (3:Int)≤slack p (.push 318 ending) := by simpa using price
       exact Or.inr (by omega)
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (After26512.locks i) (After26512.unique i) inside
   have count := List.Nodup.length_le_of_subset (After26512.unique j) (List.Subset.trans kept endInside.2)
   rw [After26512.size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms trade
end Owner1007.Lower291Trade12
