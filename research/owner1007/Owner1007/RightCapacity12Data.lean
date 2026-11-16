import Owner1007.RightPrice4
import Owner1007.TokenCounting
namespace Owner1007.RightCapacity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.RightPrice4
abbrev p := Generated.soko1_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def upperLocks : Fin 5 → List Cell
 | 0 => [141,168] | 1 => [115] | 2 => [142] | 3 => [169] | 4 => []
def upperRegion (i : Fin 5) : List Cell :=
 soko1_2.board.floor.filter fun c => !(upperLocks i).contains c &&
   (if i.val=0 then !RightPrice4.pocket.contains c else true)
def upperCredit (i : Fin 5) : Int := if i.val=0 then 2 else if i.val=4 then 0 else 1
def lowLocks : Fin 5 → List Cell
 | 0 => [246] | 1 => [220] | 2 => [194] | 3 => [272] | 4 => []
def lowRegion (i : Fin 5) : List Cell :=
 soko1_2.board.floor.filter fun c => !(lowLocks i).contains c
def lowCredit (i : Fin 5) : Int :=
 if i.val=0 then 3 else if i.val=1 || i.val=3 then 2 else if i.val=2 then 1 else 0
def tokenLocks : Fin 2 → List Cell | 0 => [271] | 1 => []
def tokenRegion (i : Fin 2) : List Cell :=
 soko1_2.board.floor.filter fun c => !(tokenLocks i).contains c
def tokenCredit (i : Fin 2) : Int := if i.val=0 then 1 else 0
def upperNode (i : Fin 5) : Bool :=
  (upperRegion i).all fun hero => allDirs.all fun dir =>
   Corral11.walkCheck soko1_2.board upperLocks upperRegion i hero dir &&
    PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p upperLocks upperRegion upperCredit i hero dir
def lowNode (i : Fin 5) : Bool :=
  (lowRegion i).all fun hero => allDirs.all fun dir =>
   Corral11.walkCheck soko1_2.board lowLocks lowRegion i hero dir &&
    PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p lowLocks lowRegion lowCredit i hero dir
def tokenNode (i : Fin 2) : Bool :=
  (tokenRegion i).all fun hero => allDirs.all fun dir =>
   Corral11.walkCheck soko1_2.board tokenLocks tokenRegion i hero dir &&
    PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p tokenLocks tokenRegion tokenCredit i hero dir

theorem consumed_energy {n : Nat}
    {K R : Fin n → List Cell} {C : Fin n → Int}
    (closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p K R C)
    (Kunique : ∀ i, (K i).Nodup) (terminal : ∀ i, K i = [] → C i = 0)
    {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ soko1_2.initial.boulders)
    {i : Fin n} (heroInside : soko1_2.initial.player ∈ R i) (locksInside : K i ⊆ group)
    (gone : endGroup group outcomes = []) : C i ≤ energy p group outcomes := by
  obtain ⟨j,hero,inside,price⟩ := owned_trace_price closed Kunique logged (Trace.nil _) group
    unique subset heroInside locksInside
  have emptyLocks : K j = [] := by
    cases shape : K j with
    | nil => rfl
    | cons c rest =>
      have present : c ∈ endGroup group outcomes := inside (by simp [shape])
      simp only [gone,List.not_mem_nil] at present
  have zero := terminal j emptyLocks
  rw [zero] at price
  simpa only [energy,gone,debtOf,weightSum,Int.add_zero] using price
#print axioms consumed_energy
end Owner1007.RightCapacity12
