import Owner1007.FastCorral11
import Owner1007.NorthEvents12
import Owner1007.RingCut12
namespace Owner1007.PreCage12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
def U : List Cell := [108,158,159,186,187]
def sPaid (source : Cell) (dir : Dir) : Prop := (source=213 ∧ dir≠.west) ∨ source=212
instance (source : Cell) (dir : Dir) : Decidable (sPaid source dir) := by unfold sPaid; infer_instance
def northPatterns : List (List Cell) := [[210,237,238,263,265,318,345,108,158,159,186,187,213],[210,237,238,263,265,318,345,108,158,159,186,187,212],[210,237,238,263,265,318,319,108,158,159,186,187,213],[210,237,238,263,265,318,319,108,158,159,186,187,212],[210,237,238,263,265,318,293,108,158,159,186,187,213],[210,237,238,263,265,318,293,108,158,159,186,187,212],[210,237,238,263,265,318,292,108,158,159,186,187,213],[210,237,238,263,265,318,292,108,158,159,186,187,212],[210,237,238,263,265,318,291,108,158,159,186,187,213],[210,237,238,263,265,318,291,108,158,159,186,187,212]]
def northLocks (i : Fin 10) : List Cell := northPatterns[i.val]?.getD []
def northRegions : List (List Cell) := [[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,296,297,322,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,296,297,322,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,296,297,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,296,297,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,292,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,292,293,294,296,297,319,320,322,345,348,370,371,372,373,374,396,397,399,400]]
def northRegion (i : Fin 10) : List Cell := northRegions[i.val]?.getD []
def northS (i : Fin 10) : Cell := [213,212,213,212,213,212,213,212,213,212][i.val]?.getD 0
def northTag (i : Fin 10) : Cell := [345,345,319,319,293,293,292,292,291,291][i.val]?.getD 0
def ringPatterns : List (List Cell) := [[210,237,238,263,290,108,158,159,186,187,213,265],[210,237,238,263,290,108,158,159,186,187,212,265],[210,237,238,263,290,108,158,159,186,187,213,239],[210,237,238,263,290,108,158,159,186,187,212,239]]
def ringLocks (i : Fin 4) : List Cell := ringPatterns[i.val]?.getD []
def ringRegions : List (List Cell) := [[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,270,271,272,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,270,271,272,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,264,265,270,271,272,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,241,242,244,245,246,264,265,270,271,272,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]]
def ringRegion (i : Fin 4) : List Cell := ringRegions[i.val]?.getD []
def ringS (i : Fin 4) : Cell := [213,212,213,212][i.val]?.getD 0
def ringTag (i : Fin 4) : Cell := [265,265,239,239][i.val]?.getD 0
def northPaid (source : Cell) (dir : Dir) : Prop :=
 NorthEvents12.paid source dir ∨ source∈U ∨ sPaid source dir
def ringPaid (source : Cell) (dir : Dir) : Prop :=
 RingCut12.paid source dir ∨ source∈U ∨ sPaid source dir ∨
 source=239 ∨ (source=265 ∧ dir=.south) ∨ (source=238 ∧ dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (northPaid source dir) := by unfold northPaid; infer_instance
instance (source : Cell) (dir : Dir) : Decidable (ringPaid source dir) := by unfold ringPaid; infer_instance

def northAllowed (i : Fin 10) (source : Cell) (dir : Dir) (j : Fin 10) (dest : Cell) : Prop :=
 (northS i=213 ∧ source=213 ∧ dir=.west ∧ j.val=i.val+1 ∧ dest=212) ∨
 (j.val=i.val+2 ∧ source=northTag i ∧
   ((source=345 ∧ dir=.north ∧ dest=319) ∨ (source=319 ∧ dir=.north ∧ dest=293) ∨
    (source=293 ∧ dir=.west ∧ dest=292) ∨ (source=292 ∧ dir=.west ∧ dest=291)))
def ringAllowed (i : Fin 4) (source : Cell) (dir : Dir) (j : Fin 4) (dest : Cell) : Prop :=
 (ringS i=213 ∧ source=213 ∧ dir=.west ∧ j.val=i.val+1 ∧ dest=212) ∨
 (ringTag i=265 ∧ source=265 ∧ dir=.north ∧ j.val=i.val+2 ∧ dest=239)
instance (i source dir j dest) : Decidable (northAllowed i source dir j dest) := by unfold northAllowed; infer_instance
instance (i source dir j dest) : Decidable (ringAllowed i source dir j dest) := by unfold ringAllowed; infer_instance

def TaggedShift {n : Nat} (locks region : Fin n → List Cell)
 (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop) (i : Fin n) (source : Cell) (dir : Dir) : Prop :=
 ∃ j : Fin n, ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧ dest∉soko1_2.initial.holes ∧
 locks j⊆dest::(locks i).erase source ∧ source∈region j ∧ allowed i source dir j dest
instance {n} (locks region : Fin n → List Cell) (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop)
 [∀ i source dir j dest, Decidable (allowed i source dir j dest)] (i source dir) :
 Decidable (TaggedShift locks region allowed i source dir) := by unfold TaggedShift; infer_instance

def tagPart {n : Nat} (locks region : Fin n → List Cell) (paid : Cell → Dir → Prop)
 (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop)
 [∀ source dir, Decidable (paid source dir)] [∀ i source dir j dest, Decidable (allowed i source dir j dest)]
 (i : Fin n) : Bool :=
 (locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_2.board source dir.opposite with
 | none => true
 | some hero => if hero∈region i then
   decide (BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨ TaggedShift locks region allowed i source dir)
   else true
end Owner1007.PreCage12
