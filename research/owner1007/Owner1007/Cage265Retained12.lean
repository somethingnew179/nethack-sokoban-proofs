import Owner1007.FastCorral11
import Owner1007.CageLedger12
import Owner1007.Cage212Nine12
namespace Owner1007.Cage265Retained12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def lockRows : List (List Cell) := [[108,158,159,186,187,213,238,265,210,237,262],[108,158,159,186,187,213,238,265,210,211,262],[108,158,159,186,187,213,238,265,184,211,262],[108,158,159,186,187,213,238,265,184,211,236],[210,236],[184,210]]
def locks (i : Fin 6) : List Cell := lockRows[i.val]?.getD []
def regionRows : List (List Cell) := [[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,263,264,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,236,237,241,242,244,245,246,263,264,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,210,214,215,216,218,219,220,236,237,241,242,244,245,246,263,264,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,237,241,242,244,245,246,262,263,264,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400],[29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412],[29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,185,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,236,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]]
def region (i : Fin 6) : List Cell := regionRows[i.val]?.getD []
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=213 ∧ dir=.west) ∨ (source=265 ∧ dir=.north) ∨
 (source=238 ∧ dir=.east) ∨ (source=238 ∧ dir=.north) ∨
 (source=211 ∧ dir=.north) ∨ (source=211 ∧ dir=.east) ∨ (source=262 ∧ dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem row0 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 0=true := by decide +kernel
theorem row1 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 1=true := by decide +kernel
theorem row2 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 2=true := by decide +kernel
theorem row3 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 3=true := by decide +kernel
theorem row4 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 4=true := by decide +kernel
theorem row5 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid 5=true := by decide +kernel
theorem checked : ∀ i, FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
 · exact row0
 · exact row1
 · exact row2
 · exact row3
 · exact row4
 · exact row5
theorem floors : ∀ i, region i⊆soko1_2.board.floor := by decide +kernel
theorem reverse : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse floors checked
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem normal_size : ∀ i, i.val<4 → (locks i).length=11 := by decide +kernel
theorem badPair : ∀ i, 4≤i.val → [210,236]⊆locks i ∨ [184,210]⊆locks i := by decide +kernel
def normal (i : Fin 4) : Fin 6 := ⟨i.val,by omega⟩
theorem s_shift : ∀ i,
 Cage21212.locks (Cage212Nine12.normal i)⊆212::(locks (normal i)).erase 213 ∧
 213∈Cage21212.region (Cage212Nine12.normal i) := by decide +kernel
theorem pair_shift : ∀ i,
 ([239,265]:List Cell)⊆239::(locks (normal i)).erase 238 := by decide +kernel
theorem square_shift : ∀ i, ∀ source∈([238,211]:List Cell), source∈locks (normal i) →
 ([186,187,212,213]:List Cell)⊆212::(locks (normal i)).erase source := by decide +kernel
theorem gate_shift : ∀ i, 211∈locks (normal i) →
 PriceTrap12Gate.locks 0⊆185::(locks (normal i)).erase 211 ∨
 ([158,159,184,185]:List Cell)⊆185::(locks (normal i)).erase 211 := by decide +kernel
theorem upper_inside : ∀ i : Fin 4, CageLedger12.Upper⊆locks (normal i) := by decide +kernel
theorem hero263 : 263∈region (normal 0) := by decide +kernel
theorem locked_pair : Locked soko1_2.board [239,265] := locked_of_check _ _ (by decide +kernel)
#print axioms closed
end Owner1007.Cage265Retained12
