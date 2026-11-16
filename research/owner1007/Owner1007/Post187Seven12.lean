import Owner1007.FastCorral11
import Owner1007.RightPrice4
namespace Owner1007.Post187Seven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 11 → List Cell
 | 0 => [158,159,186,161,212,210,237,262]
 | 1 => [158,159,186,161,212,210,211,262]
 | 2 => [158,159,186,161,212,184,211,262]
 | 3 => [158,159,186,161,212,184,211,236]
 | 4 => [158,159,185,210]
 | 5 => [184,210]
 | 6 => [158,159,184,185]
 | 7 => [210,236]
 | 8 => [210,211,237,262]
 | 9 => [236,262]
 | 10 => []
def region : Fin 11 → List Cell
 | 0 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,238,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,210,213,214,215,216,218,219,220,236,237,238,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,237,238,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 4 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,160,161,163,164,166,167,168,169,180,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,236,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 5 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,185,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,236,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 6 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,160,161,163,164,166,167,168,169,180,186,187,189,190,191,192,193,194,206,210,211,212,213,214,215,216,218,219,220,232,236,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 7 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,211,212,213,214,215,216,218,219,220,232,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 8 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,212,213,214,215,216,218,219,220,232,238,239,241,242,244,245,246,252,253,254,255,256,258,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 9 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,210,211,212,213,214,215,216,218,219,220,232,237,238,239,241,242,244,245,246,252,253,254,255,256,258,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
 | 10 => [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,115,116,117,128,131,132,133,134,135,140,141,142,143,154,157,158,159,160,161,163,164,166,167,168,169,180,184,185,186,187,189,190,191,192,193,194,206,210,211,212,213,214,215,216,218,219,220,232,236,237,238,239,241,242,244,245,246,252,253,254,255,256,258,262,263,264,265,270,271,272,276,278,279,280,281,282,284,288,289,290,291,292,293,294,296,297,304,305,306,307,308,310,317,318,319,320,322,328,330,331,332,333,334,336,345,348,356,357,358,359,360,370,371,372,373,374,380,382,383,384,385,386,396,397,399,400,408,409,410,411,412]
def credit (i : Fin 11) : Int := if i.val<10 then 7 else 0
def target (i : Fin 11) (source : Cell) (dir : Dir) : Fin 11 :=
 match i.val,source,dir with
 | 0,186,.west => 4
 | 0,212,.west => 8
 | 0,237,.north => 1
 | 0,237,.west => 7
 | 0,262,.north => 7
 | 1,186,.west => 4
 | 1,210,.north => 2
 | 1,211,.north => 4
 | 1,262,.north => 7
 | 2,186,.west => 6
 | 2,211,.north => 6
 | 2,262,.north => 3
 | 3,186,.west => 6
 | 3,211,.north => 6
 | 3,236,.north => 5
 | 4,158,.south => 5
 | 4,185,.west => 5
 | 4,210,.north => 6
 | 8,210,.south => 9
 | 8,237,.west => 7
 | 8,262,.north => 7
 | _,_,_ => 10
def ShiftAt (i : Fin 11) (source : Cell) (dir : Dir) : Prop :=
 ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧ dest∉soko1_2.initial.holes ∧
 locks (target i source dir)⊆dest::(locks i).erase source ∧ source∈region (target i source dir) ∧
 credit i≤1+p.boulder dest-p.boulder source+credit (target i source dir)
instance (i : Fin 11) (source : Cell) (dir : Dir) : Decidable (ShiftAt i source dir) := by
 unfold ShiftAt
 infer_instance
def pushCheck (i : Fin 11) : Bool :=
 (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_2.board source dir.opposite with
 | none=>true
 | some hero=>decide (hero∉region i ∨ BlockedPush soko1_2.board (locks i) source dir ∨ ShiftAt i source dir)
def matrixNode (i : Fin 11) : Bool :=
 ((region i).all fun hero=>allDirs.all fun dir=>FastCorral11.walkCheck soko1_2.board locks region i hero dir) &&
 pushCheck i
theorem row0 : matrixNode 0=true := by decide +kernel
theorem row1 : matrixNode 1=true := by decide +kernel
theorem row2 : matrixNode 2=true := by decide +kernel
theorem row3 : matrixNode 3=true := by decide +kernel
theorem row4 : matrixNode 4=true := by decide +kernel
theorem row5 : matrixNode 5=true := by decide +kernel
theorem row6 : matrixNode 6=true := by decide +kernel
theorem row7 : matrixNode 7=true := by decide +kernel
theorem row8 : matrixNode 8=true := by decide +kernel
theorem row9 : matrixNode 9=true := by decide +kernel
theorem row10 : matrixNode 10=true := by decide +kernel
theorem rows : ∀ i, matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩ := i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6∨v=7∨v=8∨v=9∨v=10 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact row0
 · exact row1
 · exact row2
 · exact row3
 · exact row4
 · exact row5
 · exact row6
 · exact row7
 · exact row8
 · exact row9
 · exact row10
theorem floors : ∀ i, region i⊆soko1_2.board.floor := by decide +kernel
theorem reverse : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit := by
 constructor
 · intro i hero heroInside dir cell adjacent floor door notLock clear
   have all := (Bool.and_eq_true_iff.mp (rows i)).1
   have row := List.all_eq_true.mp (List.all_eq_true.mp all hero heroInside) dir (Geometry.all_directions dir)
   by_cases member : cell∈region i
   · exact member
   · simp only [FastCorral11.walkCheck,adjacent,if_neg member] at row
     exact False.elim (of_decide_eq_true row ⟨floor,door,notLock,clear⟩)
 · intro i hero heroInside dir source sourceInside adjacent
   have all := (Bool.and_eq_true_iff.mp (rows i)).2
   have row := List.all_eq_true.mp (List.all_eq_true.mp all source sourceInside) dir (Geometry.all_directions dir)
   have behind := Geometry.reverseCheck_sound soko1_2.board reverse hero (floors i heroInside) dir source adjacent
   simp only [pushCheck,behind] at row
   rcases (of_decide_eq_true row).resolve_left (fun outside=>outside heroInside) with blocked|shifted
   · exact Or.inl blocked
   · exact Or.inr ⟨target i source dir,shifted⟩
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i, credit i≤debtOf p (locks i) := by decide +kernel
theorem owned_energy_seven {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 11} (positive : credit i=7)
 (hero : state.player∈region i) (inside : locks i⊆group) :
 7≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique
   logged reached group gUnique subset hero inside
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have terminal := debt_credit j
 rw [positive] at price
 change 7≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms closed
#print axioms owned_energy_seven
end Owner1007.Post187Seven12
