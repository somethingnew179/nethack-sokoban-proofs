/- Exact147 stay-frame data for ALL twelve real original3-2 phases.
Every original successful push oracle has a listed stay or the270E fill.
All finite cases are ordinary kernel checked; this alone is NOT a CNF or
UNSAT certificate, nor a new numerical lower bound. -/
import NetHack.Soko32ZeroSlack48.Projection
namespace NetHack.Soko32SAT.Frames
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection
abbrev phases := NetHack.SokobanLinearPhases.Map32.certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Stay where
  hero : Cell
  source : Cell
  direction : Dir
  landing : Cell
  deriving DecidableEq,BEq,Repr

def stays : List Stay := [
  ⟨80, 54, .north, 28⟩,
  ⟨28, 54, .south, 80⟩,
  ⟨53, 54, .east, 55⟩,
  ⟨55, 54, .west, 53⟩,
  ⟨54, 55, .east, 56⟩,
  ⟨56, 55, .west, 54⟩,
  ⟨55, 56, .east, 57⟩,
  ⟨57, 56, .west, 55⟩,
  ⟨56, 57, .east, 58⟩,
  ⟨58, 57, .west, 56⟩,
  ⟨57, 58, .east, 59⟩,
  ⟨59, 58, .west, 57⟩,
  ⟨58, 59, .east, 60⟩,
  ⟨60, 59, .west, 58⟩,
  ⟨59, 60, .east, 61⟩,
  ⟨61, 60, .west, 59⟩,
  ⟨60, 61, .east, 62⟩,
  ⟨62, 61, .west, 60⟩,
  ⟨105, 79, .north, 53⟩,
  ⟨53, 79, .south, 105⟩,
  ⟨106, 80, .north, 54⟩,
  ⟨54, 80, .south, 106⟩,
  ⟨112, 86, .north, 60⟩,
  ⟨60, 86, .south, 112⟩,
  ⟨131, 105, .north, 79⟩,
  ⟨79, 105, .south, 131⟩,
  ⟨132, 106, .north, 80⟩,
  ⟨80, 106, .south, 132⟩,
  ⟨108, 109, .east, 110⟩,
  ⟨110, 109, .west, 108⟩,
  ⟨138, 112, .north, 86⟩,
  ⟨86, 112, .south, 138⟩,
  ⟨112, 113, .east, 114⟩,
  ⟨114, 113, .west, 112⟩,
  ⟨157, 131, .north, 105⟩,
  ⟨105, 131, .south, 157⟩,
  ⟨158, 132, .north, 106⟩,
  ⟨106, 132, .south, 158⟩,
  ⟨131, 132, .east, 133⟩,
  ⟨133, 132, .west, 131⟩,
  ⟨132, 133, .east, 134⟩,
  ⟨134, 133, .west, 132⟩,
  ⟨160, 134, .north, 108⟩,
  ⟨108, 134, .south, 160⟩,
  ⟨133, 134, .east, 135⟩,
  ⟨135, 134, .west, 133⟩,
  ⟨161, 135, .north, 109⟩,
  ⟨109, 135, .south, 161⟩,
  ⟨134, 135, .east, 136⟩,
  ⟨136, 135, .west, 134⟩,
  ⟨162, 136, .north, 110⟩,
  ⟨110, 136, .south, 162⟩,
  ⟨135, 136, .east, 137⟩,
  ⟨137, 136, .west, 135⟩,
  ⟨136, 137, .east, 138⟩,
  ⟨138, 137, .west, 136⟩,
  ⟨137, 138, .east, 139⟩,
  ⟨139, 138, .west, 137⟩,
  ⟨165, 139, .north, 113⟩,
  ⟨113, 139, .south, 165⟩,
  ⟨183, 157, .north, 131⟩,
  ⟨131, 157, .south, 183⟩,
  ⟨157, 158, .east, 159⟩,
  ⟨159, 158, .west, 157⟩,
  ⟨158, 159, .east, 160⟩,
  ⟨160, 159, .west, 158⟩,
  ⟨159, 160, .east, 161⟩,
  ⟨161, 160, .west, 159⟩,
  ⟨160, 161, .east, 162⟩,
  ⟨162, 161, .west, 160⟩,
  ⟨188, 162, .north, 136⟩,
  ⟨136, 162, .south, 188⟩,
  ⟨161, 162, .east, 163⟩,
  ⟨163, 162, .west, 161⟩,
  ⟨189, 163, .north, 137⟩,
  ⟨137, 163, .south, 189⟩,
  ⟨209, 183, .north, 157⟩,
  ⟨157, 183, .south, 209⟩,
  ⟨214, 188, .north, 162⟩,
  ⟨162, 188, .south, 214⟩,
  ⟨215, 189, .north, 163⟩,
  ⟨163, 189, .south, 215⟩,
  ⟨218, 192, .north, 166⟩,
  ⟨166, 192, .south, 218⟩,
  ⟨235, 209, .north, 183⟩,
  ⟨183, 209, .south, 235⟩,
  ⟨209, 210, .east, 211⟩,
  ⟨211, 210, .west, 209⟩,
  ⟨210, 211, .east, 212⟩,
  ⟨212, 211, .west, 210⟩,
  ⟨211, 212, .east, 213⟩,
  ⟨213, 212, .west, 211⟩,
  ⟨212, 213, .east, 214⟩,
  ⟨214, 213, .west, 212⟩,
  ⟨213, 214, .east, 215⟩,
  ⟨215, 214, .west, 213⟩,
  ⟨241, 215, .north, 189⟩,
  ⟨189, 215, .south, 241⟩,
  ⟨214, 215, .east, 216⟩,
  ⟨216, 215, .west, 214⟩,
  ⟨244, 218, .north, 192⟩,
  ⟨192, 218, .south, 244⟩,
  ⟨261, 235, .north, 209⟩,
  ⟨209, 235, .south, 261⟩,
  ⟨265, 239, .north, 213⟩,
  ⟨213, 239, .south, 265⟩,
  ⟨267, 241, .north, 215⟩,
  ⟨215, 241, .south, 267⟩,
  ⟨241, 242, .east, 243⟩,
  ⟨243, 242, .west, 241⟩,
  ⟨242, 243, .east, 244⟩,
  ⟨244, 243, .west, 242⟩,
  ⟨270, 244, .north, 218⟩,
  ⟨218, 244, .south, 270⟩,
  ⟨243, 244, .east, 245⟩,
  ⟨245, 244, .west, 243⟩,
  ⟨287, 261, .north, 235⟩,
  ⟨235, 261, .south, 287⟩,
  ⟨291, 265, .north, 239⟩,
  ⟨239, 265, .south, 291⟩,
  ⟨265, 266, .east, 267⟩,
  ⟨267, 266, .west, 265⟩,
  ⟨293, 267, .north, 241⟩,
  ⟨241, 267, .south, 293⟩,
  ⟨295, 269, .north, 243⟩,
  ⟨243, 269, .south, 295⟩,
  ⟨271, 270, .west, 269⟩,
  ⟨287, 288, .east, 289⟩,
  ⟨289, 288, .west, 287⟩,
  ⟨288, 289, .east, 290⟩,
  ⟨290, 289, .west, 288⟩,
  ⟨289, 290, .east, 291⟩,
  ⟨291, 290, .west, 289⟩,
  ⟨317, 291, .north, 265⟩,
  ⟨265, 291, .south, 317⟩,
  ⟨290, 291, .east, 292⟩,
  ⟨292, 291, .west, 290⟩,
  ⟨318, 292, .north, 266⟩,
  ⟨266, 292, .south, 318⟩,
  ⟨291, 292, .east, 293⟩,
  ⟨293, 292, .west, 291⟩,
  ⟨292, 293, .east, 294⟩,
  ⟨294, 293, .west, 292⟩,
  ⟨293, 294, .east, 295⟩,
  ⟨295, 294, .west, 293⟩,
  ⟨321, 295, .north, 269⟩,
  ⟨269, 295, .south, 321⟩
]

def fits (hero source : Cell) (direction : Dir) (landing : Cell) (row : Stay) : Bool :=
  decide (row.hero = hero ∧ row.source = source ∧ row.direction = direction ∧ row.landing = landing)

def check (phase : Nat) (hero : Cell) (direction : Dir) : Bool :=
  match advance soko3_2.board hero direction with
  | none => true
  | some source =>
    if !(phases.crates phase).contains source then true else
    match pushOracle soko3_2.board HazardPhases.emptyBoxes
        (project (soko3_2.initial.holes.drop phase)) source direction with
    | none => true
    | some (.stay landing) => stays.any (fits hero source direction landing)
    | some (.fill hole) => decide (hero = 269 ∧ source = 270 ∧ direction = .east ∧
        hole = (soko3_2.initial.holes.drop phase).headD 0)

theorem rows_checked : ∀ phase : Fin 12,
    (phases.heroes phase).all (fun hero => allDirs.all (check phase hero)) = true := by decide +kernel

def Covered (phase : Nat) (hero source : Cell) (direction : Dir) : Ending → Prop
  | .stay landing => ∃ row ∈ stays,
      row.hero = hero ∧ row.source = source ∧ row.direction = direction ∧ row.landing = landing
  | .fill hole => hero = 269 ∧ source = 270 ∧ direction = .east ∧
      hole = (soko3_2.initial.holes.drop phase).headD 0

theorem oracle_covered (phase : Nat) (active : phase < 12) (hero : Cell)
    (heroMember : hero ∈ phases.heroes phase) (source : Cell)
    (sourceMember : source ∈ phases.crates phase) (direction : Dir)
    (adjacent : advance soko3_2.board hero direction = some source)
    (boxes : Pattern) (result : Ending)
    (success : pushOracle soko3_2.board boxes (project (soko3_2.initial.holes.drop phase))
      source direction = some result) : Covered phase hero source direction result := by
  have row := List.all_eq_true.mp (List.all_eq_true.mp (rows_checked ⟨phase,active⟩) hero heroMember)
    direction (Geometry.all_directions direction)
  have empty := HazardPhases.push_empty_covers soko3_2.board boxes _ source direction result success
  have present : (phases.crates phase).contains source = true := List.contains_iff_mem.mpr sourceMember
  simp only [check,adjacent,present,Bool.not_true,Bool.false_eq_true,↓reduceIte,empty] at row
  cases result with
  | stay landing =>
    obtain ⟨frame,member,fitsRow⟩ := List.any_eq_true.mp row
    exact ⟨frame,member,of_decide_eq_true fitsRow⟩
  | fill hole =>
    change hero = 269 ∧ source = 270 ∧ direction = .east ∧
      hole = (soko3_2.initial.holes.drop phase).headD 0
    exact of_decide_eq_true row

theorem original_push_covered {history : List Dir} {state : State} {pushes moves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state pushes moves)
    (direction : Dir) (t : Transition) (checked : step soko3_2.board state direction = some t)
    (didPush : t.pushed = true) :
    ∃ phase source result, phase < 12 ∧ state.holes = soko3_2.initial.holes.drop phase ∧
      advance soko3_2.board state.player direction = some source ∧
      pushBoulder soko3_2.board state source direction = some result ∧
      t.state = {player := source,boulders := result.boulders,holes := afterFill state.holes result.filled} ∧
      Covered phase state.player source direction (ending result) := by
  have good := NetHack.SokobanLinearPhases.Map32.trace_phase_invariant reached
  rcases good.2 with ⟨phase,within⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state within
  have current : HazardPhases.At phases
      (HazardPhaseCountedCorrection.phaseOf soko3_2.initial.holes state) state := by
    rw [←phaseEq]; exact within
  have currentActive := HazardPhaseCountedCorrection.active_of_step phases state current direction t checked
  have active : phase < 12 := by
    change HazardPhaseCountedCorrection.phaseOf soko3_2.initial.holes state < 12 at currentActive
    omega
  rcases step_cases_full soko3_2.board state direction t checked with walked | pushed
  · rcases walked with ⟨target,adjacent,floor,boxClear,holeClear,shape⟩
    simp only [shape] at didPush
    contradiction
  · rcases pushed with ⟨source,result,adjacent,floor,present,push,shape⟩
    have oracle := pushOracle_exact soko3_2.board state good.1 source direction
    rw [push,Option.map_some,within.2.1] at oracle
    exact ⟨phase,source,result,active,within.2.1,adjacent,push,by simp only [shape],
      oracle_covered phase active state.player within.2.2.1 source (within.2.2.2 present)
        direction adjacent (project state.boulders) (ending result) oracle.symm⟩

end NetHack.Soko32SAT.Frames
