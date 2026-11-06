/- A three-cell gate credit. The auxiliary potential only forces any
decrease to originate at244. It is NOT asserted to be a global potential. -/
import NetHack.Sokoban32Refined.LowerBound
import NetHack.Sokoban.PatternGuardMonotone
namespace NetHack.Soko32Gate138
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection NetHack.Sokoban.LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev prior := NetHack.Sokoban32Refined.certificate
abbrev potential := Generated.soko3_2Potential
def gateSupport : List Cell := [139,165,244]
def pocket : List Cell := [165,166,192,218]
def gate (hero : Cell) (p : Pattern) : Int :=
  if p 244 && (p 139 || p 165) && !pocket.contains hero then 2 else 0
def localPotential : Potential := ⟨fun cell => if cell = 244 then -1 else 0,fun _ => 0⟩
theorem gate_respects (hero : Cell) (p q : Pattern) (same : Agree gateSupport p q) : gate hero p = gate hero q := by
  have a := same 139 (by decide +kernel)
  have b := same 165 (by decide +kernel)
  have c := same 244 (by decide +kernel)
  simp only [gate,a,b,c]
theorem gate_cases (hero : Cell) (p : Pattern) : gate hero p = 0 ∨ gate hero p = 2 := by
  unfold gate; split <;> simp
theorem gate_nonnegative (hero : Cell) (p : Pattern) : 0 ≤ gate hero p := by
  rcases gate_cases hero p with h|h <;> omega
theorem gate_at_most_two (hero : Cell) (p : Pattern) : gate hero p ≤ 2 := by
  rcases gate_cases hero p with h|h <;> omega
theorem gate_positive_outside (hero : Cell) (p : Pattern) (positive : 0 < gate hero p) : hero ∉ pocket := by
  by_cases member : hero ∈ pocket
  · have zero : gate hero p = 0 := by simp [gate,member]
    omega
  · exact member

def strictCheck : Bool := soko3_2.board.floor.all fun hero => allDirs.all fun direction =>
  if advance soko3_2.board hero direction = some 244 ∧ direction.diagonal = false ∧ hero ∉ pocket then
    decide (hero ∈ ([243,245,270] : List Cell)) &&
      (PreciseRolling.stayTargets soko3_2.board 244 direction).all fun landing =>
        decide (landing ∉ prior.support ∧ 2 ≤ 1 + potential.boulder landing - potential.boulder 244)
  else true
def fillCheck : Bool := allDirs.all fun direction =>
  (pushTargets soko3_2.board 244 direction).all fun landing => decide (landing ∉ soko3_2.initial.holes)

theorem fall_source (hero : Cell) (p : Pattern) (source landing : Cell)
    (numeric : gate hero p ≤ 1 + localPotential.boulder landing - localPotential.boulder source +
      gate source (change p source (some landing)))
    (decreasing : gate source (change p source (some landing)) < gate hero p) : source = 244 := by
  by_cases same : source = 244
  · exact same
  have own : localPotential.boulder source = 0 := by simp [localPotential,same]
  have other : localPotential.boulder landing ≤ 0 := by
    change (if landing = 244 then (-1 : Int) else 0) ≤ 0
    split <;> omega
  have before := gate_cases hero p
  have after := gate_cases source (change p source (some landing))
  rw [own] at numeric
  omega
end NetHack.Soko32Gate138
