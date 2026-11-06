/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d480 (p : Pattern) : Int := if p 49 then d479 p else d447 p
theorem agree480 (p q : Pattern) (h : Agree support p q) : d480 p = d480 q := by
  simp only [d480, h 49 (by decide), agree479 p q h, agree447 p q h]
theorem nonnegative480 (p : Pattern) : 0 ≤ d480 p :=
  nonnegative_ite (p 49) (nonnegative479 p) (nonnegative447 p)
def d481 (p : Pattern) : Int := if p 48 then d480 p else d169 p
theorem agree481 (p q : Pattern) (h : Agree support p q) : d481 p = d481 q := by
  simp only [d481, h 48 (by decide), agree480 p q h, agree169 p q h]
theorem nonnegative481 (p : Pattern) : 0 ≤ d481 p :=
  nonnegative_ite (p 48) (nonnegative480 p) (nonnegative169 p)
def d482 (p : Pattern) : Int := if p 49 then d447 p else d101 p
theorem agree482 (p q : Pattern) (h : Agree support p q) : d482 p = d482 q := by
  simp only [d482, h 49 (by decide), agree447 p q h, agree101 p q h]
theorem nonnegative482 (p : Pattern) : 0 ≤ d482 p :=
  nonnegative_ite (p 49) (nonnegative447 p) (nonnegative101 p)
def d483 (p : Pattern) : Int := if p 49 then d479 p else d101 p
theorem agree483 (p q : Pattern) (h : Agree support p q) : d483 p = d483 q := by
  simp only [d483, h 49 (by decide), agree479 p q h, agree101 p q h]
theorem nonnegative483 (p : Pattern) : 0 ≤ d483 p :=
  nonnegative_ite (p 49) (nonnegative479 p) (nonnegative101 p)
def d484 (p : Pattern) : Int := if p 48 then d483 p else d482 p
theorem agree484 (p q : Pattern) (h : Agree support p q) : d484 p = d484 q := by
  simp only [d484, h 48 (by decide), agree483 p q h, agree482 p q h]
theorem nonnegative484 (p : Pattern) : 0 ≤ d484 p :=
  nonnegative_ite (p 48) (nonnegative483 p) (nonnegative482 p)
def d485 (p : Pattern) : Int := if p 71 then d446 p else d101 p
theorem agree485 (p q : Pattern) (h : Agree support p q) : d485 p = d485 q := by
  simp only [d485, h 71 (by decide), agree446 p q h, agree101 p q h]
theorem nonnegative485 (p : Pattern) : 0 ≤ d485 p :=
  nonnegative_ite (p 71) (nonnegative446 p) (nonnegative101 p)
def d486 (p : Pattern) : Int := if p 71 then d478 p else d101 p
theorem agree486 (p q : Pattern) (h : Agree support p q) : d486 p = d486 q := by
  simp only [d486, h 71 (by decide), agree478 p q h, agree101 p q h]
theorem nonnegative486 (p : Pattern) : 0 ≤ d486 p :=
  nonnegative_ite (p 71) (nonnegative478 p) (nonnegative101 p)
def d487 (p : Pattern) : Int := if p 49 then d486 p else d485 p
theorem agree487 (p q : Pattern) (h : Agree support p q) : d487 p = d487 q := by
  simp only [d487, h 49 (by decide), agree486 p q h, agree485 p q h]
theorem nonnegative487 (p : Pattern) : 0 ≤ d487 p :=
  nonnegative_ite (p 49) (nonnegative486 p) (nonnegative485 p)
def d488 (p : Pattern) : Int := if p 48 then d487 p else d485 p
theorem agree488 (p q : Pattern) (h : Agree support p q) : d488 p = d488 q := by
  simp only [d488, h 48 (by decide), agree487 p q h, agree485 p q h]
theorem nonnegative488 (p : Pattern) : 0 ≤ d488 p :=
  nonnegative_ite (p 48) (nonnegative487 p) (nonnegative485 p)
def d489 (p : Pattern) : Int := if p 115 then d426 p else d98 p
theorem agree489 (p q : Pattern) (h : Agree support p q) : d489 p = d489 q := by
  simp only [d489, h 115 (by decide), agree426 p q h, agree98 p q h]
theorem nonnegative489 (p : Pattern) : 0 ≤ d489 p :=
  nonnegative_ite (p 115) (nonnegative426 p) (nonnegative98 p)
def d490 (p : Pattern) : Int := if p 115 then d445 p else d98 p
theorem agree490 (p q : Pattern) (h : Agree support p q) : d490 p = d490 q := by
  simp only [d490, h 115 (by decide), agree445 p q h, agree98 p q h]
theorem nonnegative490 (p : Pattern) : 0 ≤ d490 p :=
  nonnegative_ite (p 115) (nonnegative445 p) (nonnegative98 p)
def d491 (p : Pattern) : Int := if p 71 then d490 p else d489 p
theorem agree491 (p q : Pattern) (h : Agree support p q) : d491 p = d491 q := by
  simp only [d491, h 71 (by decide), agree490 p q h, agree489 p q h]
theorem nonnegative491 (p : Pattern) : 0 ≤ d491 p :=
  nonnegative_ite (p 71) (nonnegative490 p) (nonnegative489 p)
def d492 (p : Pattern) : Int := if p 115 then d445 p else d164 p
theorem agree492 (p q : Pattern) (h : Agree support p q) : d492 p = d492 q := by
  simp only [d492, h 115 (by decide), agree445 p q h, agree164 p q h]
theorem nonnegative492 (p : Pattern) : 0 ≤ d492 p :=
  nonnegative_ite (p 115) (nonnegative445 p) (nonnegative164 p)
def d493 (p : Pattern) : Int := if p 71 then d492 p else d489 p
theorem agree493 (p q : Pattern) (h : Agree support p q) : d493 p = d493 q := by
  simp only [d493, h 71 (by decide), agree492 p q h, agree489 p q h]
theorem nonnegative493 (p : Pattern) : 0 ≤ d493 p :=
  nonnegative_ite (p 71) (nonnegative492 p) (nonnegative489 p)
def d494 (p : Pattern) : Int := if p 49 then d493 p else d491 p
theorem agree494 (p q : Pattern) (h : Agree support p q) : d494 p = d494 q := by
  simp only [d494, h 49 (by decide), agree493 p q h, agree491 p q h]
theorem nonnegative494 (p : Pattern) : 0 ≤ d494 p :=
  nonnegative_ite (p 49) (nonnegative493 p) (nonnegative491 p)
def d495 (p : Pattern) : Int := if p 115 then d477 p else d225 p
theorem agree495 (p q : Pattern) (h : Agree support p q) : d495 p = d495 q := by
  simp only [d495, h 115 (by decide), agree477 p q h, agree225 p q h]
theorem nonnegative495 (p : Pattern) : 0 ≤ d495 p :=
  nonnegative_ite (p 115) (nonnegative477 p) (nonnegative225 p)
def d496 (p : Pattern) : Int := if p 71 then d495 p else d489 p
theorem agree496 (p q : Pattern) (h : Agree support p q) : d496 p = d496 q := by
  simp only [d496, h 71 (by decide), agree495 p q h, agree489 p q h]
theorem nonnegative496 (p : Pattern) : 0 ≤ d496 p :=
  nonnegative_ite (p 71) (nonnegative495 p) (nonnegative489 p)
def d497 (p : Pattern) : Int := if p 49 then d496 p else d491 p
theorem agree497 (p q : Pattern) (h : Agree support p q) : d497 p = d497 q := by
  simp only [d497, h 49 (by decide), agree496 p q h, agree491 p q h]
theorem nonnegative497 (p : Pattern) : 0 ≤ d497 p :=
  nonnegative_ite (p 49) (nonnegative496 p) (nonnegative491 p)
def d498 (p : Pattern) : Int := if p 48 then d497 p else d494 p
theorem agree498 (p q : Pattern) (h : Agree support p q) : d498 p = d498 q := by
  simp only [d498, h 48 (by decide), agree497 p q h, agree494 p q h]
theorem nonnegative498 (p : Pattern) : 0 ≤ d498 p :=
  nonnegative_ite (p 48) (nonnegative497 p) (nonnegative494 p)
def d499 (p : Pattern) : Int := if p 116 then d413 p else d88 p
theorem agree499 (p q : Pattern) (h : Agree support p q) : d499 p = d499 q := by
  simp only [d499, h 116 (by decide), agree413 p q h, agree88 p q h]
theorem nonnegative499 (p : Pattern) : 0 ≤ d499 p :=
  nonnegative_ite (p 116) (nonnegative413 p) (nonnegative88 p)
def d500 (p : Pattern) : Int := if p 116 then d425 p else d88 p
theorem agree500 (p q : Pattern) (h : Agree support p q) : d500 p = d500 q := by
  simp only [d500, h 116 (by decide), agree425 p q h, agree88 p q h]
theorem nonnegative500 (p : Pattern) : 0 ≤ d500 p :=
  nonnegative_ite (p 116) (nonnegative425 p) (nonnegative88 p)
def d501 (p : Pattern) : Int := if p 115 then d500 p else d499 p
theorem agree501 (p q : Pattern) (h : Agree support p q) : d501 p = d501 q := by
  simp only [d501, h 115 (by decide), agree500 p q h, agree499 p q h]
theorem nonnegative501 (p : Pattern) : 0 ≤ d501 p :=
  nonnegative_ite (p 115) (nonnegative500 p) (nonnegative499 p)
def d502 (p : Pattern) : Int := if p 116 then d442 p else d88 p
theorem agree502 (p q : Pattern) (h : Agree support p q) : d502 p = d502 q := by
  simp only [d502, h 116 (by decide), agree442 p q h, agree88 p q h]
theorem nonnegative502 (p : Pattern) : 0 ≤ d502 p :=
  nonnegative_ite (p 116) (nonnegative442 p) (nonnegative88 p)
def d503 (p : Pattern) : Int := if p 116 then d444 p else d88 p
theorem agree503 (p q : Pattern) (h : Agree support p q) : d503 p = d503 q := by
  simp only [d503, h 116 (by decide), agree444 p q h, agree88 p q h]
theorem nonnegative503 (p : Pattern) : 0 ≤ d503 p :=
  nonnegative_ite (p 116) (nonnegative444 p) (nonnegative88 p)
def d504 (p : Pattern) : Int := if p 115 then d503 p else d502 p
theorem agree504 (p q : Pattern) (h : Agree support p q) : d504 p = d504 q := by
  simp only [d504, h 115 (by decide), agree503 p q h, agree502 p q h]
theorem nonnegative504 (p : Pattern) : 0 ≤ d504 p :=
  nonnegative_ite (p 115) (nonnegative503 p) (nonnegative502 p)
def d505 (p : Pattern) : Int := if p 71 then d504 p else d501 p
theorem agree505 (p q : Pattern) (h : Agree support p q) : d505 p = d505 q := by
  simp only [d505, h 71 (by decide), agree504 p q h, agree501 p q h]
theorem nonnegative505 (p : Pattern) : 0 ≤ d505 p :=
  nonnegative_ite (p 71) (nonnegative504 p) (nonnegative501 p)
def d506 (p : Pattern) : Int := if p 116 then d442 p else d158 p
theorem agree506 (p q : Pattern) (h : Agree support p q) : d506 p = d506 q := by
  simp only [d506, h 116 (by decide), agree442 p q h, agree158 p q h]
theorem nonnegative506 (p : Pattern) : 0 ≤ d506 p :=
  nonnegative_ite (p 116) (nonnegative442 p) (nonnegative158 p)
def d507 (p : Pattern) : Int := if p 116 then d444 p else d158 p
theorem agree507 (p q : Pattern) (h : Agree support p q) : d507 p = d507 q := by
  simp only [d507, h 116 (by decide), agree444 p q h, agree158 p q h]
theorem nonnegative507 (p : Pattern) : 0 ≤ d507 p :=
  nonnegative_ite (p 116) (nonnegative444 p) (nonnegative158 p)
def d508 (p : Pattern) : Int := if p 115 then d507 p else d506 p
theorem agree508 (p q : Pattern) (h : Agree support p q) : d508 p = d508 q := by
  simp only [d508, h 115 (by decide), agree507 p q h, agree506 p q h]
theorem nonnegative508 (p : Pattern) : 0 ≤ d508 p :=
  nonnegative_ite (p 115) (nonnegative507 p) (nonnegative506 p)
def d509 (p : Pattern) : Int := if p 71 then d508 p else d501 p
theorem agree509 (p q : Pattern) (h : Agree support p q) : d509 p = d509 q := by
  simp only [d509, h 71 (by decide), agree508 p q h, agree501 p q h]
theorem nonnegative509 (p : Pattern) : 0 ≤ d509 p :=
  nonnegative_ite (p 71) (nonnegative508 p) (nonnegative501 p)
def d510 (p : Pattern) : Int := if p 49 then d509 p else d505 p
theorem agree510 (p q : Pattern) (h : Agree support p q) : d510 p = d510 q := by
  simp only [d510, h 49 (by decide), agree509 p q h, agree505 p q h]
theorem nonnegative510 (p : Pattern) : 0 ≤ d510 p :=
  nonnegative_ite (p 49) (nonnegative509 p) (nonnegative505 p)
def d511 (p : Pattern) : Int := if p 116 then d463 p else d223 p
theorem agree511 (p q : Pattern) (h : Agree support p q) : d511 p = d511 q := by
  simp only [d511, h 116 (by decide), agree463 p q h, agree223 p q h]
theorem nonnegative511 (p : Pattern) : 0 ≤ d511 p :=
  nonnegative_ite (p 116) (nonnegative463 p) (nonnegative223 p)
def d512 (p : Pattern) : Int := if p 116 then d476 p else d306 p
theorem agree512 (p q : Pattern) (h : Agree support p q) : d512 p = d512 q := by
  simp only [d512, h 116 (by decide), agree476 p q h, agree306 p q h]
theorem nonnegative512 (p : Pattern) : 0 ≤ d512 p :=
  nonnegative_ite (p 116) (nonnegative476 p) (nonnegative306 p)
def d513 (p : Pattern) : Int := if p 115 then d512 p else d511 p
theorem agree513 (p q : Pattern) (h : Agree support p q) : d513 p = d513 q := by
  simp only [d513, h 115 (by decide), agree512 p q h, agree511 p q h]
theorem nonnegative513 (p : Pattern) : 0 ≤ d513 p :=
  nonnegative_ite (p 115) (nonnegative512 p) (nonnegative511 p)
def d514 (p : Pattern) : Int := if p 71 then d513 p else d501 p
theorem agree514 (p q : Pattern) (h : Agree support p q) : d514 p = d514 q := by
  simp only [d514, h 71 (by decide), agree513 p q h, agree501 p q h]
theorem nonnegative514 (p : Pattern) : 0 ≤ d514 p :=
  nonnegative_ite (p 71) (nonnegative513 p) (nonnegative501 p)
def d515 (p : Pattern) : Int := if p 49 then d514 p else d505 p
theorem agree515 (p q : Pattern) (h : Agree support p q) : d515 p = d515 q := by
  simp only [d515, h 49 (by decide), agree514 p q h, agree505 p q h]
theorem nonnegative515 (p : Pattern) : 0 ≤ d515 p :=
  nonnegative_ite (p 49) (nonnegative514 p) (nonnegative505 p)
def d516 (p : Pattern) : Int := if p 48 then d515 p else d510 p
theorem agree516 (p q : Pattern) (h : Agree support p q) : d516 p = d516 q := by
  simp only [d516, h 48 (by decide), agree515 p q h, agree510 p q h]
theorem nonnegative516 (p : Pattern) : 0 ≤ d516 p :=
  nonnegative_ite (p 48) (nonnegative515 p) (nonnegative510 p)
def d517 (p : Pattern) : Int := if p 138 then d400 p else d77 p
theorem agree517 (p q : Pattern) (h : Agree support p q) : d517 p = d517 q := by
  simp only [d517, h 138 (by decide), agree400 p q h, agree77 p q h]
theorem nonnegative517 (p : Pattern) : 0 ≤ d517 p :=
  nonnegative_ite (p 138) (nonnegative400 p) (nonnegative77 p)
def d518 (p : Pattern) : Int := if p 204 then d18 p else d14 p
theorem agree518 (p q : Pattern) (h : Agree support p q) : d518 p = d518 q := by
  simp only [d518, h 204 (by decide), agree18 p q h, agree14 p q h]
theorem nonnegative518 (p : Pattern) : 0 ≤ d518 p :=
  nonnegative_ite (p 204) (nonnegative18 p) (nonnegative14 p)
def d519 (p : Pattern) : Int := if p 182 then d36 p else d518 p
theorem agree519 (p q : Pattern) (h : Agree support p q) : d519 p = d519 q := by
  simp only [d519, h 182 (by decide), agree36 p q h, agree518 p q h]
theorem nonnegative519 (p : Pattern) : 0 ≤ d519 p :=
  nonnegative_ite (p 182) (nonnegative36 p) (nonnegative518 p)
def d520 (p : Pattern) : Int := if p 182 then d59 p else d518 p
theorem agree520 (p q : Pattern) (h : Agree support p q) : d520 p = d520 q := by
  simp only [d520, h 182 (by decide), agree59 p q h, agree518 p q h]
theorem nonnegative520 (p : Pattern) : 0 ≤ d520 p :=
  nonnegative_ite (p 182) (nonnegative59 p) (nonnegative518 p)
def d521 (p : Pattern) : Int := if p 163 then d520 p else d519 p
theorem agree521 (p q : Pattern) (h : Agree support p q) : d521 p = d521 q := by
  simp only [d521, h 163 (by decide), agree520 p q h, agree519 p q h]
theorem nonnegative521 (p : Pattern) : 0 ≤ d521 p :=
  nonnegative_ite (p 163) (nonnegative520 p) (nonnegative519 p)
def d522 (p : Pattern) : Int := if p 182 then d12 p else d518 p
theorem agree522 (p q : Pattern) (h : Agree support p q) : d522 p = d522 q := by
  simp only [d522, h 182 (by decide), agree12 p q h, agree518 p q h]
theorem nonnegative522 (p : Pattern) : 0 ≤ d522 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative518 p)
def d523 (p : Pattern) : Int := if p 204 then d191 p else d18 p
theorem agree523 (p q : Pattern) (h : Agree support p q) : d523 p = d523 q := by
  simp only [d523, h 204 (by decide), agree191 p q h, agree18 p q h]
theorem nonnegative523 (p : Pattern) : 0 ≤ d523 p :=
  nonnegative_ite (p 204) (nonnegative191 p) (nonnegative18 p)
def d524 (p : Pattern) : Int := if p 182 then d12 p else d523 p
theorem agree524 (p q : Pattern) (h : Agree support p q) : d524 p = d524 q := by
  simp only [d524, h 182 (by decide), agree12 p q h, agree523 p q h]
theorem nonnegative524 (p : Pattern) : 0 ≤ d524 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative523 p)
def d525 (p : Pattern) : Int := if p 163 then d524 p else d522 p
theorem agree525 (p q : Pattern) (h : Agree support p q) : d525 p = d525 q := by
  simp only [d525, h 163 (by decide), agree524 p q h, agree522 p q h]
theorem nonnegative525 (p : Pattern) : 0 ≤ d525 p :=
  nonnegative_ite (p 163) (nonnegative524 p) (nonnegative522 p)
def d526 (p : Pattern) : Int := if p 162 then d525 p else d521 p
theorem agree526 (p q : Pattern) (h : Agree support p q) : d526 p = d526 q := by
  simp only [d526, h 162 (by decide), agree525 p q h, agree521 p q h]
theorem nonnegative526 (p : Pattern) : 0 ≤ d526 p :=
  nonnegative_ite (p 162) (nonnegative525 p) (nonnegative521 p)
def d527 (p : Pattern) : Int := if p 182 then d12 p else d25 p
theorem agree527 (p q : Pattern) (h : Agree support p q) : d527 p = d527 q := by
  simp only [d527, h 182 (by decide), agree12 p q h, agree25 p q h]
theorem nonnegative527 (p : Pattern) : 0 ≤ d527 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative25 p)
def d528 (p : Pattern) : Int := if p 163 then d12 p else d527 p
theorem agree528 (p q : Pattern) (h : Agree support p q) : d528 p = d528 q := by
  simp only [d528, h 163 (by decide), agree12 p q h, agree527 p q h]
theorem nonnegative528 (p : Pattern) : 0 ≤ d528 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative527 p)
def d529 (p : Pattern) : Int := if p 162 then d528 p else d525 p
theorem agree529 (p q : Pattern) (h : Agree support p q) : d529 p = d529 q := by
  simp only [d529, h 162 (by decide), agree528 p q h, agree525 p q h]
theorem nonnegative529 (p : Pattern) : 0 ≤ d529 p :=
  nonnegative_ite (p 162) (nonnegative528 p) (nonnegative525 p)
def d530 (p : Pattern) : Int := if p 161 then d529 p else d526 p
theorem agree530 (p q : Pattern) (h : Agree support p q) : d530 p = d530 q := by
  simp only [d530, h 161 (by decide), agree529 p q h, agree526 p q h]
theorem nonnegative530 (p : Pattern) : 0 ≤ d530 p :=
  nonnegative_ite (p 161) (nonnegative529 p) (nonnegative526 p)
def d531 (p : Pattern) : Int := if p 160 then d530 p else d29 p
theorem agree531 (p q : Pattern) (h : Agree support p q) : d531 p = d531 q := by
  simp only [d531, h 160 (by decide), agree530 p q h, agree29 p q h]
theorem nonnegative531 (p : Pattern) : 0 ≤ d531 p :=
  nonnegative_ite (p 160) (nonnegative530 p) (nonnegative29 p)
def d532 (p : Pattern) : Int := if p 204 then d35 p else d31 p
theorem agree532 (p q : Pattern) (h : Agree support p q) : d532 p = d532 q := by
  simp only [d532, h 204 (by decide), agree35 p q h, agree31 p q h]
theorem nonnegative532 (p : Pattern) : 0 ≤ d532 p :=
  nonnegative_ite (p 204) (nonnegative35 p) (nonnegative31 p)
def d533 (p : Pattern) : Int := if p 182 then d12 p else d532 p
theorem agree533 (p q : Pattern) (h : Agree support p q) : d533 p = d533 q := by
  simp only [d533, h 182 (by decide), agree12 p q h, agree532 p q h]
theorem nonnegative533 (p : Pattern) : 0 ≤ d533 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative532 p)
def d534 (p : Pattern) : Int := if p 163 then d533 p else d520 p
theorem agree534 (p q : Pattern) (h : Agree support p q) : d534 p = d534 q := by
  simp only [d534, h 163 (by decide), agree533 p q h, agree520 p q h]
theorem nonnegative534 (p : Pattern) : 0 ≤ d534 p :=
  nonnegative_ite (p 163) (nonnegative533 p) (nonnegative520 p)
def d535 (p : Pattern) : Int := if p 163 then d527 p else d524 p
theorem agree535 (p q : Pattern) (h : Agree support p q) : d535 p = d535 q := by
  simp only [d535, h 163 (by decide), agree527 p q h, agree524 p q h]
theorem nonnegative535 (p : Pattern) : 0 ≤ d535 p :=
  nonnegative_ite (p 163) (nonnegative527 p) (nonnegative524 p)
def d536 (p : Pattern) : Int := if p 162 then d535 p else d534 p
theorem agree536 (p q : Pattern) (h : Agree support p q) : d536 p = d536 q := by
  simp only [d536, h 162 (by decide), agree535 p q h, agree534 p q h]
theorem nonnegative536 (p : Pattern) : 0 ≤ d536 p :=
  nonnegative_ite (p 162) (nonnegative535 p) (nonnegative534 p)
def d537 (p : Pattern) : Int := if p 163 then d277 p else d524 p
theorem agree537 (p q : Pattern) (h : Agree support p q) : d537 p = d537 q := by
  simp only [d537, h 163 (by decide), agree277 p q h, agree524 p q h]
theorem nonnegative537 (p : Pattern) : 0 ≤ d537 p :=
  nonnegative_ite (p 163) (nonnegative277 p) (nonnegative524 p)
def d538 (p : Pattern) : Int := if p 182 then d12 p else d41 p
theorem agree538 (p q : Pattern) (h : Agree support p q) : d538 p = d538 q := by
  simp only [d538, h 182 (by decide), agree12 p q h, agree41 p q h]
theorem nonnegative538 (p : Pattern) : 0 ≤ d538 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative41 p)
def d539 (p : Pattern) : Int := if p 163 then d12 p else d538 p
theorem agree539 (p q : Pattern) (h : Agree support p q) : d539 p = d539 q := by
  simp only [d539, h 163 (by decide), agree12 p q h, agree538 p q h]
theorem nonnegative539 (p : Pattern) : 0 ≤ d539 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative538 p)
def d540 (p : Pattern) : Int := if p 162 then d539 p else d537 p
theorem agree540 (p q : Pattern) (h : Agree support p q) : d540 p = d540 q := by
  simp only [d540, h 162 (by decide), agree539 p q h, agree537 p q h]
theorem nonnegative540 (p : Pattern) : 0 ≤ d540 p :=
  nonnegative_ite (p 162) (nonnegative539 p) (nonnegative537 p)
def d541 (p : Pattern) : Int := if p 161 then d540 p else d536 p
theorem agree541 (p q : Pattern) (h : Agree support p q) : d541 p = d541 q := by
  simp only [d541, h 161 (by decide), agree540 p q h, agree536 p q h]
theorem nonnegative541 (p : Pattern) : 0 ≤ d541 p :=
  nonnegative_ite (p 161) (nonnegative540 p) (nonnegative536 p)
def d542 (p : Pattern) : Int := if p 160 then d541 p else d65 p
theorem agree542 (p q : Pattern) (h : Agree support p q) : d542 p = d542 q := by
  simp only [d542, h 160 (by decide), agree541 p q h, agree65 p q h]
theorem nonnegative542 (p : Pattern) : 0 ≤ d542 p :=
  nonnegative_ite (p 160) (nonnegative541 p) (nonnegative65 p)
def d543 (p : Pattern) : Int := if p 141 then d542 p else d531 p
theorem agree543 (p q : Pattern) (h : Agree support p q) : d543 p = d543 q := by
  simp only [d543, h 141 (by decide), agree542 p q h, agree531 p q h]
theorem nonnegative543 (p : Pattern) : 0 ≤ d543 p :=
  nonnegative_ite (p 141) (nonnegative542 p) (nonnegative531 p)
def d544 (p : Pattern) : Int := if p 138 then d412 p else d543 p
theorem agree544 (p q : Pattern) (h : Agree support p q) : d544 p = d544 q := by
  simp only [d544, h 138 (by decide), agree412 p q h, agree543 p q h]
theorem nonnegative544 (p : Pattern) : 0 ≤ d544 p :=
  nonnegative_ite (p 138) (nonnegative412 p) (nonnegative543 p)
def d545 (p : Pattern) : Int := if p 116 then d544 p else d517 p
theorem agree545 (p q : Pattern) (h : Agree support p q) : d545 p = d545 q := by
  simp only [d545, h 116 (by decide), agree544 p q h, agree517 p q h]
theorem nonnegative545 (p : Pattern) : 0 ≤ d545 p :=
  nonnegative_ite (p 116) (nonnegative544 p) (nonnegative517 p)
def d546 (p : Pattern) : Int := if p 138 then d422 p else d77 p
theorem agree546 (p q : Pattern) (h : Agree support p q) : d546 p = d546 q := by
  simp only [d546, h 138 (by decide), agree422 p q h, agree77 p q h]
theorem nonnegative546 (p : Pattern) : 0 ≤ d546 p :=
  nonnegative_ite (p 138) (nonnegative422 p) (nonnegative77 p)
def d547 (p : Pattern) : Int := if p 138 then d12 p else d543 p
theorem agree547 (p q : Pattern) (h : Agree support p q) : d547 p = d547 q := by
  simp only [d547, h 138 (by decide), agree12 p q h, agree543 p q h]
theorem nonnegative547 (p : Pattern) : 0 ≤ d547 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative543 p)
def d548 (p : Pattern) : Int := if p 116 then d547 p else d546 p
theorem agree548 (p q : Pattern) (h : Agree support p q) : d548 p = d548 q := by
  simp only [d548, h 116 (by decide), agree547 p q h, agree546 p q h]
theorem nonnegative548 (p : Pattern) : 0 ≤ d548 p :=
  nonnegative_ite (p 116) (nonnegative547 p) (nonnegative546 p)
def d549 (p : Pattern) : Int := if p 115 then d548 p else d545 p
theorem agree549 (p q : Pattern) (h : Agree support p q) : d549 p = d549 q := by
  simp only [d549, h 115 (by decide), agree548 p q h, agree545 p q h]
theorem nonnegative549 (p : Pattern) : 0 ≤ d549 p :=
  nonnegative_ite (p 115) (nonnegative548 p) (nonnegative545 p)
def d550 (p : Pattern) : Int := if p 138 then d439 p else d77 p
theorem agree550 (p q : Pattern) (h : Agree support p q) : d550 p = d550 q := by
  simp only [d550, h 138 (by decide), agree439 p q h, agree77 p q h]
theorem nonnegative550 (p : Pattern) : 0 ≤ d550 p :=
  nonnegative_ite (p 138) (nonnegative439 p) (nonnegative77 p)
def d551 (p : Pattern) : Int := if p 138 then d441 p else d543 p
theorem agree551 (p q : Pattern) (h : Agree support p q) : d551 p = d551 q := by
  simp only [d551, h 138 (by decide), agree441 p q h, agree543 p q h]
theorem nonnegative551 (p : Pattern) : 0 ≤ d551 p :=
  nonnegative_ite (p 138) (nonnegative441 p) (nonnegative543 p)
def d552 (p : Pattern) : Int := if p 116 then d551 p else d550 p
theorem agree552 (p q : Pattern) (h : Agree support p q) : d552 p = d552 q := by
  simp only [d552, h 116 (by decide), agree551 p q h, agree550 p q h]
theorem nonnegative552 (p : Pattern) : 0 ≤ d552 p :=
  nonnegative_ite (p 116) (nonnegative551 p) (nonnegative550 p)
def d553 (p : Pattern) : Int := if p 138 then d412 p else d77 p
theorem agree553 (p q : Pattern) (h : Agree support p q) : d553 p = d553 q := by
  simp only [d553, h 138 (by decide), agree412 p q h, agree77 p q h]
theorem nonnegative553 (p : Pattern) : 0 ≤ d553 p :=
  nonnegative_ite (p 138) (nonnegative412 p) (nonnegative77 p)
def d554 (p : Pattern) : Int := if p 116 then d547 p else d553 p
theorem agree554 (p q : Pattern) (h : Agree support p q) : d554 p = d554 q := by
  simp only [d554, h 116 (by decide), agree547 p q h, agree553 p q h]
theorem nonnegative554 (p : Pattern) : 0 ≤ d554 p :=
  nonnegative_ite (p 116) (nonnegative547 p) (nonnegative553 p)
def d555 (p : Pattern) : Int := if p 115 then d554 p else d552 p
theorem agree555 (p q : Pattern) (h : Agree support p q) : d555 p = d555 q := by
  simp only [d555, h 115 (by decide), agree554 p q h, agree552 p q h]
theorem nonnegative555 (p : Pattern) : 0 ≤ d555 p :=
  nonnegative_ite (p 115) (nonnegative554 p) (nonnegative552 p)
def d556 (p : Pattern) : Int := if p 71 then d555 p else d549 p
theorem agree556 (p q : Pattern) (h : Agree support p q) : d556 p = d556 q := by
  simp only [d556, h 71 (by decide), agree555 p q h, agree549 p q h]
theorem nonnegative556 (p : Pattern) : 0 ≤ d556 p :=
  nonnegative_ite (p 71) (nonnegative555 p) (nonnegative549 p)
def d557 (p : Pattern) : Int := if p 138 then d439 p else d147 p
theorem agree557 (p q : Pattern) (h : Agree support p q) : d557 p = d557 q := by
  simp only [d557, h 138 (by decide), agree439 p q h, agree147 p q h]
theorem nonnegative557 (p : Pattern) : 0 ≤ d557 p :=
  nonnegative_ite (p 138) (nonnegative439 p) (nonnegative147 p)
def d558 (p : Pattern) : Int := if p 204 then d107 p else d103 p
theorem agree558 (p q : Pattern) (h : Agree support p q) : d558 p = d558 q := by
  simp only [d558, h 204 (by decide), agree107 p q h, agree103 p q h]
theorem nonnegative558 (p : Pattern) : 0 ≤ d558 p :=
  nonnegative_ite (p 204) (nonnegative107 p) (nonnegative103 p)
def d559 (p : Pattern) : Int := if p 182 then d121 p else d558 p
theorem agree559 (p q : Pattern) (h : Agree support p q) : d559 p = d559 q := by
  simp only [d559, h 182 (by decide), agree121 p q h, agree558 p q h]
theorem nonnegative559 (p : Pattern) : 0 ≤ d559 p :=
  nonnegative_ite (p 182) (nonnegative121 p) (nonnegative558 p)
def d560 (p : Pattern) : Int := if p 182 then d41 p else d558 p
theorem agree560 (p q : Pattern) (h : Agree support p q) : d560 p = d560 q := by
  simp only [d560, h 182 (by decide), agree41 p q h, agree558 p q h]
theorem nonnegative560 (p : Pattern) : 0 ≤ d560 p :=
  nonnegative_ite (p 182) (nonnegative41 p) (nonnegative558 p)
def d561 (p : Pattern) : Int := if p 163 then d560 p else d559 p
theorem agree561 (p q : Pattern) (h : Agree support p q) : d561 p = d561 q := by
  simp only [d561, h 163 (by decide), agree560 p q h, agree559 p q h]
theorem nonnegative561 (p : Pattern) : 0 ≤ d561 p :=
  nonnegative_ite (p 163) (nonnegative560 p) (nonnegative559 p)
def d562 (p : Pattern) : Int := if p 182 then d12 p else d558 p
theorem agree562 (p q : Pattern) (h : Agree support p q) : d562 p = d562 q := by
  simp only [d562, h 182 (by decide), agree12 p q h, agree558 p q h]
theorem nonnegative562 (p : Pattern) : 0 ≤ d562 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative558 p)
def d563 (p : Pattern) : Int := if p 204 then d24 p else d107 p
theorem agree563 (p q : Pattern) (h : Agree support p q) : d563 p = d563 q := by
  simp only [d563, h 204 (by decide), agree24 p q h, agree107 p q h]
theorem nonnegative563 (p : Pattern) : 0 ≤ d563 p :=
  nonnegative_ite (p 204) (nonnegative24 p) (nonnegative107 p)
def d564 (p : Pattern) : Int := if p 182 then d12 p else d563 p
theorem agree564 (p q : Pattern) (h : Agree support p q) : d564 p = d564 q := by
  simp only [d564, h 182 (by decide), agree12 p q h, agree563 p q h]
theorem nonnegative564 (p : Pattern) : 0 ≤ d564 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative563 p)
def d565 (p : Pattern) : Int := if p 163 then d564 p else d562 p
theorem agree565 (p q : Pattern) (h : Agree support p q) : d565 p = d565 q := by
  simp only [d565, h 163 (by decide), agree564 p q h, agree562 p q h]
theorem nonnegative565 (p : Pattern) : 0 ≤ d565 p :=
  nonnegative_ite (p 163) (nonnegative564 p) (nonnegative562 p)
def d566 (p : Pattern) : Int := if p 162 then d565 p else d561 p
theorem agree566 (p q : Pattern) (h : Agree support p q) : d566 p = d566 q := by
  simp only [d566, h 162 (by decide), agree565 p q h, agree561 p q h]
theorem nonnegative566 (p : Pattern) : 0 ≤ d566 p :=
  nonnegative_ite (p 162) (nonnegative565 p) (nonnegative561 p)
def d567 (p : Pattern) : Int := if p 162 then d278 p else d565 p
theorem agree567 (p q : Pattern) (h : Agree support p q) : d567 p = d567 q := by
  simp only [d567, h 162 (by decide), agree278 p q h, agree565 p q h]
theorem nonnegative567 (p : Pattern) : 0 ≤ d567 p :=
  nonnegative_ite (p 162) (nonnegative278 p) (nonnegative565 p)
def d568 (p : Pattern) : Int := if p 161 then d567 p else d566 p
theorem agree568 (p q : Pattern) (h : Agree support p q) : d568 p = d568 q := by
  simp only [d568, h 161 (by decide), agree567 p q h, agree566 p q h]
theorem nonnegative568 (p : Pattern) : 0 ≤ d568 p :=
  nonnegative_ite (p 161) (nonnegative567 p) (nonnegative566 p)
def d569 (p : Pattern) : Int := if p 160 then d568 p else d114 p
theorem agree569 (p q : Pattern) (h : Agree support p q) : d569 p = d569 q := by
  simp only [d569, h 160 (by decide), agree568 p q h, agree114 p q h]
theorem nonnegative569 (p : Pattern) : 0 ≤ d569 p :=
  nonnegative_ite (p 160) (nonnegative568 p) (nonnegative114 p)
def d570 (p : Pattern) : Int := if p 204 then d120 p else d116 p
theorem agree570 (p q : Pattern) (h : Agree support p q) : d570 p = d570 q := by
  simp only [d570, h 204 (by decide), agree120 p q h, agree116 p q h]
theorem nonnegative570 (p : Pattern) : 0 ≤ d570 p :=
  nonnegative_ite (p 204) (nonnegative120 p) (nonnegative116 p)
def d571 (p : Pattern) : Int := if p 182 then d12 p else d570 p
theorem agree571 (p q : Pattern) (h : Agree support p q) : d571 p = d571 q := by
  simp only [d571, h 182 (by decide), agree12 p q h, agree570 p q h]
theorem nonnegative571 (p : Pattern) : 0 ≤ d571 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative570 p)
def d572 (p : Pattern) : Int := if p 163 then d571 p else d560 p
theorem agree572 (p q : Pattern) (h : Agree support p q) : d572 p = d572 q := by
  simp only [d572, h 163 (by decide), agree571 p q h, agree560 p q h]
theorem nonnegative572 (p : Pattern) : 0 ≤ d572 p :=
  nonnegative_ite (p 163) (nonnegative571 p) (nonnegative560 p)
def d573 (p : Pattern) : Int := if p 163 then d277 p else d564 p
theorem agree573 (p q : Pattern) (h : Agree support p q) : d573 p = d573 q := by
  simp only [d573, h 163 (by decide), agree277 p q h, agree564 p q h]
theorem nonnegative573 (p : Pattern) : 0 ≤ d573 p :=
  nonnegative_ite (p 163) (nonnegative277 p) (nonnegative564 p)
def d574 (p : Pattern) : Int := if p 162 then d573 p else d572 p
theorem agree574 (p q : Pattern) (h : Agree support p q) : d574 p = d574 q := by
  simp only [d574, h 162 (by decide), agree573 p q h, agree572 p q h]
theorem nonnegative574 (p : Pattern) : 0 ≤ d574 p :=
  nonnegative_ite (p 162) (nonnegative573 p) (nonnegative572 p)
def d575 (p : Pattern) : Int := if p 163 then d538 p else d564 p
theorem agree575 (p q : Pattern) (h : Agree support p q) : d575 p = d575 q := by
  simp only [d575, h 163 (by decide), agree538 p q h, agree564 p q h]
theorem nonnegative575 (p : Pattern) : 0 ≤ d575 p :=
  nonnegative_ite (p 163) (nonnegative538 p) (nonnegative564 p)
def d576 (p : Pattern) : Int := if p 162 then d12 p else d575 p
theorem agree576 (p q : Pattern) (h : Agree support p q) : d576 p = d576 q := by
  simp only [d576, h 162 (by decide), agree12 p q h, agree575 p q h]
theorem nonnegative576 (p : Pattern) : 0 ≤ d576 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative575 p)
def d577 (p : Pattern) : Int := if p 161 then d576 p else d574 p
theorem agree577 (p q : Pattern) (h : Agree support p q) : d577 p = d577 q := by
  simp only [d577, h 161 (by decide), agree576 p q h, agree574 p q h]
theorem nonnegative577 (p : Pattern) : 0 ≤ d577 p :=
  nonnegative_ite (p 161) (nonnegative576 p) (nonnegative574 p)
def d578 (p : Pattern) : Int := if p 160 then d577 p else d138 p
theorem agree578 (p q : Pattern) (h : Agree support p q) : d578 p = d578 q := by
  simp only [d578, h 160 (by decide), agree577 p q h, agree138 p q h]
theorem nonnegative578 (p : Pattern) : 0 ≤ d578 p :=
  nonnegative_ite (p 160) (nonnegative577 p) (nonnegative138 p)
def d579 (p : Pattern) : Int := if p 141 then d578 p else d569 p
theorem agree579 (p q : Pattern) (h : Agree support p q) : d579 p = d579 q := by
  simp only [d579, h 141 (by decide), agree578 p q h, agree569 p q h]
theorem nonnegative579 (p : Pattern) : 0 ≤ d579 p :=
  nonnegative_ite (p 141) (nonnegative578 p) (nonnegative569 p)
def d580 (p : Pattern) : Int := if p 138 then d441 p else d579 p
theorem agree580 (p q : Pattern) (h : Agree support p q) : d580 p = d580 q := by
  simp only [d580, h 138 (by decide), agree441 p q h, agree579 p q h]
theorem nonnegative580 (p : Pattern) : 0 ≤ d580 p :=
  nonnegative_ite (p 138) (nonnegative441 p) (nonnegative579 p)
def d581 (p : Pattern) : Int := if p 116 then d580 p else d557 p
theorem agree581 (p q : Pattern) (h : Agree support p q) : d581 p = d581 q := by
  simp only [d581, h 116 (by decide), agree580 p q h, agree557 p q h]
theorem nonnegative581 (p : Pattern) : 0 ≤ d581 p :=
  nonnegative_ite (p 116) (nonnegative580 p) (nonnegative557 p)
def d582 (p : Pattern) : Int := if p 138 then d412 p else d147 p
theorem agree582 (p q : Pattern) (h : Agree support p q) : d582 p = d582 q := by
  simp only [d582, h 138 (by decide), agree412 p q h, agree147 p q h]
theorem nonnegative582 (p : Pattern) : 0 ≤ d582 p :=
  nonnegative_ite (p 138) (nonnegative412 p) (nonnegative147 p)
def d583 (p : Pattern) : Int := if p 138 then d12 p else d579 p
theorem agree583 (p q : Pattern) (h : Agree support p q) : d583 p = d583 q := by
  simp only [d583, h 138 (by decide), agree12 p q h, agree579 p q h]
theorem nonnegative583 (p : Pattern) : 0 ≤ d583 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative579 p)
def d584 (p : Pattern) : Int := if p 116 then d583 p else d582 p
theorem agree584 (p q : Pattern) (h : Agree support p q) : d584 p = d584 q := by
  simp only [d584, h 116 (by decide), agree583 p q h, agree582 p q h]
theorem nonnegative584 (p : Pattern) : 0 ≤ d584 p :=
  nonnegative_ite (p 116) (nonnegative583 p) (nonnegative582 p)
def d585 (p : Pattern) : Int := if p 115 then d584 p else d581 p
theorem agree585 (p q : Pattern) (h : Agree support p q) : d585 p = d585 q := by
  simp only [d585, h 115 (by decide), agree584 p q h, agree581 p q h]
theorem nonnegative585 (p : Pattern) : 0 ≤ d585 p :=
  nonnegative_ite (p 115) (nonnegative584 p) (nonnegative581 p)
def d586 (p : Pattern) : Int := if p 71 then d585 p else d549 p
theorem agree586 (p q : Pattern) (h : Agree support p q) : d586 p = d586 q := by
  simp only [d586, h 71 (by decide), agree585 p q h, agree549 p q h]
theorem nonnegative586 (p : Pattern) : 0 ≤ d586 p :=
  nonnegative_ite (p 71) (nonnegative585 p) (nonnegative549 p)
def d587 (p : Pattern) : Int := if p 49 then d586 p else d556 p
theorem agree587 (p q : Pattern) (h : Agree support p q) : d587 p = d587 q := by
  simp only [d587, h 49 (by decide), agree586 p q h, agree556 p q h]
theorem nonnegative587 (p : Pattern) : 0 ≤ d587 p :=
  nonnegative_ite (p 49) (nonnegative586 p) (nonnegative556 p)
def d588 (p : Pattern) : Int := if p 204 then d18 p else d31 p
theorem agree588 (p q : Pattern) (h : Agree support p q) : d588 p = d588 q := by
  simp only [d588, h 204 (by decide), agree18 p q h, agree31 p q h]
theorem nonnegative588 (p : Pattern) : 0 ≤ d588 p :=
  nonnegative_ite (p 204) (nonnegative18 p) (nonnegative31 p)
def d589 (p : Pattern) : Int := if p 182 then d12 p else d588 p
theorem agree589 (p q : Pattern) (h : Agree support p q) : d589 p = d589 q := by
  simp only [d589, h 182 (by decide), agree12 p q h, agree588 p q h]
theorem nonnegative589 (p : Pattern) : 0 ≤ d589 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative588 p)
def d590 (p : Pattern) : Int := if p 204 then d191 p else d35 p
theorem agree590 (p q : Pattern) (h : Agree support p q) : d590 p = d590 q := by
  simp only [d590, h 204 (by decide), agree191 p q h, agree35 p q h]
theorem nonnegative590 (p : Pattern) : 0 ≤ d590 p :=
  nonnegative_ite (p 204) (nonnegative191 p) (nonnegative35 p)
def d591 (p : Pattern) : Int := if p 182 then d12 p else d590 p
theorem agree591 (p q : Pattern) (h : Agree support p q) : d591 p = d591 q := by
  simp only [d591, h 182 (by decide), agree12 p q h, agree590 p q h]
theorem nonnegative591 (p : Pattern) : 0 ≤ d591 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative590 p)
def d592 (p : Pattern) : Int := if p 163 then d591 p else d589 p
theorem agree592 (p q : Pattern) (h : Agree support p q) : d592 p = d592 q := by
  simp only [d592, h 163 (by decide), agree591 p q h, agree589 p q h]
theorem nonnegative592 (p : Pattern) : 0 ≤ d592 p :=
  nonnegative_ite (p 163) (nonnegative591 p) (nonnegative589 p)
def d593 (p : Pattern) : Int := if p 162 then d592 p else d521 p
theorem agree593 (p q : Pattern) (h : Agree support p q) : d593 p = d593 q := by
  simp only [d593, h 162 (by decide), agree592 p q h, agree521 p q h]
theorem nonnegative593 (p : Pattern) : 0 ≤ d593 p :=
  nonnegative_ite (p 162) (nonnegative592 p) (nonnegative521 p)
def d594 (p : Pattern) : Int := if p 162 then d539 p else d592 p
theorem agree594 (p q : Pattern) (h : Agree support p q) : d594 p = d594 q := by
  simp only [d594, h 162 (by decide), agree539 p q h, agree592 p q h]
theorem nonnegative594 (p : Pattern) : 0 ≤ d594 p :=
  nonnegative_ite (p 162) (nonnegative539 p) (nonnegative592 p)
def d595 (p : Pattern) : Int := if p 161 then d594 p else d593 p
theorem agree595 (p q : Pattern) (h : Agree support p q) : d595 p = d595 q := by
  simp only [d595, h 161 (by decide), agree594 p q h, agree593 p q h]
theorem nonnegative595 (p : Pattern) : 0 ≤ d595 p :=
  nonnegative_ite (p 161) (nonnegative594 p) (nonnegative593 p)
def d596 (p : Pattern) : Int := if p 160 then d595 p else d189 p
theorem agree596 (p q : Pattern) (h : Agree support p q) : d596 p = d596 q := by
  simp only [d596, h 160 (by decide), agree595 p q h, agree189 p q h]
theorem nonnegative596 (p : Pattern) : 0 ≤ d596 p :=
  nonnegative_ite (p 160) (nonnegative595 p) (nonnegative189 p)
def d597 (p : Pattern) : Int := if p 182 then d59 p else d588 p
theorem agree597 (p q : Pattern) (h : Agree support p q) : d597 p = d597 q := by
  simp only [d597, h 182 (by decide), agree59 p q h, agree588 p q h]
theorem nonnegative597 (p : Pattern) : 0 ≤ d597 p :=
  nonnegative_ite (p 182) (nonnegative59 p) (nonnegative588 p)
def d598 (p : Pattern) : Int := if p 163 then d533 p else d597 p
theorem agree598 (p q : Pattern) (h : Agree support p q) : d598 p = d598 q := by
  simp only [d598, h 163 (by decide), agree533 p q h, agree597 p q h]
theorem nonnegative598 (p : Pattern) : 0 ≤ d598 p :=
  nonnegative_ite (p 163) (nonnegative533 p) (nonnegative597 p)
def d599 (p : Pattern) : Int := if p 163 then d538 p else d524 p
theorem agree599 (p q : Pattern) (h : Agree support p q) : d599 p = d599 q := by
  simp only [d599, h 163 (by decide), agree538 p q h, agree524 p q h]
theorem nonnegative599 (p : Pattern) : 0 ≤ d599 p :=
  nonnegative_ite (p 163) (nonnegative538 p) (nonnegative524 p)
end NetHack.Sokoban22Refined85
