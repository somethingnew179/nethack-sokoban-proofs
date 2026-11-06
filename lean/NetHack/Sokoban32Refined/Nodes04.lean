/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d480 (p : Pattern) : Int := if p 134 then d70 p else d479 p
theorem agree480 (p q : Pattern) (h : Agree support p q) : d480 p = d480 q := by
  simp only [d480, h 134 (by decide), agree70 p q h, agree479 p q h]
theorem nonnegative480 (p : Pattern) : 0 ≤ d480 p :=
  nonnegative_ite (p 134) (nonnegative70 p) (nonnegative479 p)
def d481 (p : Pattern) : Int := if p 133 then d480 p else d477 p
theorem agree481 (p q : Pattern) (h : Agree support p q) : d481 p = d481 q := by
  simp only [d481, h 133 (by decide), agree480 p q h, agree477 p q h]
theorem nonnegative481 (p : Pattern) : 0 ≤ d481 p :=
  nonnegative_ite (p 133) (nonnegative480 p) (nonnegative477 p)
def d482 (p : Pattern) : Int := if p 132 then d481 p else d462 p
theorem agree482 (p q : Pattern) (h : Agree support p q) : d482 p = d482 q := by
  simp only [d482, h 132 (by decide), agree481 p q h, agree462 p q h]
theorem nonnegative482 (p : Pattern) : 0 ≤ d482 p :=
  nonnegative_ite (p 132) (nonnegative481 p) (nonnegative462 p)
def d483 (p : Pattern) : Int := if p 139 then d142 p else d8 p
theorem agree483 (p q : Pattern) (h : Agree support p q) : d483 p = d483 q := by
  simp only [d483, h 139 (by decide), agree142 p q h, agree8 p q h]
theorem nonnegative483 (p : Pattern) : 0 ≤ d483 p :=
  nonnegative_ite (p 139) (nonnegative142 p) (nonnegative8 p)
def d484 (p : Pattern) : Int := if p 138 then d52 p else d483 p
theorem agree484 (p q : Pattern) (h : Agree support p q) : d484 p = d484 q := by
  simp only [d484, h 138 (by decide), agree52 p q h, agree483 p q h]
theorem nonnegative484 (p : Pattern) : 0 ≤ d484 p :=
  nonnegative_ite (p 138) (nonnegative52 p) (nonnegative483 p)
def d485 (p : Pattern) : Int := if p 134 then d54 p else d484 p
theorem agree485 (p q : Pattern) (h : Agree support p q) : d485 p = d485 q := by
  simp only [d485, h 134 (by decide), agree54 p q h, agree484 p q h]
theorem nonnegative485 (p : Pattern) : 0 ≤ d485 p :=
  nonnegative_ite (p 134) (nonnegative54 p) (nonnegative484 p)
def d486 (p : Pattern) : Int := if p 133 then d75 p else d485 p
theorem agree486 (p q : Pattern) (h : Agree support p q) : d486 p = d486 q := by
  simp only [d486, h 133 (by decide), agree75 p q h, agree485 p q h]
theorem nonnegative486 (p : Pattern) : 0 ≤ d486 p :=
  nonnegative_ite (p 133) (nonnegative75 p) (nonnegative485 p)
def d487 (p : Pattern) : Int := if p 132 then d486 p else d462 p
theorem agree487 (p q : Pattern) (h : Agree support p q) : d487 p = d487 q := by
  simp only [d487, h 132 (by decide), agree486 p q h, agree462 p q h]
theorem nonnegative487 (p : Pattern) : 0 ≤ d487 p :=
  nonnegative_ite (p 132) (nonnegative486 p) (nonnegative462 p)
def d488 (p : Pattern) : Int := if p 113 then d487 p else d482 p
theorem agree488 (p q : Pattern) (h : Agree support p q) : d488 p = d488 q := by
  simp only [d488, h 113 (by decide), agree487 p q h, agree482 p q h]
theorem nonnegative488 (p : Pattern) : 0 ≤ d488 p :=
  nonnegative_ite (p 113) (nonnegative487 p) (nonnegative482 p)
def d489 (p : Pattern) : Int := if p 133 then d75 p else d461 p
theorem agree489 (p q : Pattern) (h : Agree support p q) : d489 p = d489 q := by
  simp only [d489, h 133 (by decide), agree75 p q h, agree461 p q h]
theorem nonnegative489 (p : Pattern) : 0 ≤ d489 p :=
  nonnegative_ite (p 133) (nonnegative75 p) (nonnegative461 p)
def d490 (p : Pattern) : Int := if p 132 then d489 p else d471 p
theorem agree490 (p q : Pattern) (h : Agree support p q) : d490 p = d490 q := by
  simp only [d490, h 132 (by decide), agree489 p q h, agree471 p q h]
theorem nonnegative490 (p : Pattern) : 0 ≤ d490 p :=
  nonnegative_ite (p 132) (nonnegative489 p) (nonnegative471 p)
def d491 (p : Pattern) : Int := if p 133 then d75 p else d470 p
theorem agree491 (p q : Pattern) (h : Agree support p q) : d491 p = d491 q := by
  simp only [d491, h 133 (by decide), agree75 p q h, agree470 p q h]
theorem nonnegative491 (p : Pattern) : 0 ≤ d491 p :=
  nonnegative_ite (p 133) (nonnegative75 p) (nonnegative470 p)
def d492 (p : Pattern) : Int := if p 132 then d491 p else d471 p
theorem agree492 (p q : Pattern) (h : Agree support p q) : d492 p = d492 q := by
  simp only [d492, h 132 (by decide), agree491 p q h, agree471 p q h]
theorem nonnegative492 (p : Pattern) : 0 ≤ d492 p :=
  nonnegative_ite (p 132) (nonnegative491 p) (nonnegative471 p)
def d493 (p : Pattern) : Int := if p 113 then d492 p else d490 p
theorem agree493 (p q : Pattern) (h : Agree support p q) : d493 p = d493 q := by
  simp only [d493, h 113 (by decide), agree492 p q h, agree490 p q h]
theorem nonnegative493 (p : Pattern) : 0 ≤ d493 p :=
  nonnegative_ite (p 113) (nonnegative492 p) (nonnegative490 p)
def d494 (p : Pattern) : Int := if p 112 then d493 p else d488 p
theorem agree494 (p q : Pattern) (h : Agree support p q) : d494 p = d494 q := by
  simp only [d494, h 112 (by decide), agree493 p q h, agree488 p q h]
theorem nonnegative494 (p : Pattern) : 0 ≤ d494 p :=
  nonnegative_ite (p 112) (nonnegative493 p) (nonnegative488 p)
def d495 (p : Pattern) : Int := if p 106 then d494 p else d476 p
theorem agree495 (p q : Pattern) (h : Agree support p q) : d495 p = d495 q := by
  simp only [d495, h 106 (by decide), agree494 p q h, agree476 p q h]
theorem nonnegative495 (p : Pattern) : 0 ≤ d495 p :=
  nonnegative_ite (p 106) (nonnegative494 p) (nonnegative476 p)
def d496 (p : Pattern) : Int := if p 134 then d58 p else d484 p
theorem agree496 (p q : Pattern) (h : Agree support p q) : d496 p = d496 q := by
  simp only [d496, h 134 (by decide), agree58 p q h, agree484 p q h]
theorem nonnegative496 (p : Pattern) : 0 ≤ d496 p :=
  nonnegative_ite (p 134) (nonnegative58 p) (nonnegative484 p)
def d497 (p : Pattern) : Int := if p 133 then d473 p else d496 p
theorem agree497 (p q : Pattern) (h : Agree support p q) : d497 p = d497 q := by
  simp only [d497, h 133 (by decide), agree473 p q h, agree496 p q h]
theorem nonnegative497 (p : Pattern) : 0 ≤ d497 p :=
  nonnegative_ite (p 133) (nonnegative473 p) (nonnegative496 p)
def d498 (p : Pattern) : Int := if p 132 then d497 p else d462 p
theorem agree498 (p q : Pattern) (h : Agree support p q) : d498 p = d498 q := by
  simp only [d498, h 132 (by decide), agree497 p q h, agree462 p q h]
theorem nonnegative498 (p : Pattern) : 0 ≤ d498 p :=
  nonnegative_ite (p 132) (nonnegative497 p) (nonnegative462 p)
def d499 (p : Pattern) : Int := if p 113 then d498 p else d468 p
theorem agree499 (p q : Pattern) (h : Agree support p q) : d499 p = d499 q := by
  simp only [d499, h 113 (by decide), agree498 p q h, agree468 p q h]
theorem nonnegative499 (p : Pattern) : 0 ≤ d499 p :=
  nonnegative_ite (p 113) (nonnegative498 p) (nonnegative468 p)
def d500 (p : Pattern) : Int := if p 139 then d138 p else d14 p
theorem agree500 (p q : Pattern) (h : Agree support p q) : d500 p = d500 q := by
  simp only [d500, h 139 (by decide), agree138 p q h, agree14 p q h]
theorem nonnegative500 (p : Pattern) : 0 ≤ d500 p :=
  nonnegative_ite (p 139) (nonnegative138 p) (nonnegative14 p)
def d501 (p : Pattern) : Int := if p 138 then d97 p else d500 p
theorem agree501 (p q : Pattern) (h : Agree support p q) : d501 p = d501 q := by
  simp only [d501, h 138 (by decide), agree97 p q h, agree500 p q h]
theorem nonnegative501 (p : Pattern) : 0 ≤ d501 p :=
  nonnegative_ite (p 138) (nonnegative97 p) (nonnegative500 p)
def d502 (p : Pattern) : Int := if p 134 then d97 p else d501 p
theorem agree502 (p q : Pattern) (h : Agree support p q) : d502 p = d502 q := by
  simp only [d502, h 134 (by decide), agree97 p q h, agree501 p q h]
theorem nonnegative502 (p : Pattern) : 0 ≤ d502 p :=
  nonnegative_ite (p 134) (nonnegative97 p) (nonnegative501 p)
def d503 (p : Pattern) : Int := if p 133 then d109 p else d502 p
theorem agree503 (p q : Pattern) (h : Agree support p q) : d503 p = d503 q := by
  simp only [d503, h 133 (by decide), agree109 p q h, agree502 p q h]
theorem nonnegative503 (p : Pattern) : 0 ≤ d503 p :=
  nonnegative_ite (p 133) (nonnegative109 p) (nonnegative502 p)
def d504 (p : Pattern) : Int := if p 134 then d70 p else d501 p
theorem agree504 (p q : Pattern) (h : Agree support p q) : d504 p = d504 q := by
  simp only [d504, h 134 (by decide), agree70 p q h, agree501 p q h]
theorem nonnegative504 (p : Pattern) : 0 ≤ d504 p :=
  nonnegative_ite (p 134) (nonnegative70 p) (nonnegative501 p)
def d505 (p : Pattern) : Int := if p 133 then d75 p else d504 p
theorem agree505 (p q : Pattern) (h : Agree support p q) : d505 p = d505 q := by
  simp only [d505, h 133 (by decide), agree75 p q h, agree504 p q h]
theorem nonnegative505 (p : Pattern) : 0 ≤ d505 p :=
  nonnegative_ite (p 133) (nonnegative75 p) (nonnegative504 p)
def d506 (p : Pattern) : Int := if p 132 then d505 p else d503 p
theorem agree506 (p q : Pattern) (h : Agree support p q) : d506 p = d506 q := by
  simp only [d506, h 132 (by decide), agree505 p q h, agree503 p q h]
theorem nonnegative506 (p : Pattern) : 0 ≤ d506 p :=
  nonnegative_ite (p 132) (nonnegative505 p) (nonnegative503 p)
def d507 (p : Pattern) : Int := if p 132 then d125 p else d503 p
theorem agree507 (p q : Pattern) (h : Agree support p q) : d507 p = d507 q := by
  simp only [d507, h 132 (by decide), agree125 p q h, agree503 p q h]
theorem nonnegative507 (p : Pattern) : 0 ≤ d507 p :=
  nonnegative_ite (p 132) (nonnegative125 p) (nonnegative503 p)
def d508 (p : Pattern) : Int := if p 113 then d507 p else d506 p
theorem agree508 (p q : Pattern) (h : Agree support p q) : d508 p = d508 q := by
  simp only [d508, h 113 (by decide), agree507 p q h, agree506 p q h]
theorem nonnegative508 (p : Pattern) : 0 ≤ d508 p :=
  nonnegative_ite (p 113) (nonnegative507 p) (nonnegative506 p)
def d509 (p : Pattern) : Int := if p 112 then d508 p else d499 p
theorem agree509 (p q : Pattern) (h : Agree support p q) : d509 p = d509 q := by
  simp only [d509, h 112 (by decide), agree508 p q h, agree499 p q h]
theorem nonnegative509 (p : Pattern) : 0 ≤ d509 p :=
  nonnegative_ite (p 112) (nonnegative508 p) (nonnegative499 p)
def d510 (p : Pattern) : Int := if p 134 then d52 p else d484 p
theorem agree510 (p q : Pattern) (h : Agree support p q) : d510 p = d510 q := by
  simp only [d510, h 134 (by decide), agree52 p q h, agree484 p q h]
theorem nonnegative510 (p : Pattern) : 0 ≤ d510 p :=
  nonnegative_ite (p 134) (nonnegative52 p) (nonnegative484 p)
def d511 (p : Pattern) : Int := if p 133 then d470 p else d510 p
theorem agree511 (p q : Pattern) (h : Agree support p q) : d511 p = d511 q := by
  simp only [d511, h 133 (by decide), agree470 p q h, agree510 p q h]
theorem nonnegative511 (p : Pattern) : 0 ≤ d511 p :=
  nonnegative_ite (p 133) (nonnegative470 p) (nonnegative510 p)
def d512 (p : Pattern) : Int := if p 132 then d491 p else d511 p
theorem agree512 (p q : Pattern) (h : Agree support p q) : d512 p = d512 q := by
  simp only [d512, h 132 (by decide), agree491 p q h, agree511 p q h]
theorem nonnegative512 (p : Pattern) : 0 ≤ d512 p :=
  nonnegative_ite (p 132) (nonnegative491 p) (nonnegative511 p)
def d513 (p : Pattern) : Int := if p 113 then d512 p else d487 p
theorem agree513 (p q : Pattern) (h : Agree support p q) : d513 p = d513 q := by
  simp only [d513, h 113 (by decide), agree512 p q h, agree487 p q h]
theorem nonnegative513 (p : Pattern) : 0 ≤ d513 p :=
  nonnegative_ite (p 113) (nonnegative512 p) (nonnegative487 p)
def d514 (p : Pattern) : Int := if p 132 then d111 p else d503 p
theorem agree514 (p q : Pattern) (h : Agree support p q) : d514 p = d514 q := by
  simp only [d514, h 132 (by decide), agree111 p q h, agree503 p q h]
theorem nonnegative514 (p : Pattern) : 0 ≤ d514 p :=
  nonnegative_ite (p 132) (nonnegative111 p) (nonnegative503 p)
def d515 (p : Pattern) : Int := if p 113 then d112 p else d514 p
theorem agree515 (p q : Pattern) (h : Agree support p q) : d515 p = d515 q := by
  simp only [d515, h 113 (by decide), agree112 p q h, agree514 p q h]
theorem nonnegative515 (p : Pattern) : 0 ≤ d515 p :=
  nonnegative_ite (p 113) (nonnegative112 p) (nonnegative514 p)
def d516 (p : Pattern) : Int := if p 112 then d515 p else d513 p
theorem agree516 (p q : Pattern) (h : Agree support p q) : d516 p = d516 q := by
  simp only [d516, h 112 (by decide), agree515 p q h, agree513 p q h]
theorem nonnegative516 (p : Pattern) : 0 ≤ d516 p :=
  nonnegative_ite (p 112) (nonnegative515 p) (nonnegative513 p)
def d517 (p : Pattern) : Int := if p 106 then d516 p else d509 p
theorem agree517 (p q : Pattern) (h : Agree support p q) : d517 p = d517 q := by
  simp only [d517, h 106 (by decide), agree516 p q h, agree509 p q h]
theorem nonnegative517 (p : Pattern) : 0 ≤ d517 p :=
  nonnegative_ite (p 106) (nonnegative516 p) (nonnegative509 p)
def d518 (p : Pattern) : Int := if p 86 then d517 p else d495 p
theorem agree518 (p q : Pattern) (h : Agree support p q) : d518 p = d518 q := by
  simp only [d518, h 86 (by decide), agree517 p q h, agree495 p q h]
theorem nonnegative518 (p : Pattern) : 0 ≤ d518 p :=
  nonnegative_ite (p 86) (nonnegative517 p) (nonnegative495 p)
def d519 (p : Pattern) : Int := if p 134 then d58 p else d52 p
theorem agree519 (p q : Pattern) (h : Agree support p q) : d519 p = d519 q := by
  simp only [d519, h 134 (by decide), agree58 p q h, agree52 p q h]
theorem nonnegative519 (p : Pattern) : 0 ≤ d519 p :=
  nonnegative_ite (p 134) (nonnegative58 p) (nonnegative52 p)
def d520 (p : Pattern) : Int := if p 133 then d473 p else d519 p
theorem agree520 (p q : Pattern) (h : Agree support p q) : d520 p = d520 q := by
  simp only [d520, h 133 (by decide), agree473 p q h, agree519 p q h]
theorem nonnegative520 (p : Pattern) : 0 ≤ d520 p :=
  nonnegative_ite (p 133) (nonnegative473 p) (nonnegative519 p)
def d521 (p : Pattern) : Int := if p 132 then d520 p else d471 p
theorem agree521 (p q : Pattern) (h : Agree support p q) : d521 p = d521 q := by
  simp only [d521, h 132 (by decide), agree520 p q h, agree471 p q h]
theorem nonnegative521 (p : Pattern) : 0 ≤ d521 p :=
  nonnegative_ite (p 132) (nonnegative520 p) (nonnegative471 p)
def d522 (p : Pattern) : Int := if p 113 then d521 p else d475 p
theorem agree522 (p q : Pattern) (h : Agree support p q) : d522 p = d522 q := by
  simp only [d522, h 113 (by decide), agree521 p q h, agree475 p q h]
theorem nonnegative522 (p : Pattern) : 0 ≤ d522 p :=
  nonnegative_ite (p 113) (nonnegative521 p) (nonnegative475 p)
def d523 (p : Pattern) : Int := if p 112 then d522 p else d499 p
theorem agree523 (p q : Pattern) (h : Agree support p q) : d523 p = d523 q := by
  simp only [d523, h 112 (by decide), agree522 p q h, agree499 p q h]
theorem nonnegative523 (p : Pattern) : 0 ≤ d523 p :=
  nonnegative_ite (p 112) (nonnegative522 p) (nonnegative499 p)
def d524 (p : Pattern) : Int := if p 133 then d470 p else d52 p
theorem agree524 (p q : Pattern) (h : Agree support p q) : d524 p = d524 q := by
  simp only [d524, h 133 (by decide), agree470 p q h, agree52 p q h]
theorem nonnegative524 (p : Pattern) : 0 ≤ d524 p :=
  nonnegative_ite (p 133) (nonnegative470 p) (nonnegative52 p)
def d525 (p : Pattern) : Int := if p 132 then d491 p else d524 p
theorem agree525 (p q : Pattern) (h : Agree support p q) : d525 p = d525 q := by
  simp only [d525, h 132 (by decide), agree491 p q h, agree524 p q h]
theorem nonnegative525 (p : Pattern) : 0 ≤ d525 p :=
  nonnegative_ite (p 132) (nonnegative491 p) (nonnegative524 p)
def d526 (p : Pattern) : Int := if p 113 then d525 p else d492 p
theorem agree526 (p q : Pattern) (h : Agree support p q) : d526 p = d526 q := by
  simp only [d526, h 113 (by decide), agree525 p q h, agree492 p q h]
theorem nonnegative526 (p : Pattern) : 0 ≤ d526 p :=
  nonnegative_ite (p 113) (nonnegative525 p) (nonnegative492 p)
def d527 (p : Pattern) : Int := if p 112 then d526 p else d513 p
theorem agree527 (p q : Pattern) (h : Agree support p q) : d527 p = d527 q := by
  simp only [d527, h 112 (by decide), agree526 p q h, agree513 p q h]
theorem nonnegative527 (p : Pattern) : 0 ≤ d527 p :=
  nonnegative_ite (p 112) (nonnegative526 p) (nonnegative513 p)
def d528 (p : Pattern) : Int := if p 106 then d527 p else d523 p
theorem agree528 (p q : Pattern) (h : Agree support p q) : d528 p = d528 q := by
  simp only [d528, h 106 (by decide), agree527 p q h, agree523 p q h]
theorem nonnegative528 (p : Pattern) : 0 ≤ d528 p :=
  nonnegative_ite (p 106) (nonnegative527 p) (nonnegative523 p)
def d529 (p : Pattern) : Int := if p 132 then d520 p else d511 p
theorem agree529 (p q : Pattern) (h : Agree support p q) : d529 p = d529 q := by
  simp only [d529, h 132 (by decide), agree520 p q h, agree511 p q h]
theorem nonnegative529 (p : Pattern) : 0 ≤ d529 p :=
  nonnegative_ite (p 132) (nonnegative520 p) (nonnegative511 p)
def d530 (p : Pattern) : Int := if p 113 then d529 p else d498 p
theorem agree530 (p q : Pattern) (h : Agree support p q) : d530 p = d530 q := by
  simp only [d530, h 113 (by decide), agree529 p q h, agree498 p q h]
theorem nonnegative530 (p : Pattern) : 0 ≤ d530 p :=
  nonnegative_ite (p 113) (nonnegative529 p) (nonnegative498 p)
def d531 (p : Pattern) : Int := if p 113 then d126 p else d507 p
theorem agree531 (p q : Pattern) (h : Agree support p q) : d531 p = d531 q := by
  simp only [d531, h 113 (by decide), agree126 p q h, agree507 p q h]
theorem nonnegative531 (p : Pattern) : 0 ≤ d531 p :=
  nonnegative_ite (p 113) (nonnegative126 p) (nonnegative507 p)
def d532 (p : Pattern) : Int := if p 112 then d531 p else d530 p
theorem agree532 (p q : Pattern) (h : Agree support p q) : d532 p = d532 q := by
  simp only [d532, h 112 (by decide), agree531 p q h, agree530 p q h]
theorem nonnegative532 (p : Pattern) : 0 ≤ d532 p :=
  nonnegative_ite (p 112) (nonnegative531 p) (nonnegative530 p)
def d533 (p : Pattern) : Int := if p 113 then d525 p else d512 p
theorem agree533 (p q : Pattern) (h : Agree support p q) : d533 p = d533 q := by
  simp only [d533, h 113 (by decide), agree525 p q h, agree512 p q h]
theorem nonnegative533 (p : Pattern) : 0 ≤ d533 p :=
  nonnegative_ite (p 113) (nonnegative525 p) (nonnegative512 p)
def d534 (p : Pattern) : Int := if p 112 then d130 p else d533 p
theorem agree534 (p q : Pattern) (h : Agree support p q) : d534 p = d534 q := by
  simp only [d534, h 112 (by decide), agree130 p q h, agree533 p q h]
theorem nonnegative534 (p : Pattern) : 0 ≤ d534 p :=
  nonnegative_ite (p 112) (nonnegative130 p) (nonnegative533 p)
def d535 (p : Pattern) : Int := if p 106 then d534 p else d532 p
theorem agree535 (p q : Pattern) (h : Agree support p q) : d535 p = d535 q := by
  simp only [d535, h 106 (by decide), agree534 p q h, agree532 p q h]
theorem nonnegative535 (p : Pattern) : 0 ≤ d535 p :=
  nonnegative_ite (p 106) (nonnegative534 p) (nonnegative532 p)
def d536 (p : Pattern) : Int := if p 86 then d535 p else d528 p
theorem agree536 (p q : Pattern) (h : Agree support p q) : d536 p = d536 q := by
  simp only [d536, h 86 (by decide), agree535 p q h, agree528 p q h]
theorem nonnegative536 (p : Pattern) : 0 ≤ d536 p :=
  nonnegative_ite (p 86) (nonnegative535 p) (nonnegative528 p)
def d537 (p : Pattern) : Int := if p 80 then d536 p else d518 p
theorem agree537 (p q : Pattern) (h : Agree support p q) : d537 p = d537 q := by
  simp only [d537, h 80 (by decide), agree536 p q h, agree518 p q h]
theorem nonnegative537 (p : Pattern) : 0 ≤ d537 p :=
  nonnegative_ite (p 80) (nonnegative536 p) (nonnegative518 p)
def d538 (p : Pattern) : Int := if p 158 then d23 p else d6 p
theorem agree538 (p q : Pattern) (h : Agree support p q) : d538 p = d538 q := by
  simp only [d538, h 158 (by decide), agree23 p q h, agree6 p q h]
theorem nonnegative538 (p : Pattern) : 0 ≤ d538 p :=
  nonnegative_ite (p 158) (nonnegative23 p) (nonnegative6 p)
def d539 (p : Pattern) : Int := if p 158 then d2 p else d6 p
theorem agree539 (p q : Pattern) (h : Agree support p q) : d539 p = d539 q := by
  simp only [d539, h 158 (by decide), agree2 p q h, agree6 p q h]
theorem nonnegative539 (p : Pattern) : 0 ≤ d539 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative6 p)
def d540 (p : Pattern) : Int := if p 158 then d2 p else d12 p
theorem agree540 (p q : Pattern) (h : Agree support p q) : d540 p = d540 q := by
  simp only [d540, h 158 (by decide), agree2 p q h, agree12 p q h]
theorem nonnegative540 (p : Pattern) : 0 ≤ d540 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative12 p)
def d541 (p : Pattern) : Int := if p 139 then d540 p else d539 p
theorem agree541 (p q : Pattern) (h : Agree support p q) : d541 p = d541 q := by
  simp only [d541, h 139 (by decide), agree540 p q h, agree539 p q h]
theorem nonnegative541 (p : Pattern) : 0 ≤ d541 p :=
  nonnegative_ite (p 139) (nonnegative540 p) (nonnegative539 p)
def d542 (p : Pattern) : Int := if p 138 then d541 p else d538 p
theorem agree542 (p q : Pattern) (h : Agree support p q) : d542 p = d542 q := by
  simp only [d542, h 138 (by decide), agree541 p q h, agree538 p q h]
theorem nonnegative542 (p : Pattern) : 0 ≤ d542 p :=
  nonnegative_ite (p 138) (nonnegative541 p) (nonnegative538 p)
def d543 (p : Pattern) : Int := if p 138 then d541 p else d539 p
theorem agree543 (p q : Pattern) (h : Agree support p q) : d543 p = d543 q := by
  simp only [d543, h 138 (by decide), agree541 p q h, agree539 p q h]
theorem nonnegative543 (p : Pattern) : 0 ≤ d543 p :=
  nonnegative_ite (p 138) (nonnegative541 p) (nonnegative539 p)
def d544 (p : Pattern) : Int := if p 134 then d543 p else d542 p
theorem agree544 (p q : Pattern) (h : Agree support p q) : d544 p = d544 q := by
  simp only [d544, h 134 (by decide), agree543 p q h, agree542 p q h]
theorem nonnegative544 (p : Pattern) : 0 ≤ d544 p :=
  nonnegative_ite (p 134) (nonnegative543 p) (nonnegative542 p)
def d545 (p : Pattern) : Int := if p 158 then d2 p else d18 p
theorem agree545 (p q : Pattern) (h : Agree support p q) : d545 p = d545 q := by
  simp only [d545, h 158 (by decide), agree2 p q h, agree18 p q h]
theorem nonnegative545 (p : Pattern) : 0 ≤ d545 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative18 p)
def d546 (p : Pattern) : Int := if p 158 then d2 p else d22 p
theorem agree546 (p q : Pattern) (h : Agree support p q) : d546 p = d546 q := by
  simp only [d546, h 158 (by decide), agree2 p q h, agree22 p q h]
theorem nonnegative546 (p : Pattern) : 0 ≤ d546 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative22 p)
def d547 (p : Pattern) : Int := if p 139 then d546 p else d545 p
theorem agree547 (p q : Pattern) (h : Agree support p q) : d547 p = d547 q := by
  simp only [d547, h 139 (by decide), agree546 p q h, agree545 p q h]
theorem nonnegative547 (p : Pattern) : 0 ≤ d547 p :=
  nonnegative_ite (p 139) (nonnegative546 p) (nonnegative545 p)
def d548 (p : Pattern) : Int := if p 138 then d547 p else d545 p
theorem agree548 (p q : Pattern) (h : Agree support p q) : d548 p = d548 q := by
  simp only [d548, h 138 (by decide), agree547 p q h, agree545 p q h]
theorem nonnegative548 (p : Pattern) : 0 ≤ d548 p :=
  nonnegative_ite (p 138) (nonnegative547 p) (nonnegative545 p)
def d549 (p : Pattern) : Int := if p 134 then d548 p else d543 p
theorem agree549 (p q : Pattern) (h : Agree support p q) : d549 p = d549 q := by
  simp only [d549, h 134 (by decide), agree548 p q h, agree543 p q h]
theorem nonnegative549 (p : Pattern) : 0 ≤ d549 p :=
  nonnegative_ite (p 134) (nonnegative548 p) (nonnegative543 p)
def d550 (p : Pattern) : Int := if p 133 then d549 p else d544 p
theorem agree550 (p q : Pattern) (h : Agree support p q) : d550 p = d550 q := by
  simp only [d550, h 133 (by decide), agree549 p q h, agree544 p q h]
theorem nonnegative550 (p : Pattern) : 0 ≤ d550 p :=
  nonnegative_ite (p 133) (nonnegative549 p) (nonnegative544 p)
def d551 (p : Pattern) : Int := if p 158 then d2 p else d31 p
theorem agree551 (p q : Pattern) (h : Agree support p q) : d551 p = d551 q := by
  simp only [d551, h 158 (by decide), agree2 p q h, agree31 p q h]
theorem nonnegative551 (p : Pattern) : 0 ≤ d551 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative31 p)
def d552 (p : Pattern) : Int := if p 139 then d546 p else d551 p
theorem agree552 (p q : Pattern) (h : Agree support p q) : d552 p = d552 q := by
  simp only [d552, h 139 (by decide), agree546 p q h, agree551 p q h]
theorem nonnegative552 (p : Pattern) : 0 ≤ d552 p :=
  nonnegative_ite (p 139) (nonnegative546 p) (nonnegative551 p)
def d553 (p : Pattern) : Int := if p 138 then d552 p else d551 p
theorem agree553 (p q : Pattern) (h : Agree support p q) : d553 p = d553 q := by
  simp only [d553, h 138 (by decide), agree552 p q h, agree551 p q h]
theorem nonnegative553 (p : Pattern) : 0 ≤ d553 p :=
  nonnegative_ite (p 138) (nonnegative552 p) (nonnegative551 p)
def d554 (p : Pattern) : Int := if p 134 then d553 p else d542 p
theorem agree554 (p q : Pattern) (h : Agree support p q) : d554 p = d554 q := by
  simp only [d554, h 134 (by decide), agree553 p q h, agree542 p q h]
theorem nonnegative554 (p : Pattern) : 0 ≤ d554 p :=
  nonnegative_ite (p 134) (nonnegative553 p) (nonnegative542 p)
def d555 (p : Pattern) : Int := if p 133 then d549 p else d554 p
theorem agree555 (p q : Pattern) (h : Agree support p q) : d555 p = d555 q := by
  simp only [d555, h 133 (by decide), agree549 p q h, agree554 p q h]
theorem nonnegative555 (p : Pattern) : 0 ≤ d555 p :=
  nonnegative_ite (p 133) (nonnegative549 p) (nonnegative554 p)
def d556 (p : Pattern) : Int := if p 132 then d555 p else d550 p
theorem agree556 (p q : Pattern) (h : Agree support p q) : d556 p = d556 q := by
  simp only [d556, h 132 (by decide), agree555 p q h, agree550 p q h]
theorem nonnegative556 (p : Pattern) : 0 ≤ d556 p :=
  nonnegative_ite (p 132) (nonnegative555 p) (nonnegative550 p)
def d557 (p : Pattern) : Int := if p 134 then d547 p else d541 p
theorem agree557 (p q : Pattern) (h : Agree support p q) : d557 p = d557 q := by
  simp only [d557, h 134 (by decide), agree547 p q h, agree541 p q h]
theorem nonnegative557 (p : Pattern) : 0 ≤ d557 p :=
  nonnegative_ite (p 134) (nonnegative547 p) (nonnegative541 p)
def d558 (p : Pattern) : Int := if p 133 then d557 p else d541 p
theorem agree558 (p q : Pattern) (h : Agree support p q) : d558 p = d558 q := by
  simp only [d558, h 133 (by decide), agree557 p q h, agree541 p q h]
theorem nonnegative558 (p : Pattern) : 0 ≤ d558 p :=
  nonnegative_ite (p 133) (nonnegative557 p) (nonnegative541 p)
def d559 (p : Pattern) : Int := if p 134 then d552 p else d541 p
theorem agree559 (p q : Pattern) (h : Agree support p q) : d559 p = d559 q := by
  simp only [d559, h 134 (by decide), agree552 p q h, agree541 p q h]
theorem nonnegative559 (p : Pattern) : 0 ≤ d559 p :=
  nonnegative_ite (p 134) (nonnegative552 p) (nonnegative541 p)
def d560 (p : Pattern) : Int := if p 133 then d557 p else d559 p
theorem agree560 (p q : Pattern) (h : Agree support p q) : d560 p = d560 q := by
  simp only [d560, h 133 (by decide), agree557 p q h, agree559 p q h]
theorem nonnegative560 (p : Pattern) : 0 ≤ d560 p :=
  nonnegative_ite (p 133) (nonnegative557 p) (nonnegative559 p)
def d561 (p : Pattern) : Int := if p 132 then d560 p else d558 p
theorem agree561 (p q : Pattern) (h : Agree support p q) : d561 p = d561 q := by
  simp only [d561, h 132 (by decide), agree560 p q h, agree558 p q h]
theorem nonnegative561 (p : Pattern) : 0 ≤ d561 p :=
  nonnegative_ite (p 132) (nonnegative560 p) (nonnegative558 p)
def d562 (p : Pattern) : Int := if p 139 then d2 p else d539 p
theorem agree562 (p q : Pattern) (h : Agree support p q) : d562 p = d562 q := by
  simp only [d562, h 139 (by decide), agree2 p q h, agree539 p q h]
theorem nonnegative562 (p : Pattern) : 0 ≤ d562 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative539 p)
def d563 (p : Pattern) : Int := if p 138 then d562 p else d541 p
theorem agree563 (p q : Pattern) (h : Agree support p q) : d563 p = d563 q := by
  simp only [d563, h 138 (by decide), agree562 p q h, agree541 p q h]
theorem nonnegative563 (p : Pattern) : 0 ≤ d563 p :=
  nonnegative_ite (p 138) (nonnegative562 p) (nonnegative541 p)
def d564 (p : Pattern) : Int := if p 139 then d2 p else d545 p
theorem agree564 (p q : Pattern) (h : Agree support p q) : d564 p = d564 q := by
  simp only [d564, h 139 (by decide), agree2 p q h, agree545 p q h]
theorem nonnegative564 (p : Pattern) : 0 ≤ d564 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative545 p)
def d565 (p : Pattern) : Int := if p 138 then d564 p else d547 p
theorem agree565 (p q : Pattern) (h : Agree support p q) : d565 p = d565 q := by
  simp only [d565, h 138 (by decide), agree564 p q h, agree547 p q h]
theorem nonnegative565 (p : Pattern) : 0 ≤ d565 p :=
  nonnegative_ite (p 138) (nonnegative564 p) (nonnegative547 p)
def d566 (p : Pattern) : Int := if p 134 then d565 p else d563 p
theorem agree566 (p q : Pattern) (h : Agree support p q) : d566 p = d566 q := by
  simp only [d566, h 134 (by decide), agree565 p q h, agree563 p q h]
theorem nonnegative566 (p : Pattern) : 0 ≤ d566 p :=
  nonnegative_ite (p 134) (nonnegative565 p) (nonnegative563 p)
def d567 (p : Pattern) : Int := if p 133 then d566 p else d563 p
theorem agree567 (p q : Pattern) (h : Agree support p q) : d567 p = d567 q := by
  simp only [d567, h 133 (by decide), agree566 p q h, agree563 p q h]
theorem nonnegative567 (p : Pattern) : 0 ≤ d567 p :=
  nonnegative_ite (p 133) (nonnegative566 p) (nonnegative563 p)
def d568 (p : Pattern) : Int := if p 139 then d2 p else d551 p
theorem agree568 (p q : Pattern) (h : Agree support p q) : d568 p = d568 q := by
  simp only [d568, h 139 (by decide), agree2 p q h, agree551 p q h]
theorem nonnegative568 (p : Pattern) : 0 ≤ d568 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative551 p)
def d569 (p : Pattern) : Int := if p 138 then d568 p else d552 p
theorem agree569 (p q : Pattern) (h : Agree support p q) : d569 p = d569 q := by
  simp only [d569, h 138 (by decide), agree568 p q h, agree552 p q h]
theorem nonnegative569 (p : Pattern) : 0 ≤ d569 p :=
  nonnegative_ite (p 138) (nonnegative568 p) (nonnegative552 p)
def d570 (p : Pattern) : Int := if p 134 then d569 p else d563 p
theorem agree570 (p q : Pattern) (h : Agree support p q) : d570 p = d570 q := by
  simp only [d570, h 134 (by decide), agree569 p q h, agree563 p q h]
theorem nonnegative570 (p : Pattern) : 0 ≤ d570 p :=
  nonnegative_ite (p 134) (nonnegative569 p) (nonnegative563 p)
def d571 (p : Pattern) : Int := if p 133 then d566 p else d570 p
theorem agree571 (p q : Pattern) (h : Agree support p q) : d571 p = d571 q := by
  simp only [d571, h 133 (by decide), agree566 p q h, agree570 p q h]
theorem nonnegative571 (p : Pattern) : 0 ≤ d571 p :=
  nonnegative_ite (p 133) (nonnegative566 p) (nonnegative570 p)
def d572 (p : Pattern) : Int := if p 132 then d571 p else d567 p
theorem agree572 (p q : Pattern) (h : Agree support p q) : d572 p = d572 q := by
  simp only [d572, h 132 (by decide), agree571 p q h, agree567 p q h]
theorem nonnegative572 (p : Pattern) : 0 ≤ d572 p :=
  nonnegative_ite (p 132) (nonnegative571 p) (nonnegative567 p)
def d573 (p : Pattern) : Int := if p 113 then d572 p else d561 p
theorem agree573 (p q : Pattern) (h : Agree support p q) : d573 p = d573 q := by
  simp only [d573, h 113 (by decide), agree572 p q h, agree561 p q h]
theorem nonnegative573 (p : Pattern) : 0 ≤ d573 p :=
  nonnegative_ite (p 113) (nonnegative572 p) (nonnegative561 p)
def d574 (p : Pattern) : Int := if p 112 then d573 p else d556 p
theorem agree574 (p q : Pattern) (h : Agree support p q) : d574 p = d574 q := by
  simp only [d574, h 112 (by decide), agree573 p q h, agree556 p q h]
theorem nonnegative574 (p : Pattern) : 0 ≤ d574 p :=
  nonnegative_ite (p 112) (nonnegative573 p) (nonnegative556 p)
def d575 (p : Pattern) : Int := if p 134 then d548 p else d542 p
theorem agree575 (p q : Pattern) (h : Agree support p q) : d575 p = d575 q := by
  simp only [d575, h 134 (by decide), agree548 p q h, agree542 p q h]
theorem nonnegative575 (p : Pattern) : 0 ≤ d575 p :=
  nonnegative_ite (p 134) (nonnegative548 p) (nonnegative542 p)
def d576 (p : Pattern) : Int := if p 139 then d2 p else d540 p
theorem agree576 (p q : Pattern) (h : Agree support p q) : d576 p = d576 q := by
  simp only [d576, h 139 (by decide), agree2 p q h, agree540 p q h]
theorem nonnegative576 (p : Pattern) : 0 ≤ d576 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative540 p)
def d577 (p : Pattern) : Int := if p 138 then d576 p else d540 p
theorem agree577 (p q : Pattern) (h : Agree support p q) : d577 p = d577 q := by
  simp only [d577, h 138 (by decide), agree576 p q h, agree540 p q h]
theorem nonnegative577 (p : Pattern) : 0 ≤ d577 p :=
  nonnegative_ite (p 138) (nonnegative576 p) (nonnegative540 p)
def d578 (p : Pattern) : Int := if p 139 then d2 p else d546 p
theorem agree578 (p q : Pattern) (h : Agree support p q) : d578 p = d578 q := by
  simp only [d578, h 139 (by decide), agree2 p q h, agree546 p q h]
theorem nonnegative578 (p : Pattern) : 0 ≤ d578 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative546 p)
def d579 (p : Pattern) : Int := if p 138 then d578 p else d546 p
theorem agree579 (p q : Pattern) (h : Agree support p q) : d579 p = d579 q := by
  simp only [d579, h 138 (by decide), agree578 p q h, agree546 p q h]
theorem nonnegative579 (p : Pattern) : 0 ≤ d579 p :=
  nonnegative_ite (p 138) (nonnegative578 p) (nonnegative546 p)
def d580 (p : Pattern) : Int := if p 134 then d579 p else d577 p
theorem agree580 (p q : Pattern) (h : Agree support p q) : d580 p = d580 q := by
  simp only [d580, h 134 (by decide), agree579 p q h, agree577 p q h]
theorem nonnegative580 (p : Pattern) : 0 ≤ d580 p :=
  nonnegative_ite (p 134) (nonnegative579 p) (nonnegative577 p)
def d581 (p : Pattern) : Int := if p 133 then d580 p else d575 p
theorem agree581 (p q : Pattern) (h : Agree support p q) : d581 p = d581 q := by
  simp only [d581, h 133 (by decide), agree580 p q h, agree575 p q h]
theorem nonnegative581 (p : Pattern) : 0 ≤ d581 p :=
  nonnegative_ite (p 133) (nonnegative580 p) (nonnegative575 p)
def d582 (p : Pattern) : Int := if p 132 then d581 p else d550 p
theorem agree582 (p q : Pattern) (h : Agree support p q) : d582 p = d582 q := by
  simp only [d582, h 132 (by decide), agree581 p q h, agree550 p q h]
theorem nonnegative582 (p : Pattern) : 0 ≤ d582 p :=
  nonnegative_ite (p 132) (nonnegative581 p) (nonnegative550 p)
def d583 (p : Pattern) : Int := if p 139 then d539 p else d538 p
theorem agree583 (p q : Pattern) (h : Agree support p q) : d583 p = d583 q := by
  simp only [d583, h 139 (by decide), agree539 p q h, agree538 p q h]
theorem nonnegative583 (p : Pattern) : 0 ≤ d583 p :=
  nonnegative_ite (p 139) (nonnegative539 p) (nonnegative538 p)
def d584 (p : Pattern) : Int := if p 138 then d541 p else d583 p
theorem agree584 (p q : Pattern) (h : Agree support p q) : d584 p = d584 q := by
  simp only [d584, h 138 (by decide), agree541 p q h, agree583 p q h]
theorem nonnegative584 (p : Pattern) : 0 ≤ d584 p :=
  nonnegative_ite (p 138) (nonnegative541 p) (nonnegative583 p)
def d585 (p : Pattern) : Int := if p 134 then d548 p else d584 p
theorem agree585 (p q : Pattern) (h : Agree support p q) : d585 p = d585 q := by
  simp only [d585, h 134 (by decide), agree548 p q h, agree584 p q h]
theorem nonnegative585 (p : Pattern) : 0 ≤ d585 p :=
  nonnegative_ite (p 134) (nonnegative548 p) (nonnegative584 p)
def d586 (p : Pattern) : Int := if p 134 then d578 p else d576 p
theorem agree586 (p q : Pattern) (h : Agree support p q) : d586 p = d586 q := by
  simp only [d586, h 134 (by decide), agree578 p q h, agree576 p q h]
theorem nonnegative586 (p : Pattern) : 0 ≤ d586 p :=
  nonnegative_ite (p 134) (nonnegative578 p) (nonnegative576 p)
def d587 (p : Pattern) : Int := if p 133 then d586 p else d585 p
theorem agree587 (p q : Pattern) (h : Agree support p q) : d587 p = d587 q := by
  simp only [d587, h 133 (by decide), agree586 p q h, agree585 p q h]
theorem nonnegative587 (p : Pattern) : 0 ≤ d587 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative585 p)
def d588 (p : Pattern) : Int := if p 132 then d587 p else d550 p
theorem agree588 (p q : Pattern) (h : Agree support p q) : d588 p = d588 q := by
  simp only [d588, h 132 (by decide), agree587 p q h, agree550 p q h]
theorem nonnegative588 (p : Pattern) : 0 ≤ d588 p :=
  nonnegative_ite (p 132) (nonnegative587 p) (nonnegative550 p)
def d589 (p : Pattern) : Int := if p 113 then d588 p else d582 p
theorem agree589 (p q : Pattern) (h : Agree support p q) : d589 p = d589 q := by
  simp only [d589, h 113 (by decide), agree588 p q h, agree582 p q h]
theorem nonnegative589 (p : Pattern) : 0 ≤ d589 p :=
  nonnegative_ite (p 113) (nonnegative588 p) (nonnegative582 p)
def d590 (p : Pattern) : Int := if p 133 then d586 p else d557 p
theorem agree590 (p q : Pattern) (h : Agree support p q) : d590 p = d590 q := by
  simp only [d590, h 133 (by decide), agree586 p q h, agree557 p q h]
theorem nonnegative590 (p : Pattern) : 0 ≤ d590 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative557 p)
def d591 (p : Pattern) : Int := if p 132 then d590 p else d558 p
theorem agree591 (p q : Pattern) (h : Agree support p q) : d591 p = d591 q := by
  simp only [d591, h 132 (by decide), agree590 p q h, agree558 p q h]
theorem nonnegative591 (p : Pattern) : 0 ≤ d591 p :=
  nonnegative_ite (p 132) (nonnegative590 p) (nonnegative558 p)
def d592 (p : Pattern) : Int := if p 133 then d586 p else d566 p
theorem agree592 (p q : Pattern) (h : Agree support p q) : d592 p = d592 q := by
  simp only [d592, h 133 (by decide), agree586 p q h, agree566 p q h]
theorem nonnegative592 (p : Pattern) : 0 ≤ d592 p :=
  nonnegative_ite (p 133) (nonnegative586 p) (nonnegative566 p)
def d593 (p : Pattern) : Int := if p 132 then d592 p else d567 p
theorem agree593 (p q : Pattern) (h : Agree support p q) : d593 p = d593 q := by
  simp only [d593, h 132 (by decide), agree592 p q h, agree567 p q h]
theorem nonnegative593 (p : Pattern) : 0 ≤ d593 p :=
  nonnegative_ite (p 132) (nonnegative592 p) (nonnegative567 p)
def d594 (p : Pattern) : Int := if p 113 then d593 p else d591 p
theorem agree594 (p q : Pattern) (h : Agree support p q) : d594 p = d594 q := by
  simp only [d594, h 113 (by decide), agree593 p q h, agree591 p q h]
theorem nonnegative594 (p : Pattern) : 0 ≤ d594 p :=
  nonnegative_ite (p 113) (nonnegative593 p) (nonnegative591 p)
def d595 (p : Pattern) : Int := if p 112 then d594 p else d589 p
theorem agree595 (p q : Pattern) (h : Agree support p q) : d595 p = d595 q := by
  simp only [d595, h 112 (by decide), agree594 p q h, agree589 p q h]
theorem nonnegative595 (p : Pattern) : 0 ≤ d595 p :=
  nonnegative_ite (p 112) (nonnegative594 p) (nonnegative589 p)
def d596 (p : Pattern) : Int := if p 106 then d595 p else d574 p
theorem agree596 (p q : Pattern) (h : Agree support p q) : d596 p = d596 q := by
  simp only [d596, h 106 (by decide), agree595 p q h, agree574 p q h]
theorem nonnegative596 (p : Pattern) : 0 ≤ d596 p :=
  nonnegative_ite (p 106) (nonnegative595 p) (nonnegative574 p)
def d597 (p : Pattern) : Int := if p 138 then d562 p else d538 p
theorem agree597 (p q : Pattern) (h : Agree support p q) : d597 p = d597 q := by
  simp only [d597, h 138 (by decide), agree562 p q h, agree538 p q h]
theorem nonnegative597 (p : Pattern) : 0 ≤ d597 p :=
  nonnegative_ite (p 138) (nonnegative562 p) (nonnegative538 p)
def d598 (p : Pattern) : Int := if p 138 then d562 p else d539 p
theorem agree598 (p q : Pattern) (h : Agree support p q) : d598 p = d598 q := by
  simp only [d598, h 138 (by decide), agree562 p q h, agree539 p q h]
theorem nonnegative598 (p : Pattern) : 0 ≤ d598 p :=
  nonnegative_ite (p 138) (nonnegative562 p) (nonnegative539 p)
def d599 (p : Pattern) : Int := if p 134 then d598 p else d597 p
theorem agree599 (p q : Pattern) (h : Agree support p q) : d599 p = d599 q := by
  simp only [d599, h 134 (by decide), agree598 p q h, agree597 p q h]
theorem nonnegative599 (p : Pattern) : 0 ≤ d599 p :=
  nonnegative_ite (p 134) (nonnegative598 p) (nonnegative597 p)
end NetHack.Sokoban32Refined
