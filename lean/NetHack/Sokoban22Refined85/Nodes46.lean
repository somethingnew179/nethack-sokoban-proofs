/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes45
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d5520 (p : Pattern) : Int := if p 138 then d5519 p else d5518 p
theorem agree5520 (p q : Pattern) (h : Agree support p q) : d5520 p = d5520 q := by
  simp only [d5520, h 138 (by decide), agree5519 p q h, agree5518 p q h]
theorem nonnegative5520 (p : Pattern) : 0 ≤ d5520 p :=
  nonnegative_ite (p 138) (nonnegative5519 p) (nonnegative5518 p)
def d5521 (p : Pattern) : Int := if p 138 then d12 p else d5519 p
theorem agree5521 (p q : Pattern) (h : Agree support p q) : d5521 p = d5521 q := by
  simp only [d5521, h 138 (by decide), agree12 p q h, agree5519 p q h]
theorem nonnegative5521 (p : Pattern) : 0 ≤ d5521 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5519 p)
def d5522 (p : Pattern) : Int := if p 116 then d5521 p else d5520 p
theorem agree5522 (p q : Pattern) (h : Agree support p q) : d5522 p = d5522 q := by
  simp only [d5522, h 116 (by decide), agree5521 p q h, agree5520 p q h]
theorem nonnegative5522 (p : Pattern) : 0 ≤ d5522 p :=
  nonnegative_ite (p 116) (nonnegative5521 p) (nonnegative5520 p)
def d5523 (p : Pattern) : Int := if p 115 then d5522 p else d5508 p
theorem agree5523 (p q : Pattern) (h : Agree support p q) : d5523 p = d5523 q := by
  simp only [d5523, h 115 (by decide), agree5522 p q h, agree5508 p q h]
theorem nonnegative5523 (p : Pattern) : 0 ≤ d5523 p :=
  nonnegative_ite (p 115) (nonnegative5522 p) (nonnegative5508 p)
def d5524 (p : Pattern) : Int := if p 71 then d5523 p else d5511 p
theorem agree5524 (p q : Pattern) (h : Agree support p q) : d5524 p = d5524 q := by
  simp only [d5524, h 71 (by decide), agree5523 p q h, agree5511 p q h]
theorem nonnegative5524 (p : Pattern) : 0 ≤ d5524 p :=
  nonnegative_ite (p 71) (nonnegative5523 p) (nonnegative5511 p)
def d5525 (p : Pattern) : Int := if p 138 then d5512 p else d4578 p
theorem agree5525 (p q : Pattern) (h : Agree support p q) : d5525 p = d5525 q := by
  simp only [d5525, h 138 (by decide), agree5512 p q h, agree4578 p q h]
theorem nonnegative5525 (p : Pattern) : 0 ≤ d5525 p :=
  nonnegative_ite (p 138) (nonnegative5512 p) (nonnegative4578 p)
def d5526 (p : Pattern) : Int := if p 116 then d5514 p else d5525 p
theorem agree5526 (p q : Pattern) (h : Agree support p q) : d5526 p = d5526 q := by
  simp only [d5526, h 116 (by decide), agree5514 p q h, agree5525 p q h]
theorem nonnegative5526 (p : Pattern) : 0 ≤ d5526 p :=
  nonnegative_ite (p 116) (nonnegative5514 p) (nonnegative5525 p)
def d5527 (p : Pattern) : Int := if p 141 then d4589 p else d4585 p
theorem agree5527 (p q : Pattern) (h : Agree support p q) : d5527 p = d5527 q := by
  simp only [d5527, h 141 (by decide), agree4589 p q h, agree4585 p q h]
theorem nonnegative5527 (p : Pattern) : 0 ≤ d5527 p :=
  nonnegative_ite (p 141) (nonnegative4589 p) (nonnegative4585 p)
def d5528 (p : Pattern) : Int := if p 141 then d4596 p else d4531 p
theorem agree5528 (p q : Pattern) (h : Agree support p q) : d5528 p = d5528 q := by
  simp only [d5528, h 141 (by decide), agree4596 p q h, agree4531 p q h]
theorem nonnegative5528 (p : Pattern) : 0 ≤ d5528 p :=
  nonnegative_ite (p 141) (nonnegative4596 p) (nonnegative4531 p)
def d5529 (p : Pattern) : Int := if p 138 then d5528 p else d5527 p
theorem agree5529 (p q : Pattern) (h : Agree support p q) : d5529 p = d5529 q := by
  simp only [d5529, h 138 (by decide), agree5528 p q h, agree5527 p q h]
theorem nonnegative5529 (p : Pattern) : 0 ≤ d5529 p :=
  nonnegative_ite (p 138) (nonnegative5528 p) (nonnegative5527 p)
def d5530 (p : Pattern) : Int := if p 141 then d4596 p else d4607 p
theorem agree5530 (p q : Pattern) (h : Agree support p q) : d5530 p = d5530 q := by
  simp only [d5530, h 141 (by decide), agree4596 p q h, agree4607 p q h]
theorem nonnegative5530 (p : Pattern) : 0 ≤ d5530 p :=
  nonnegative_ite (p 141) (nonnegative4596 p) (nonnegative4607 p)
def d5531 (p : Pattern) : Int := if p 138 then d12 p else d5530 p
theorem agree5531 (p q : Pattern) (h : Agree support p q) : d5531 p = d5531 q := by
  simp only [d5531, h 138 (by decide), agree12 p q h, agree5530 p q h]
theorem nonnegative5531 (p : Pattern) : 0 ≤ d5531 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative5530 p)
def d5532 (p : Pattern) : Int := if p 116 then d5531 p else d5529 p
theorem agree5532 (p q : Pattern) (h : Agree support p q) : d5532 p = d5532 q := by
  simp only [d5532, h 116 (by decide), agree5531 p q h, agree5529 p q h]
theorem nonnegative5532 (p : Pattern) : 0 ≤ d5532 p :=
  nonnegative_ite (p 116) (nonnegative5531 p) (nonnegative5529 p)
def d5533 (p : Pattern) : Int := if p 115 then d5532 p else d5526 p
theorem agree5533 (p q : Pattern) (h : Agree support p q) : d5533 p = d5533 q := by
  simp only [d5533, h 115 (by decide), agree5532 p q h, agree5526 p q h]
theorem nonnegative5533 (p : Pattern) : 0 ≤ d5533 p :=
  nonnegative_ite (p 115) (nonnegative5532 p) (nonnegative5526 p)
def d5534 (p : Pattern) : Int := if p 71 then d5533 p else d5511 p
theorem agree5534 (p q : Pattern) (h : Agree support p q) : d5534 p = d5534 q := by
  simp only [d5534, h 71 (by decide), agree5533 p q h, agree5511 p q h]
theorem nonnegative5534 (p : Pattern) : 0 ≤ d5534 p :=
  nonnegative_ite (p 71) (nonnegative5533 p) (nonnegative5511 p)
def d5535 (p : Pattern) : Int := if p 49 then d5534 p else d5524 p
theorem agree5535 (p q : Pattern) (h : Agree support p q) : d5535 p = d5535 q := by
  simp only [d5535, h 49 (by decide), agree5534 p q h, agree5524 p q h]
theorem nonnegative5535 (p : Pattern) : 0 ≤ d5535 p :=
  nonnegative_ite (p 49) (nonnegative5534 p) (nonnegative5524 p)
def d5536 (p : Pattern) : Int := if p 48 then d5535 p else d5517 p
theorem agree5536 (p q : Pattern) (h : Agree support p q) : d5536 p = d5536 q := by
  simp only [d5536, h 48 (by decide), agree5535 p q h, agree5517 p q h]
theorem nonnegative5536 (p : Pattern) : 0 ≤ d5536 p :=
  nonnegative_ite (p 48) (nonnegative5535 p) (nonnegative5517 p)
def d5537 (p : Pattern) : Int := if p 204 then d0 p else d5502 p
theorem agree5537 (p q : Pattern) (h : Agree support p q) : d5537 p = d5537 q := by
  simp only [d5537, h 204 (by decide), agree0 p q h, agree5502 p q h]
theorem nonnegative5537 (p : Pattern) : 0 ≤ d5537 p :=
  nonnegative_ite (p 204) (nonnegative0 p) (nonnegative5502 p)
def d5538 (p : Pattern) : Int := if p 224 then d5502 p else d0 p
theorem agree5538 (p q : Pattern) (h : Agree support p q) : d5538 p = d5538 q := by
  simp only [d5538, h 224 (by decide), agree5502 p q h, agree0 p q h]
theorem nonnegative5538 (p : Pattern) : 0 ≤ d5538 p :=
  nonnegative_ite (p 224) (nonnegative5502 p) (nonnegative0 p)
def d5539 (p : Pattern) : Int := if p 224 then d0 p else d5268 p
theorem agree5539 (p q : Pattern) (h : Agree support p q) : d5539 p = d5539 q := by
  simp only [d5539, h 224 (by decide), agree0 p q h, agree5268 p q h]
theorem nonnegative5539 (p : Pattern) : 0 ≤ d5539 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5268 p)
def d5540 (p : Pattern) : Int := if p 224 then d0 p else d5501 p
theorem agree5540 (p q : Pattern) (h : Agree support p q) : d5540 p = d5540 q := by
  simp only [d5540, h 224 (by decide), agree0 p q h, agree5501 p q h]
theorem nonnegative5540 (p : Pattern) : 0 ≤ d5540 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5501 p)
def d5541 (p : Pattern) : Int := if p 224 then d1770 p else d14 p
theorem agree5541 (p q : Pattern) (h : Agree support p q) : d5541 p = d5541 q := by
  simp only [d5541, h 224 (by decide), agree1770 p q h, agree14 p q h]
theorem nonnegative5541 (p : Pattern) : 0 ≤ d5541 p :=
  nonnegative_ite (p 224) (nonnegative1770 p) (nonnegative14 p)
def d5542 (p : Pattern) : Int := if p 204 then d5541 p else d14 p
theorem agree5542 (p q : Pattern) (h : Agree support p q) : d5542 p = d5542 q := by
  simp only [d5542, h 204 (by decide), agree5541 p q h, agree14 p q h]
theorem nonnegative5542 (p : Pattern) : 0 ≤ d5542 p :=
  nonnegative_ite (p 204) (nonnegative5541 p) (nonnegative14 p)
def d5543 (p : Pattern) : Int := if p 224 then d1684 p else d14 p
theorem agree5543 (p q : Pattern) (h : Agree support p q) : d5543 p = d5543 q := by
  simp only [d5543, h 224 (by decide), agree1684 p q h, agree14 p q h]
theorem nonnegative5543 (p : Pattern) : 0 ≤ d5543 p :=
  nonnegative_ite (p 224) (nonnegative1684 p) (nonnegative14 p)
def d5544 (p : Pattern) : Int := if p 204 then d12 p else d5543 p
theorem agree5544 (p q : Pattern) (h : Agree support p q) : d5544 p = d5544 q := by
  simp only [d5544, h 204 (by decide), agree12 p q h, agree5543 p q h]
theorem nonnegative5544 (p : Pattern) : 0 ≤ d5544 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5543 p)
def d5545 (p : Pattern) : Int := if p 182 then d5544 p else d5542 p
theorem agree5545 (p q : Pattern) (h : Agree support p q) : d5545 p = d5545 q := by
  simp only [d5545, h 182 (by decide), agree5544 p q h, agree5542 p q h]
theorem nonnegative5545 (p : Pattern) : 0 ≤ d5545 p :=
  nonnegative_ite (p 182) (nonnegative5544 p) (nonnegative5542 p)
def d5546 (p : Pattern) : Int := if p 224 then d1795 p else d18 p
theorem agree5546 (p q : Pattern) (h : Agree support p q) : d5546 p = d5546 q := by
  simp only [d5546, h 224 (by decide), agree1795 p q h, agree18 p q h]
theorem nonnegative5546 (p : Pattern) : 0 ≤ d5546 p :=
  nonnegative_ite (p 224) (nonnegative1795 p) (nonnegative18 p)
def d5547 (p : Pattern) : Int := if p 204 then d5546 p else d18 p
theorem agree5547 (p q : Pattern) (h : Agree support p q) : d5547 p = d5547 q := by
  simp only [d5547, h 204 (by decide), agree5546 p q h, agree18 p q h]
theorem nonnegative5547 (p : Pattern) : 0 ≤ d5547 p :=
  nonnegative_ite (p 204) (nonnegative5546 p) (nonnegative18 p)
def d5548 (p : Pattern) : Int := if p 224 then d1694 p else d18 p
theorem agree5548 (p q : Pattern) (h : Agree support p q) : d5548 p = d5548 q := by
  simp only [d5548, h 224 (by decide), agree1694 p q h, agree18 p q h]
theorem nonnegative5548 (p : Pattern) : 0 ≤ d5548 p :=
  nonnegative_ite (p 224) (nonnegative1694 p) (nonnegative18 p)
def d5549 (p : Pattern) : Int := if p 204 then d12 p else d5548 p
theorem agree5549 (p q : Pattern) (h : Agree support p q) : d5549 p = d5549 q := by
  simp only [d5549, h 204 (by decide), agree12 p q h, agree5548 p q h]
theorem nonnegative5549 (p : Pattern) : 0 ≤ d5549 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5548 p)
def d5550 (p : Pattern) : Int := if p 182 then d5549 p else d5547 p
theorem agree5550 (p q : Pattern) (h : Agree support p q) : d5550 p = d5550 q := by
  simp only [d5550, h 182 (by decide), agree5549 p q h, agree5547 p q h]
theorem nonnegative5550 (p : Pattern) : 0 ≤ d5550 p :=
  nonnegative_ite (p 182) (nonnegative5549 p) (nonnegative5547 p)
def d5551 (p : Pattern) : Int := if p 163 then d5550 p else d5545 p
theorem agree5551 (p q : Pattern) (h : Agree support p q) : d5551 p = d5551 q := by
  simp only [d5551, h 163 (by decide), agree5550 p q h, agree5545 p q h]
theorem nonnegative5551 (p : Pattern) : 0 ≤ d5551 p :=
  nonnegative_ite (p 163) (nonnegative5550 p) (nonnegative5545 p)
def d5552 (p : Pattern) : Int := if p 162 then d5551 p else d5545 p
theorem agree5552 (p q : Pattern) (h : Agree support p q) : d5552 p = d5552 q := by
  simp only [d5552, h 162 (by decide), agree5551 p q h, agree5545 p q h]
theorem nonnegative5552 (p : Pattern) : 0 ≤ d5552 p :=
  nonnegative_ite (p 162) (nonnegative5551 p) (nonnegative5545 p)
def d5553 (p : Pattern) : Int := if p 224 then d356 p else d24 p
theorem agree5553 (p q : Pattern) (h : Agree support p q) : d5553 p = d5553 q := by
  simp only [d5553, h 224 (by decide), agree356 p q h, agree24 p q h]
theorem nonnegative5553 (p : Pattern) : 0 ≤ d5553 p :=
  nonnegative_ite (p 224) (nonnegative356 p) (nonnegative24 p)
def d5554 (p : Pattern) : Int := if p 204 then d5553 p else d24 p
theorem agree5554 (p q : Pattern) (h : Agree support p q) : d5554 p = d5554 q := by
  simp only [d5554, h 204 (by decide), agree5553 p q h, agree24 p q h]
theorem nonnegative5554 (p : Pattern) : 0 ≤ d5554 p :=
  nonnegative_ite (p 204) (nonnegative5553 p) (nonnegative24 p)
def d5555 (p : Pattern) : Int := if p 224 then d1702 p else d24 p
theorem agree5555 (p q : Pattern) (h : Agree support p q) : d5555 p = d5555 q := by
  simp only [d5555, h 224 (by decide), agree1702 p q h, agree24 p q h]
theorem nonnegative5555 (p : Pattern) : 0 ≤ d5555 p :=
  nonnegative_ite (p 224) (nonnegative1702 p) (nonnegative24 p)
def d5556 (p : Pattern) : Int := if p 204 then d12 p else d5555 p
theorem agree5556 (p q : Pattern) (h : Agree support p q) : d5556 p = d5556 q := by
  simp only [d5556, h 204 (by decide), agree12 p q h, agree5555 p q h]
theorem nonnegative5556 (p : Pattern) : 0 ≤ d5556 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5555 p)
def d5557 (p : Pattern) : Int := if p 182 then d5556 p else d5554 p
theorem agree5557 (p q : Pattern) (h : Agree support p q) : d5557 p = d5557 q := by
  simp only [d5557, h 182 (by decide), agree5556 p q h, agree5554 p q h]
theorem nonnegative5557 (p : Pattern) : 0 ≤ d5557 p :=
  nonnegative_ite (p 182) (nonnegative5556 p) (nonnegative5554 p)
def d5558 (p : Pattern) : Int := if p 163 then d12 p else d5557 p
theorem agree5558 (p q : Pattern) (h : Agree support p q) : d5558 p = d5558 q := by
  simp only [d5558, h 163 (by decide), agree12 p q h, agree5557 p q h]
theorem nonnegative5558 (p : Pattern) : 0 ≤ d5558 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5557 p)
def d5559 (p : Pattern) : Int := if p 162 then d5558 p else d5551 p
theorem agree5559 (p q : Pattern) (h : Agree support p q) : d5559 p = d5559 q := by
  simp only [d5559, h 162 (by decide), agree5558 p q h, agree5551 p q h]
theorem nonnegative5559 (p : Pattern) : 0 ≤ d5559 p :=
  nonnegative_ite (p 162) (nonnegative5558 p) (nonnegative5551 p)
def d5560 (p : Pattern) : Int := if p 161 then d5559 p else d5552 p
theorem agree5560 (p q : Pattern) (h : Agree support p q) : d5560 p = d5560 q := by
  simp only [d5560, h 161 (by decide), agree5559 p q h, agree5552 p q h]
theorem nonnegative5560 (p : Pattern) : 0 ≤ d5560 p :=
  nonnegative_ite (p 161) (nonnegative5559 p) (nonnegative5552 p)
def d5561 (p : Pattern) : Int := if p 224 then d1714 p else d31 p
theorem agree5561 (p q : Pattern) (h : Agree support p q) : d5561 p = d5561 q := by
  simp only [d5561, h 224 (by decide), agree1714 p q h, agree31 p q h]
theorem nonnegative5561 (p : Pattern) : 0 ≤ d5561 p :=
  nonnegative_ite (p 224) (nonnegative1714 p) (nonnegative31 p)
def d5562 (p : Pattern) : Int := if p 204 then d12 p else d5561 p
theorem agree5562 (p q : Pattern) (h : Agree support p q) : d5562 p = d5562 q := by
  simp only [d5562, h 204 (by decide), agree12 p q h, agree5561 p q h]
theorem nonnegative5562 (p : Pattern) : 0 ≤ d5562 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5561 p)
def d5563 (p : Pattern) : Int := if p 182 then d5562 p else d5542 p
theorem agree5563 (p q : Pattern) (h : Agree support p q) : d5563 p = d5563 q := by
  simp only [d5563, h 182 (by decide), agree5562 p q h, agree5542 p q h]
theorem nonnegative5563 (p : Pattern) : 0 ≤ d5563 p :=
  nonnegative_ite (p 182) (nonnegative5562 p) (nonnegative5542 p)
def d5564 (p : Pattern) : Int := if p 224 then d1722 p else d35 p
theorem agree5564 (p q : Pattern) (h : Agree support p q) : d5564 p = d5564 q := by
  simp only [d5564, h 224 (by decide), agree1722 p q h, agree35 p q h]
theorem nonnegative5564 (p : Pattern) : 0 ≤ d5564 p :=
  nonnegative_ite (p 224) (nonnegative1722 p) (nonnegative35 p)
def d5565 (p : Pattern) : Int := if p 204 then d12 p else d5564 p
theorem agree5565 (p q : Pattern) (h : Agree support p q) : d5565 p = d5565 q := by
  simp only [d5565, h 204 (by decide), agree12 p q h, agree5564 p q h]
theorem nonnegative5565 (p : Pattern) : 0 ≤ d5565 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5564 p)
def d5566 (p : Pattern) : Int := if p 182 then d5565 p else d5542 p
theorem agree5566 (p q : Pattern) (h : Agree support p q) : d5566 p = d5566 q := by
  simp only [d5566, h 182 (by decide), agree5565 p q h, agree5542 p q h]
theorem nonnegative5566 (p : Pattern) : 0 ≤ d5566 p :=
  nonnegative_ite (p 182) (nonnegative5565 p) (nonnegative5542 p)
def d5567 (p : Pattern) : Int := if p 163 then d5566 p else d5563 p
theorem agree5567 (p q : Pattern) (h : Agree support p q) : d5567 p = d5567 q := by
  simp only [d5567, h 163 (by decide), agree5566 p q h, agree5563 p q h]
theorem nonnegative5567 (p : Pattern) : 0 ≤ d5567 p :=
  nonnegative_ite (p 163) (nonnegative5566 p) (nonnegative5563 p)
def d5568 (p : Pattern) : Int := if p 224 then d327 p else d40 p
theorem agree5568 (p q : Pattern) (h : Agree support p q) : d5568 p = d5568 q := by
  simp only [d5568, h 224 (by decide), agree327 p q h, agree40 p q h]
theorem nonnegative5568 (p : Pattern) : 0 ≤ d5568 p :=
  nonnegative_ite (p 224) (nonnegative327 p) (nonnegative40 p)
def d5569 (p : Pattern) : Int := if p 204 then d12 p else d5568 p
theorem agree5569 (p q : Pattern) (h : Agree support p q) : d5569 p = d5569 q := by
  simp only [d5569, h 204 (by decide), agree12 p q h, agree5568 p q h]
theorem nonnegative5569 (p : Pattern) : 0 ≤ d5569 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5568 p)
def d5570 (p : Pattern) : Int := if p 182 then d5569 p else d5542 p
theorem agree5570 (p q : Pattern) (h : Agree support p q) : d5570 p = d5570 q := by
  simp only [d5570, h 182 (by decide), agree5569 p q h, agree5542 p q h]
theorem nonnegative5570 (p : Pattern) : 0 ≤ d5570 p :=
  nonnegative_ite (p 182) (nonnegative5569 p) (nonnegative5542 p)
def d5571 (p : Pattern) : Int := if p 182 then d12 p else d5547 p
theorem agree5571 (p q : Pattern) (h : Agree support p q) : d5571 p = d5571 q := by
  simp only [d5571, h 182 (by decide), agree12 p q h, agree5547 p q h]
theorem nonnegative5571 (p : Pattern) : 0 ≤ d5571 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5547 p)
def d5572 (p : Pattern) : Int := if p 163 then d5571 p else d5570 p
theorem agree5572 (p q : Pattern) (h : Agree support p q) : d5572 p = d5572 q := by
  simp only [d5572, h 163 (by decide), agree5571 p q h, agree5570 p q h]
theorem nonnegative5572 (p : Pattern) : 0 ≤ d5572 p :=
  nonnegative_ite (p 163) (nonnegative5571 p) (nonnegative5570 p)
def d5573 (p : Pattern) : Int := if p 162 then d5572 p else d5567 p
theorem agree5573 (p q : Pattern) (h : Agree support p q) : d5573 p = d5573 q := by
  simp only [d5573, h 162 (by decide), agree5572 p q h, agree5567 p q h]
theorem nonnegative5573 (p : Pattern) : 0 ≤ d5573 p :=
  nonnegative_ite (p 162) (nonnegative5572 p) (nonnegative5567 p)
def d5574 (p : Pattern) : Int := if p 182 then d12 p else d5542 p
theorem agree5574 (p q : Pattern) (h : Agree support p q) : d5574 p = d5574 q := by
  simp only [d5574, h 182 (by decide), agree12 p q h, agree5542 p q h]
theorem nonnegative5574 (p : Pattern) : 0 ≤ d5574 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5542 p)
def d5575 (p : Pattern) : Int := if p 163 then d5571 p else d5574 p
theorem agree5575 (p q : Pattern) (h : Agree support p q) : d5575 p = d5575 q := by
  simp only [d5575, h 163 (by decide), agree5571 p q h, agree5574 p q h]
theorem nonnegative5575 (p : Pattern) : 0 ≤ d5575 p :=
  nonnegative_ite (p 163) (nonnegative5571 p) (nonnegative5574 p)
def d5576 (p : Pattern) : Int := if p 182 then d12 p else d5554 p
theorem agree5576 (p q : Pattern) (h : Agree support p q) : d5576 p = d5576 q := by
  simp only [d5576, h 182 (by decide), agree12 p q h, agree5554 p q h]
theorem nonnegative5576 (p : Pattern) : 0 ≤ d5576 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5554 p)
def d5577 (p : Pattern) : Int := if p 163 then d12 p else d5576 p
theorem agree5577 (p q : Pattern) (h : Agree support p q) : d5577 p = d5577 q := by
  simp only [d5577, h 163 (by decide), agree12 p q h, agree5576 p q h]
theorem nonnegative5577 (p : Pattern) : 0 ≤ d5577 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5576 p)
def d5578 (p : Pattern) : Int := if p 162 then d5577 p else d5575 p
theorem agree5578 (p q : Pattern) (h : Agree support p q) : d5578 p = d5578 q := by
  simp only [d5578, h 162 (by decide), agree5577 p q h, agree5575 p q h]
theorem nonnegative5578 (p : Pattern) : 0 ≤ d5578 p :=
  nonnegative_ite (p 162) (nonnegative5577 p) (nonnegative5575 p)
def d5579 (p : Pattern) : Int := if p 161 then d5578 p else d5573 p
theorem agree5579 (p q : Pattern) (h : Agree support p q) : d5579 p = d5579 q := by
  simp only [d5579, h 161 (by decide), agree5578 p q h, agree5573 p q h]
theorem nonnegative5579 (p : Pattern) : 0 ≤ d5579 p :=
  nonnegative_ite (p 161) (nonnegative5578 p) (nonnegative5573 p)
def d5580 (p : Pattern) : Int := if p 160 then d5579 p else d5560 p
theorem agree5580 (p q : Pattern) (h : Agree support p q) : d5580 p = d5580 q := by
  simp only [d5580, h 160 (by decide), agree5579 p q h, agree5560 p q h]
theorem nonnegative5580 (p : Pattern) : 0 ≤ d5580 p :=
  nonnegative_ite (p 160) (nonnegative5579 p) (nonnegative5560 p)
def d5581 (p : Pattern) : Int := if p 204 then d5561 p else d31 p
theorem agree5581 (p q : Pattern) (h : Agree support p q) : d5581 p = d5581 q := by
  simp only [d5581, h 204 (by decide), agree5561 p q h, agree31 p q h]
theorem nonnegative5581 (p : Pattern) : 0 ≤ d5581 p :=
  nonnegative_ite (p 204) (nonnegative5561 p) (nonnegative31 p)
def d5582 (p : Pattern) : Int := if p 224 then d1743 p else d31 p
theorem agree5582 (p q : Pattern) (h : Agree support p q) : d5582 p = d5582 q := by
  simp only [d5582, h 224 (by decide), agree1743 p q h, agree31 p q h]
theorem nonnegative5582 (p : Pattern) : 0 ≤ d5582 p :=
  nonnegative_ite (p 224) (nonnegative1743 p) (nonnegative31 p)
def d5583 (p : Pattern) : Int := if p 204 then d12 p else d5582 p
theorem agree5583 (p q : Pattern) (h : Agree support p q) : d5583 p = d5583 q := by
  simp only [d5583, h 204 (by decide), agree12 p q h, agree5582 p q h]
theorem nonnegative5583 (p : Pattern) : 0 ≤ d5583 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5582 p)
def d5584 (p : Pattern) : Int := if p 182 then d5583 p else d5581 p
theorem agree5584 (p q : Pattern) (h : Agree support p q) : d5584 p = d5584 q := by
  simp only [d5584, h 182 (by decide), agree5583 p q h, agree5581 p q h]
theorem nonnegative5584 (p : Pattern) : 0 ≤ d5584 p :=
  nonnegative_ite (p 182) (nonnegative5583 p) (nonnegative5581 p)
def d5585 (p : Pattern) : Int := if p 163 then d5584 p else d5545 p
theorem agree5585 (p q : Pattern) (h : Agree support p q) : d5585 p = d5585 q := by
  simp only [d5585, h 163 (by decide), agree5584 p q h, agree5545 p q h]
theorem nonnegative5585 (p : Pattern) : 0 ≤ d5585 p :=
  nonnegative_ite (p 163) (nonnegative5584 p) (nonnegative5545 p)
def d5586 (p : Pattern) : Int := if p 163 then d5557 p else d5550 p
theorem agree5586 (p q : Pattern) (h : Agree support p q) : d5586 p = d5586 q := by
  simp only [d5586, h 163 (by decide), agree5557 p q h, agree5550 p q h]
theorem nonnegative5586 (p : Pattern) : 0 ≤ d5586 p :=
  nonnegative_ite (p 163) (nonnegative5557 p) (nonnegative5550 p)
def d5587 (p : Pattern) : Int := if p 162 then d5586 p else d5585 p
theorem agree5587 (p q : Pattern) (h : Agree support p q) : d5587 p = d5587 q := by
  simp only [d5587, h 162 (by decide), agree5586 p q h, agree5585 p q h]
theorem nonnegative5587 (p : Pattern) : 0 ≤ d5587 p :=
  nonnegative_ite (p 162) (nonnegative5586 p) (nonnegative5585 p)
def d5588 (p : Pattern) : Int := if p 224 then d329 p else d58 p
theorem agree5588 (p q : Pattern) (h : Agree support p q) : d5588 p = d5588 q := by
  simp only [d5588, h 224 (by decide), agree329 p q h, agree58 p q h]
theorem nonnegative5588 (p : Pattern) : 0 ≤ d5588 p :=
  nonnegative_ite (p 224) (nonnegative329 p) (nonnegative58 p)
def d5589 (p : Pattern) : Int := if p 204 then d5588 p else d58 p
theorem agree5589 (p q : Pattern) (h : Agree support p q) : d5589 p = d5589 q := by
  simp only [d5589, h 204 (by decide), agree5588 p q h, agree58 p q h]
theorem nonnegative5589 (p : Pattern) : 0 ≤ d5589 p :=
  nonnegative_ite (p 204) (nonnegative5588 p) (nonnegative58 p)
def d5590 (p : Pattern) : Int := if p 204 then d12 p else d5588 p
theorem agree5590 (p q : Pattern) (h : Agree support p q) : d5590 p = d5590 q := by
  simp only [d5590, h 204 (by decide), agree12 p q h, agree5588 p q h]
theorem nonnegative5590 (p : Pattern) : 0 ≤ d5590 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5588 p)
def d5591 (p : Pattern) : Int := if p 182 then d5590 p else d5589 p
theorem agree5591 (p q : Pattern) (h : Agree support p q) : d5591 p = d5591 q := by
  simp only [d5591, h 182 (by decide), agree5590 p q h, agree5589 p q h]
theorem nonnegative5591 (p : Pattern) : 0 ≤ d5591 p :=
  nonnegative_ite (p 182) (nonnegative5590 p) (nonnegative5589 p)
def d5592 (p : Pattern) : Int := if p 163 then d5591 p else d5550 p
theorem agree5592 (p q : Pattern) (h : Agree support p q) : d5592 p = d5592 q := by
  simp only [d5592, h 163 (by decide), agree5591 p q h, agree5550 p q h]
theorem nonnegative5592 (p : Pattern) : 0 ≤ d5592 p :=
  nonnegative_ite (p 163) (nonnegative5591 p) (nonnegative5550 p)
def d5593 (p : Pattern) : Int := if p 204 then d5568 p else d40 p
theorem agree5593 (p q : Pattern) (h : Agree support p q) : d5593 p = d5593 q := by
  simp only [d5593, h 204 (by decide), agree5568 p q h, agree40 p q h]
theorem nonnegative5593 (p : Pattern) : 0 ≤ d5593 p :=
  nonnegative_ite (p 204) (nonnegative5568 p) (nonnegative40 p)
def d5594 (p : Pattern) : Int := if p 182 then d5569 p else d5593 p
theorem agree5594 (p q : Pattern) (h : Agree support p q) : d5594 p = d5594 q := by
  simp only [d5594, h 182 (by decide), agree5569 p q h, agree5593 p q h]
theorem nonnegative5594 (p : Pattern) : 0 ≤ d5594 p :=
  nonnegative_ite (p 182) (nonnegative5569 p) (nonnegative5593 p)
def d5595 (p : Pattern) : Int := if p 163 then d12 p else d5594 p
theorem agree5595 (p q : Pattern) (h : Agree support p q) : d5595 p = d5595 q := by
  simp only [d5595, h 163 (by decide), agree12 p q h, agree5594 p q h]
theorem nonnegative5595 (p : Pattern) : 0 ≤ d5595 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5594 p)
def d5596 (p : Pattern) : Int := if p 162 then d5595 p else d5592 p
theorem agree5596 (p q : Pattern) (h : Agree support p q) : d5596 p = d5596 q := by
  simp only [d5596, h 162 (by decide), agree5595 p q h, agree5592 p q h]
theorem nonnegative5596 (p : Pattern) : 0 ≤ d5596 p :=
  nonnegative_ite (p 162) (nonnegative5595 p) (nonnegative5592 p)
def d5597 (p : Pattern) : Int := if p 161 then d5596 p else d5587 p
theorem agree5597 (p q : Pattern) (h : Agree support p q) : d5597 p = d5597 q := by
  simp only [d5597, h 161 (by decide), agree5596 p q h, agree5587 p q h]
theorem nonnegative5597 (p : Pattern) : 0 ≤ d5597 p :=
  nonnegative_ite (p 161) (nonnegative5596 p) (nonnegative5587 p)
def d5598 (p : Pattern) : Int := if p 182 then d12 p else d5581 p
theorem agree5598 (p q : Pattern) (h : Agree support p q) : d5598 p = d5598 q := by
  simp only [d5598, h 182 (by decide), agree12 p q h, agree5581 p q h]
theorem nonnegative5598 (p : Pattern) : 0 ≤ d5598 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5581 p)
def d5599 (p : Pattern) : Int := if p 163 then d5598 p else d5566 p
theorem agree5599 (p q : Pattern) (h : Agree support p q) : d5599 p = d5599 q := by
  simp only [d5599, h 163 (by decide), agree5598 p q h, agree5566 p q h]
theorem nonnegative5599 (p : Pattern) : 0 ≤ d5599 p :=
  nonnegative_ite (p 163) (nonnegative5598 p) (nonnegative5566 p)
def d5600 (p : Pattern) : Int := if p 163 then d5576 p else d5571 p
theorem agree5600 (p q : Pattern) (h : Agree support p q) : d5600 p = d5600 q := by
  simp only [d5600, h 163 (by decide), agree5576 p q h, agree5571 p q h]
theorem nonnegative5600 (p : Pattern) : 0 ≤ d5600 p :=
  nonnegative_ite (p 163) (nonnegative5576 p) (nonnegative5571 p)
def d5601 (p : Pattern) : Int := if p 162 then d5600 p else d5599 p
theorem agree5601 (p q : Pattern) (h : Agree support p q) : d5601 p = d5601 q := by
  simp only [d5601, h 162 (by decide), agree5600 p q h, agree5599 p q h]
theorem nonnegative5601 (p : Pattern) : 0 ≤ d5601 p :=
  nonnegative_ite (p 162) (nonnegative5600 p) (nonnegative5599 p)
def d5602 (p : Pattern) : Int := if p 182 then d12 p else d5589 p
theorem agree5602 (p q : Pattern) (h : Agree support p q) : d5602 p = d5602 q := by
  simp only [d5602, h 182 (by decide), agree12 p q h, agree5589 p q h]
theorem nonnegative5602 (p : Pattern) : 0 ≤ d5602 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5589 p)
def d5603 (p : Pattern) : Int := if p 163 then d5602 p else d5571 p
theorem agree5603 (p q : Pattern) (h : Agree support p q) : d5603 p = d5603 q := by
  simp only [d5603, h 163 (by decide), agree5602 p q h, agree5571 p q h]
theorem nonnegative5603 (p : Pattern) : 0 ≤ d5603 p :=
  nonnegative_ite (p 163) (nonnegative5602 p) (nonnegative5571 p)
def d5604 (p : Pattern) : Int := if p 182 then d12 p else d5593 p
theorem agree5604 (p q : Pattern) (h : Agree support p q) : d5604 p = d5604 q := by
  simp only [d5604, h 182 (by decide), agree12 p q h, agree5593 p q h]
theorem nonnegative5604 (p : Pattern) : 0 ≤ d5604 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative5593 p)
def d5605 (p : Pattern) : Int := if p 163 then d12 p else d5604 p
theorem agree5605 (p q : Pattern) (h : Agree support p q) : d5605 p = d5605 q := by
  simp only [d5605, h 163 (by decide), agree12 p q h, agree5604 p q h]
theorem nonnegative5605 (p : Pattern) : 0 ≤ d5605 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5604 p)
def d5606 (p : Pattern) : Int := if p 162 then d5605 p else d5603 p
theorem agree5606 (p q : Pattern) (h : Agree support p q) : d5606 p = d5606 q := by
  simp only [d5606, h 162 (by decide), agree5605 p q h, agree5603 p q h]
theorem nonnegative5606 (p : Pattern) : 0 ≤ d5606 p :=
  nonnegative_ite (p 162) (nonnegative5605 p) (nonnegative5603 p)
def d5607 (p : Pattern) : Int := if p 161 then d5606 p else d5601 p
theorem agree5607 (p q : Pattern) (h : Agree support p q) : d5607 p = d5607 q := by
  simp only [d5607, h 161 (by decide), agree5606 p q h, agree5601 p q h]
theorem nonnegative5607 (p : Pattern) : 0 ≤ d5607 p :=
  nonnegative_ite (p 161) (nonnegative5606 p) (nonnegative5601 p)
def d5608 (p : Pattern) : Int := if p 160 then d5607 p else d5597 p
theorem agree5608 (p q : Pattern) (h : Agree support p q) : d5608 p = d5608 q := by
  simp only [d5608, h 160 (by decide), agree5607 p q h, agree5597 p q h]
theorem nonnegative5608 (p : Pattern) : 0 ≤ d5608 p :=
  nonnegative_ite (p 160) (nonnegative5607 p) (nonnegative5597 p)
def d5609 (p : Pattern) : Int := if p 141 then d5608 p else d5580 p
theorem agree5609 (p q : Pattern) (h : Agree support p q) : d5609 p = d5609 q := by
  simp only [d5609, h 141 (by decide), agree5608 p q h, agree5580 p q h]
theorem nonnegative5609 (p : Pattern) : 0 ≤ d5609 p :=
  nonnegative_ite (p 141) (nonnegative5608 p) (nonnegative5580 p)
def d5610 (p : Pattern) : Int := if p 204 then d12 p else d5541 p
theorem agree5610 (p q : Pattern) (h : Agree support p q) : d5610 p = d5610 q := by
  simp only [d5610, h 204 (by decide), agree12 p q h, agree5541 p q h]
theorem nonnegative5610 (p : Pattern) : 0 ≤ d5610 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5541 p)
def d5611 (p : Pattern) : Int := if p 182 then d5610 p else d5542 p
theorem agree5611 (p q : Pattern) (h : Agree support p q) : d5611 p = d5611 q := by
  simp only [d5611, h 182 (by decide), agree5610 p q h, agree5542 p q h]
theorem nonnegative5611 (p : Pattern) : 0 ≤ d5611 p :=
  nonnegative_ite (p 182) (nonnegative5610 p) (nonnegative5542 p)
def d5612 (p : Pattern) : Int := if p 204 then d12 p else d5546 p
theorem agree5612 (p q : Pattern) (h : Agree support p q) : d5612 p = d5612 q := by
  simp only [d5612, h 204 (by decide), agree12 p q h, agree5546 p q h]
theorem nonnegative5612 (p : Pattern) : 0 ≤ d5612 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5546 p)
def d5613 (p : Pattern) : Int := if p 182 then d5612 p else d5547 p
theorem agree5613 (p q : Pattern) (h : Agree support p q) : d5613 p = d5613 q := by
  simp only [d5613, h 182 (by decide), agree5612 p q h, agree5547 p q h]
theorem nonnegative5613 (p : Pattern) : 0 ≤ d5613 p :=
  nonnegative_ite (p 182) (nonnegative5612 p) (nonnegative5547 p)
def d5614 (p : Pattern) : Int := if p 163 then d5613 p else d5611 p
theorem agree5614 (p q : Pattern) (h : Agree support p q) : d5614 p = d5614 q := by
  simp only [d5614, h 163 (by decide), agree5613 p q h, agree5611 p q h]
theorem nonnegative5614 (p : Pattern) : 0 ≤ d5614 p :=
  nonnegative_ite (p 163) (nonnegative5613 p) (nonnegative5611 p)
def d5615 (p : Pattern) : Int := if p 162 then d5614 p else d5611 p
theorem agree5615 (p q : Pattern) (h : Agree support p q) : d5615 p = d5615 q := by
  simp only [d5615, h 162 (by decide), agree5614 p q h, agree5611 p q h]
theorem nonnegative5615 (p : Pattern) : 0 ≤ d5615 p :=
  nonnegative_ite (p 162) (nonnegative5614 p) (nonnegative5611 p)
def d5616 (p : Pattern) : Int := if p 204 then d12 p else d5553 p
theorem agree5616 (p q : Pattern) (h : Agree support p q) : d5616 p = d5616 q := by
  simp only [d5616, h 204 (by decide), agree12 p q h, agree5553 p q h]
theorem nonnegative5616 (p : Pattern) : 0 ≤ d5616 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative5553 p)
def d5617 (p : Pattern) : Int := if p 182 then d5616 p else d5554 p
theorem agree5617 (p q : Pattern) (h : Agree support p q) : d5617 p = d5617 q := by
  simp only [d5617, h 182 (by decide), agree5616 p q h, agree5554 p q h]
theorem nonnegative5617 (p : Pattern) : 0 ≤ d5617 p :=
  nonnegative_ite (p 182) (nonnegative5616 p) (nonnegative5554 p)
def d5618 (p : Pattern) : Int := if p 163 then d12 p else d5617 p
theorem agree5618 (p q : Pattern) (h : Agree support p q) : d5618 p = d5618 q := by
  simp only [d5618, h 163 (by decide), agree12 p q h, agree5617 p q h]
theorem nonnegative5618 (p : Pattern) : 0 ≤ d5618 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5617 p)
def d5619 (p : Pattern) : Int := if p 162 then d5618 p else d5614 p
theorem agree5619 (p q : Pattern) (h : Agree support p q) : d5619 p = d5619 q := by
  simp only [d5619, h 162 (by decide), agree5618 p q h, agree5614 p q h]
theorem nonnegative5619 (p : Pattern) : 0 ≤ d5619 p :=
  nonnegative_ite (p 162) (nonnegative5618 p) (nonnegative5614 p)
def d5620 (p : Pattern) : Int := if p 161 then d5619 p else d5615 p
theorem agree5620 (p q : Pattern) (h : Agree support p q) : d5620 p = d5620 q := by
  simp only [d5620, h 161 (by decide), agree5619 p q h, agree5615 p q h]
theorem nonnegative5620 (p : Pattern) : 0 ≤ d5620 p :=
  nonnegative_ite (p 161) (nonnegative5619 p) (nonnegative5615 p)
def d5621 (p : Pattern) : Int := if p 182 then d5562 p else d5581 p
theorem agree5621 (p q : Pattern) (h : Agree support p q) : d5621 p = d5621 q := by
  simp only [d5621, h 182 (by decide), agree5562 p q h, agree5581 p q h]
theorem nonnegative5621 (p : Pattern) : 0 ≤ d5621 p :=
  nonnegative_ite (p 182) (nonnegative5562 p) (nonnegative5581 p)
def d5622 (p : Pattern) : Int := if p 204 then d5564 p else d35 p
theorem agree5622 (p q : Pattern) (h : Agree support p q) : d5622 p = d5622 q := by
  simp only [d5622, h 204 (by decide), agree5564 p q h, agree35 p q h]
theorem nonnegative5622 (p : Pattern) : 0 ≤ d5622 p :=
  nonnegative_ite (p 204) (nonnegative5564 p) (nonnegative35 p)
def d5623 (p : Pattern) : Int := if p 182 then d5565 p else d5622 p
theorem agree5623 (p q : Pattern) (h : Agree support p q) : d5623 p = d5623 q := by
  simp only [d5623, h 182 (by decide), agree5565 p q h, agree5622 p q h]
theorem nonnegative5623 (p : Pattern) : 0 ≤ d5623 p :=
  nonnegative_ite (p 182) (nonnegative5565 p) (nonnegative5622 p)
def d5624 (p : Pattern) : Int := if p 163 then d5623 p else d5621 p
theorem agree5624 (p q : Pattern) (h : Agree support p q) : d5624 p = d5624 q := by
  simp only [d5624, h 163 (by decide), agree5623 p q h, agree5621 p q h]
theorem nonnegative5624 (p : Pattern) : 0 ≤ d5624 p :=
  nonnegative_ite (p 163) (nonnegative5623 p) (nonnegative5621 p)
def d5625 (p : Pattern) : Int := if p 162 then d5595 p else d5624 p
theorem agree5625 (p q : Pattern) (h : Agree support p q) : d5625 p = d5625 q := by
  simp only [d5625, h 162 (by decide), agree5595 p q h, agree5624 p q h]
theorem nonnegative5625 (p : Pattern) : 0 ≤ d5625 p :=
  nonnegative_ite (p 162) (nonnegative5595 p) (nonnegative5624 p)
def d5626 (p : Pattern) : Int := if p 161 then d12 p else d5625 p
theorem agree5626 (p q : Pattern) (h : Agree support p q) : d5626 p = d5626 q := by
  simp only [d5626, h 161 (by decide), agree12 p q h, agree5625 p q h]
theorem nonnegative5626 (p : Pattern) : 0 ≤ d5626 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5625 p)
def d5627 (p : Pattern) : Int := if p 160 then d5626 p else d5620 p
theorem agree5627 (p q : Pattern) (h : Agree support p q) : d5627 p = d5627 q := by
  simp only [d5627, h 160 (by decide), agree5626 p q h, agree5620 p q h]
theorem nonnegative5627 (p : Pattern) : 0 ≤ d5627 p :=
  nonnegative_ite (p 160) (nonnegative5626 p) (nonnegative5620 p)
def d5628 (p : Pattern) : Int := if p 163 then d5621 p else d5611 p
theorem agree5628 (p q : Pattern) (h : Agree support p q) : d5628 p = d5628 q := by
  simp only [d5628, h 163 (by decide), agree5621 p q h, agree5611 p q h]
theorem nonnegative5628 (p : Pattern) : 0 ≤ d5628 p :=
  nonnegative_ite (p 163) (nonnegative5621 p) (nonnegative5611 p)
def d5629 (p : Pattern) : Int := if p 163 then d5617 p else d5613 p
theorem agree5629 (p q : Pattern) (h : Agree support p q) : d5629 p = d5629 q := by
  simp only [d5629, h 163 (by decide), agree5617 p q h, agree5613 p q h]
theorem nonnegative5629 (p : Pattern) : 0 ≤ d5629 p :=
  nonnegative_ite (p 163) (nonnegative5617 p) (nonnegative5613 p)
def d5630 (p : Pattern) : Int := if p 162 then d5629 p else d5628 p
theorem agree5630 (p q : Pattern) (h : Agree support p q) : d5630 p = d5630 q := by
  simp only [d5630, h 162 (by decide), agree5629 p q h, agree5628 p q h]
theorem nonnegative5630 (p : Pattern) : 0 ≤ d5630 p :=
  nonnegative_ite (p 162) (nonnegative5629 p) (nonnegative5628 p)
def d5631 (p : Pattern) : Int := if p 163 then d5591 p else d5613 p
theorem agree5631 (p q : Pattern) (h : Agree support p q) : d5631 p = d5631 q := by
  simp only [d5631, h 163 (by decide), agree5591 p q h, agree5613 p q h]
theorem nonnegative5631 (p : Pattern) : 0 ≤ d5631 p :=
  nonnegative_ite (p 163) (nonnegative5591 p) (nonnegative5613 p)
def d5632 (p : Pattern) : Int := if p 162 then d5595 p else d5631 p
theorem agree5632 (p q : Pattern) (h : Agree support p q) : d5632 p = d5632 q := by
  simp only [d5632, h 162 (by decide), agree5595 p q h, agree5631 p q h]
theorem nonnegative5632 (p : Pattern) : 0 ≤ d5632 p :=
  nonnegative_ite (p 162) (nonnegative5595 p) (nonnegative5631 p)
def d5633 (p : Pattern) : Int := if p 161 then d5632 p else d5630 p
theorem agree5633 (p q : Pattern) (h : Agree support p q) : d5633 p = d5633 q := by
  simp only [d5633, h 161 (by decide), agree5632 p q h, agree5630 p q h]
theorem nonnegative5633 (p : Pattern) : 0 ≤ d5633 p :=
  nonnegative_ite (p 161) (nonnegative5632 p) (nonnegative5630 p)
def d5634 (p : Pattern) : Int := if p 163 then d12 p else d5623 p
theorem agree5634 (p q : Pattern) (h : Agree support p q) : d5634 p = d5634 q := by
  simp only [d5634, h 163 (by decide), agree12 p q h, agree5623 p q h]
theorem nonnegative5634 (p : Pattern) : 0 ≤ d5634 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative5623 p)
def d5635 (p : Pattern) : Int := if p 162 then d12 p else d5634 p
theorem agree5635 (p q : Pattern) (h : Agree support p q) : d5635 p = d5635 q := by
  simp only [d5635, h 162 (by decide), agree12 p q h, agree5634 p q h]
theorem nonnegative5635 (p : Pattern) : 0 ≤ d5635 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative5634 p)
def d5636 (p : Pattern) : Int := if p 161 then d12 p else d5635 p
theorem agree5636 (p q : Pattern) (h : Agree support p q) : d5636 p = d5636 q := by
  simp only [d5636, h 161 (by decide), agree12 p q h, agree5635 p q h]
theorem nonnegative5636 (p : Pattern) : 0 ≤ d5636 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative5635 p)
def d5637 (p : Pattern) : Int := if p 160 then d5636 p else d5633 p
theorem agree5637 (p q : Pattern) (h : Agree support p q) : d5637 p = d5637 q := by
  simp only [d5637, h 160 (by decide), agree5636 p q h, agree5633 p q h]
theorem nonnegative5637 (p : Pattern) : 0 ≤ d5637 p :=
  nonnegative_ite (p 160) (nonnegative5636 p) (nonnegative5633 p)
def d5638 (p : Pattern) : Int := if p 141 then d5637 p else d5627 p
theorem agree5638 (p q : Pattern) (h : Agree support p q) : d5638 p = d5638 q := by
  simp only [d5638, h 141 (by decide), agree5637 p q h, agree5627 p q h]
theorem nonnegative5638 (p : Pattern) : 0 ≤ d5638 p :=
  nonnegative_ite (p 141) (nonnegative5637 p) (nonnegative5627 p)
def d5639 (p : Pattern) : Int := if p 138 then d5638 p else d5609 p
theorem agree5639 (p q : Pattern) (h : Agree support p q) : d5639 p = d5639 q := by
  simp only [d5639, h 138 (by decide), agree5638 p q h, agree5609 p q h]
theorem nonnegative5639 (p : Pattern) : 0 ≤ d5639 p :=
  nonnegative_ite (p 138) (nonnegative5638 p) (nonnegative5609 p)
end NetHack.Sokoban22Refined85
