/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes37
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d4560 (p : Pattern) : Int := if p 160 then d4559 p else d4556 p
theorem agree4560 (p q : Pattern) (h : Agree support p q) : d4560 p = d4560 q := by
  simp only [d4560, h 160 (by decide), agree4559 p q h, agree4556 p q h]
theorem nonnegative4560 (p : Pattern) : 0 ≤ d4560 p :=
  nonnegative_ite (p 160) (nonnegative4559 p) (nonnegative4556 p)
def d4561 (p : Pattern) : Int := if p 163 then d40 p else d18 p
theorem agree4561 (p q : Pattern) (h : Agree support p q) : d4561 p = d4561 q := by
  simp only [d4561, h 163 (by decide), agree40 p q h, agree18 p q h]
theorem nonnegative4561 (p : Pattern) : 0 ≤ d4561 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative18 p)
def d4562 (p : Pattern) : Int := if p 162 then d4561 p else d31 p
theorem agree4562 (p q : Pattern) (h : Agree support p q) : d4562 p = d4562 q := by
  simp only [d4562, h 162 (by decide), agree4561 p q h, agree31 p q h]
theorem nonnegative4562 (p : Pattern) : 0 ≤ d4562 p :=
  nonnegative_ite (p 162) (nonnegative4561 p) (nonnegative31 p)
def d4563 (p : Pattern) : Int := if p 161 then d4495 p else d4562 p
theorem agree4563 (p q : Pattern) (h : Agree support p q) : d4563 p = d4563 q := by
  simp only [d4563, h 161 (by decide), agree4495 p q h, agree4562 p q h]
theorem nonnegative4563 (p : Pattern) : 0 ≤ d4563 p :=
  nonnegative_ite (p 161) (nonnegative4495 p) (nonnegative4562 p)
def d4564 (p : Pattern) : Int := if p 163 then d12 p else d191 p
theorem agree4564 (p q : Pattern) (h : Agree support p q) : d4564 p = d4564 q := by
  simp only [d4564, h 163 (by decide), agree12 p q h, agree191 p q h]
theorem nonnegative4564 (p : Pattern) : 0 ≤ d4564 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative191 p)
def d4565 (p : Pattern) : Int := if p 162 then d12 p else d4564 p
theorem agree4565 (p q : Pattern) (h : Agree support p q) : d4565 p = d4565 q := by
  simp only [d4565, h 162 (by decide), agree12 p q h, agree4564 p q h]
theorem nonnegative4565 (p : Pattern) : 0 ≤ d4565 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4564 p)
def d4566 (p : Pattern) : Int := if p 161 then d12 p else d4565 p
theorem agree4566 (p q : Pattern) (h : Agree support p q) : d4566 p = d4566 q := by
  simp only [d4566, h 161 (by decide), agree12 p q h, agree4565 p q h]
theorem nonnegative4566 (p : Pattern) : 0 ≤ d4566 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4565 p)
def d4567 (p : Pattern) : Int := if p 160 then d4566 p else d4563 p
theorem agree4567 (p q : Pattern) (h : Agree support p q) : d4567 p = d4567 q := by
  simp only [d4567, h 160 (by decide), agree4566 p q h, agree4563 p q h]
theorem nonnegative4567 (p : Pattern) : 0 ≤ d4567 p :=
  nonnegative_ite (p 160) (nonnegative4566 p) (nonnegative4563 p)
def d4568 (p : Pattern) : Int := if p 141 then d4567 p else d4560 p
theorem agree4568 (p q : Pattern) (h : Agree support p q) : d4568 p = d4568 q := by
  simp only [d4568, h 141 (by decide), agree4567 p q h, agree4560 p q h]
theorem nonnegative4568 (p : Pattern) : 0 ≤ d4568 p :=
  nonnegative_ite (p 141) (nonnegative4567 p) (nonnegative4560 p)
def d4569 (p : Pattern) : Int := if p 138 then d4568 p else d4554 p
theorem agree4569 (p q : Pattern) (h : Agree support p q) : d4569 p = d4569 q := by
  simp only [d4569, h 138 (by decide), agree4568 p q h, agree4554 p q h]
theorem nonnegative4569 (p : Pattern) : 0 ≤ d4569 p :=
  nonnegative_ite (p 138) (nonnegative4568 p) (nonnegative4554 p)
def d4570 (p : Pattern) : Int := if p 138 then d12 p else d4568 p
theorem agree4570 (p q : Pattern) (h : Agree support p q) : d4570 p = d4570 q := by
  simp only [d4570, h 138 (by decide), agree12 p q h, agree4568 p q h]
theorem nonnegative4570 (p : Pattern) : 0 ≤ d4570 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4568 p)
def d4571 (p : Pattern) : Int := if p 116 then d4570 p else d4569 p
theorem agree4571 (p q : Pattern) (h : Agree support p q) : d4571 p = d4571 q := by
  simp only [d4571, h 116 (by decide), agree4570 p q h, agree4569 p q h]
theorem nonnegative4571 (p : Pattern) : 0 ≤ d4571 p :=
  nonnegative_ite (p 116) (nonnegative4570 p) (nonnegative4569 p)
def d4572 (p : Pattern) : Int := if p 115 then d4571 p else d4509 p
theorem agree4572 (p q : Pattern) (h : Agree support p q) : d4572 p = d4572 q := by
  simp only [d4572, h 115 (by decide), agree4571 p q h, agree4509 p q h]
theorem nonnegative4572 (p : Pattern) : 0 ≤ d4572 p :=
  nonnegative_ite (p 115) (nonnegative4571 p) (nonnegative4509 p)
def d4573 (p : Pattern) : Int := if p 71 then d4572 p else d4512 p
theorem agree4573 (p q : Pattern) (h : Agree support p q) : d4573 p = d4573 q := by
  simp only [d4573, h 71 (by decide), agree4572 p q h, agree4512 p q h]
theorem nonnegative4573 (p : Pattern) : 0 ≤ d4573 p :=
  nonnegative_ite (p 71) (nonnegative4572 p) (nonnegative4512 p)
def d4574 (p : Pattern) : Int := if p 163 then d12 p else d107 p
theorem agree4574 (p q : Pattern) (h : Agree support p q) : d4574 p = d4574 q := by
  simp only [d4574, h 163 (by decide), agree12 p q h, agree107 p q h]
theorem nonnegative4574 (p : Pattern) : 0 ≤ d4574 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative107 p)
def d4575 (p : Pattern) : Int := if p 162 then d4574 p else d4518 p
theorem agree4575 (p q : Pattern) (h : Agree support p q) : d4575 p = d4575 q := by
  simp only [d4575, h 162 (by decide), agree4574 p q h, agree4518 p q h]
theorem nonnegative4575 (p : Pattern) : 0 ≤ d4575 p :=
  nonnegative_ite (p 162) (nonnegative4574 p) (nonnegative4518 p)
def d4576 (p : Pattern) : Int := if p 162 then d12 p else d4574 p
theorem agree4576 (p q : Pattern) (h : Agree support p q) : d4576 p = d4576 q := by
  simp only [d4576, h 162 (by decide), agree12 p q h, agree4574 p q h]
theorem nonnegative4576 (p : Pattern) : 0 ≤ d4576 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4574 p)
def d4577 (p : Pattern) : Int := if p 161 then d4576 p else d4575 p
theorem agree4577 (p q : Pattern) (h : Agree support p q) : d4577 p = d4577 q := by
  simp only [d4577, h 161 (by decide), agree4576 p q h, agree4575 p q h]
theorem nonnegative4577 (p : Pattern) : 0 ≤ d4577 p :=
  nonnegative_ite (p 161) (nonnegative4576 p) (nonnegative4575 p)
def d4578 (p : Pattern) : Int := if p 141 then d4577 p else d4517 p
theorem agree4578 (p q : Pattern) (h : Agree support p q) : d4578 p = d4578 q := by
  simp only [d4578, h 141 (by decide), agree4577 p q h, agree4517 p q h]
theorem nonnegative4578 (p : Pattern) : 0 ≤ d4578 p :=
  nonnegative_ite (p 141) (nonnegative4577 p) (nonnegative4517 p)
def d4579 (p : Pattern) : Int := if p 160 then d4531 p else d4577 p
theorem agree4579 (p q : Pattern) (h : Agree support p q) : d4579 p = d4579 q := by
  simp only [d4579, h 160 (by decide), agree4531 p q h, agree4577 p q h]
theorem nonnegative4579 (p : Pattern) : 0 ≤ d4579 p :=
  nonnegative_ite (p 160) (nonnegative4531 p) (nonnegative4577 p)
def d4580 (p : Pattern) : Int := if p 141 then d4579 p else d4528 p
theorem agree4580 (p q : Pattern) (h : Agree support p q) : d4580 p = d4580 q := by
  simp only [d4580, h 141 (by decide), agree4579 p q h, agree4528 p q h]
theorem nonnegative4580 (p : Pattern) : 0 ≤ d4580 p :=
  nonnegative_ite (p 141) (nonnegative4579 p) (nonnegative4528 p)
def d4581 (p : Pattern) : Int := if p 138 then d4580 p else d4578 p
theorem agree4581 (p q : Pattern) (h : Agree support p q) : d4581 p = d4581 q := by
  simp only [d4581, h 138 (by decide), agree4580 p q h, agree4578 p q h]
theorem nonnegative4581 (p : Pattern) : 0 ≤ d4581 p :=
  nonnegative_ite (p 138) (nonnegative4580 p) (nonnegative4578 p)
def d4582 (p : Pattern) : Int := if p 138 then d4538 p else d4580 p
theorem agree4582 (p q : Pattern) (h : Agree support p q) : d4582 p = d4582 q := by
  simp only [d4582, h 138 (by decide), agree4538 p q h, agree4580 p q h]
theorem nonnegative4582 (p : Pattern) : 0 ≤ d4582 p :=
  nonnegative_ite (p 138) (nonnegative4538 p) (nonnegative4580 p)
def d4583 (p : Pattern) : Int := if p 116 then d4582 p else d4581 p
theorem agree4583 (p q : Pattern) (h : Agree support p q) : d4583 p = d4583 q := by
  simp only [d4583, h 116 (by decide), agree4582 p q h, agree4581 p q h]
theorem nonnegative4583 (p : Pattern) : 0 ≤ d4583 p :=
  nonnegative_ite (p 116) (nonnegative4582 p) (nonnegative4581 p)
def d4584 (p : Pattern) : Int := if p 162 then d4574 p else d116 p
theorem agree4584 (p q : Pattern) (h : Agree support p q) : d4584 p = d4584 q := by
  simp only [d4584, h 162 (by decide), agree4574 p q h, agree116 p q h]
theorem nonnegative4584 (p : Pattern) : 0 ≤ d4584 p :=
  nonnegative_ite (p 162) (nonnegative4574 p) (nonnegative116 p)
def d4585 (p : Pattern) : Int := if p 161 then d4530 p else d4584 p
theorem agree4585 (p q : Pattern) (h : Agree support p q) : d4585 p = d4585 q := by
  simp only [d4585, h 161 (by decide), agree4530 p q h, agree4584 p q h]
theorem nonnegative4585 (p : Pattern) : 0 ≤ d4585 p :=
  nonnegative_ite (p 161) (nonnegative4530 p) (nonnegative4584 p)
def d4586 (p : Pattern) : Int := if p 160 then d4585 p else d4517 p
theorem agree4586 (p q : Pattern) (h : Agree support p q) : d4586 p = d4586 q := by
  simp only [d4586, h 160 (by decide), agree4585 p q h, agree4517 p q h]
theorem nonnegative4586 (p : Pattern) : 0 ≤ d4586 p :=
  nonnegative_ite (p 160) (nonnegative4585 p) (nonnegative4517 p)
def d4587 (p : Pattern) : Int := if p 162 then d4529 p else d107 p
theorem agree4587 (p q : Pattern) (h : Agree support p q) : d4587 p = d4587 q := by
  simp only [d4587, h 162 (by decide), agree4529 p q h, agree107 p q h]
theorem nonnegative4587 (p : Pattern) : 0 ≤ d4587 p :=
  nonnegative_ite (p 162) (nonnegative4529 p) (nonnegative107 p)
def d4588 (p : Pattern) : Int := if p 162 then d12 p else d4479 p
theorem agree4588 (p q : Pattern) (h : Agree support p q) : d4588 p = d4588 q := by
  simp only [d4588, h 162 (by decide), agree12 p q h, agree4479 p q h]
theorem nonnegative4588 (p : Pattern) : 0 ≤ d4588 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4479 p)
def d4589 (p : Pattern) : Int := if p 161 then d4588 p else d4587 p
theorem agree4589 (p q : Pattern) (h : Agree support p q) : d4589 p = d4589 q := by
  simp only [d4589, h 161 (by decide), agree4588 p q h, agree4587 p q h]
theorem nonnegative4589 (p : Pattern) : 0 ≤ d4589 p :=
  nonnegative_ite (p 161) (nonnegative4588 p) (nonnegative4587 p)
def d4590 (p : Pattern) : Int := if p 160 then d4589 p else d4577 p
theorem agree4590 (p q : Pattern) (h : Agree support p q) : d4590 p = d4590 q := by
  simp only [d4590, h 160 (by decide), agree4589 p q h, agree4577 p q h]
theorem nonnegative4590 (p : Pattern) : 0 ≤ d4590 p :=
  nonnegative_ite (p 160) (nonnegative4589 p) (nonnegative4577 p)
def d4591 (p : Pattern) : Int := if p 141 then d4590 p else d4586 p
theorem agree4591 (p q : Pattern) (h : Agree support p q) : d4591 p = d4591 q := by
  simp only [d4591, h 141 (by decide), agree4590 p q h, agree4586 p q h]
theorem nonnegative4591 (p : Pattern) : 0 ≤ d4591 p :=
  nonnegative_ite (p 141) (nonnegative4590 p) (nonnegative4586 p)
def d4592 (p : Pattern) : Int := if p 163 then d40 p else d116 p
theorem agree4592 (p q : Pattern) (h : Agree support p q) : d4592 p = d4592 q := by
  simp only [d4592, h 163 (by decide), agree40 p q h, agree116 p q h]
theorem nonnegative4592 (p : Pattern) : 0 ≤ d4592 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative116 p)
def d4593 (p : Pattern) : Int := if p 162 then d4592 p else d103 p
theorem agree4593 (p q : Pattern) (h : Agree support p q) : d4593 p = d4593 q := by
  simp only [d4593, h 162 (by decide), agree4592 p q h, agree103 p q h]
theorem nonnegative4593 (p : Pattern) : 0 ≤ d4593 p :=
  nonnegative_ite (p 162) (nonnegative4592 p) (nonnegative103 p)
def d4594 (p : Pattern) : Int := if p 161 then d4522 p else d4593 p
theorem agree4594 (p q : Pattern) (h : Agree support p q) : d4594 p = d4594 q := by
  simp only [d4594, h 161 (by decide), agree4522 p q h, agree4593 p q h]
theorem nonnegative4594 (p : Pattern) : 0 ≤ d4594 p :=
  nonnegative_ite (p 161) (nonnegative4522 p) (nonnegative4593 p)
def d4595 (p : Pattern) : Int := if p 160 then d4531 p else d4594 p
theorem agree4595 (p q : Pattern) (h : Agree support p q) : d4595 p = d4595 q := by
  simp only [d4595, h 160 (by decide), agree4531 p q h, agree4594 p q h]
theorem nonnegative4595 (p : Pattern) : 0 ≤ d4595 p :=
  nonnegative_ite (p 160) (nonnegative4531 p) (nonnegative4594 p)
def d4596 (p : Pattern) : Int := if p 161 then d12 p else d4588 p
theorem agree4596 (p q : Pattern) (h : Agree support p q) : d4596 p = d4596 q := by
  simp only [d4596, h 161 (by decide), agree12 p q h, agree4588 p q h]
theorem nonnegative4596 (p : Pattern) : 0 ≤ d4596 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4588 p)
def d4597 (p : Pattern) : Int := if p 160 then d4596 p else d4585 p
theorem agree4597 (p q : Pattern) (h : Agree support p q) : d4597 p = d4597 q := by
  simp only [d4597, h 160 (by decide), agree4596 p q h, agree4585 p q h]
theorem nonnegative4597 (p : Pattern) : 0 ≤ d4597 p :=
  nonnegative_ite (p 160) (nonnegative4596 p) (nonnegative4585 p)
def d4598 (p : Pattern) : Int := if p 141 then d4597 p else d4595 p
theorem agree4598 (p q : Pattern) (h : Agree support p q) : d4598 p = d4598 q := by
  simp only [d4598, h 141 (by decide), agree4597 p q h, agree4595 p q h]
theorem nonnegative4598 (p : Pattern) : 0 ≤ d4598 p :=
  nonnegative_ite (p 141) (nonnegative4597 p) (nonnegative4595 p)
def d4599 (p : Pattern) : Int := if p 138 then d4598 p else d4591 p
theorem agree4599 (p q : Pattern) (h : Agree support p q) : d4599 p = d4599 q := by
  simp only [d4599, h 138 (by decide), agree4598 p q h, agree4591 p q h]
theorem nonnegative4599 (p : Pattern) : 0 ≤ d4599 p :=
  nonnegative_ite (p 138) (nonnegative4598 p) (nonnegative4591 p)
def d4600 (p : Pattern) : Int := if p 163 then d24 p else d116 p
theorem agree4600 (p q : Pattern) (h : Agree support p q) : d4600 p = d4600 q := by
  simp only [d4600, h 163 (by decide), agree24 p q h, agree116 p q h]
theorem nonnegative4600 (p : Pattern) : 0 ≤ d4600 p :=
  nonnegative_ite (p 163) (nonnegative24 p) (nonnegative116 p)
def d4601 (p : Pattern) : Int := if p 162 then d4600 p else d103 p
theorem agree4601 (p q : Pattern) (h : Agree support p q) : d4601 p = d4601 q := by
  simp only [d4601, h 162 (by decide), agree4600 p q h, agree103 p q h]
theorem nonnegative4601 (p : Pattern) : 0 ≤ d4601 p :=
  nonnegative_ite (p 162) (nonnegative4600 p) (nonnegative103 p)
def d4602 (p : Pattern) : Int := if p 163 then d24 p else d107 p
theorem agree4602 (p q : Pattern) (h : Agree support p q) : d4602 p = d4602 q := by
  simp only [d4602, h 163 (by decide), agree24 p q h, agree107 p q h]
theorem nonnegative4602 (p : Pattern) : 0 ≤ d4602 p :=
  nonnegative_ite (p 163) (nonnegative24 p) (nonnegative107 p)
def d4603 (p : Pattern) : Int := if p 162 then d12 p else d4602 p
theorem agree4603 (p q : Pattern) (h : Agree support p q) : d4603 p = d4603 q := by
  simp only [d4603, h 162 (by decide), agree12 p q h, agree4602 p q h]
theorem nonnegative4603 (p : Pattern) : 0 ≤ d4603 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4602 p)
def d4604 (p : Pattern) : Int := if p 161 then d4603 p else d4601 p
theorem agree4604 (p q : Pattern) (h : Agree support p q) : d4604 p = d4604 q := by
  simp only [d4604, h 161 (by decide), agree4603 p q h, agree4601 p q h]
theorem nonnegative4604 (p : Pattern) : 0 ≤ d4604 p :=
  nonnegative_ite (p 161) (nonnegative4603 p) (nonnegative4601 p)
def d4605 (p : Pattern) : Int := if p 163 then d40 p else d120 p
theorem agree4605 (p q : Pattern) (h : Agree support p q) : d4605 p = d4605 q := by
  simp only [d4605, h 163 (by decide), agree40 p q h, agree120 p q h]
theorem nonnegative4605 (p : Pattern) : 0 ≤ d4605 p :=
  nonnegative_ite (p 163) (nonnegative40 p) (nonnegative120 p)
def d4606 (p : Pattern) : Int := if p 162 then d12 p else d4605 p
theorem agree4606 (p q : Pattern) (h : Agree support p q) : d4606 p = d4606 q := by
  simp only [d4606, h 162 (by decide), agree12 p q h, agree4605 p q h]
theorem nonnegative4606 (p : Pattern) : 0 ≤ d4606 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4605 p)
def d4607 (p : Pattern) : Int := if p 161 then d12 p else d4606 p
theorem agree4607 (p q : Pattern) (h : Agree support p q) : d4607 p = d4607 q := by
  simp only [d4607, h 161 (by decide), agree12 p q h, agree4606 p q h]
theorem nonnegative4607 (p : Pattern) : 0 ≤ d4607 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4606 p)
def d4608 (p : Pattern) : Int := if p 160 then d4607 p else d4604 p
theorem agree4608 (p q : Pattern) (h : Agree support p q) : d4608 p = d4608 q := by
  simp only [d4608, h 160 (by decide), agree4607 p q h, agree4604 p q h]
theorem nonnegative4608 (p : Pattern) : 0 ≤ d4608 p :=
  nonnegative_ite (p 160) (nonnegative4607 p) (nonnegative4604 p)
def d4609 (p : Pattern) : Int := if p 141 then d4597 p else d4608 p
theorem agree4609 (p q : Pattern) (h : Agree support p q) : d4609 p = d4609 q := by
  simp only [d4609, h 141 (by decide), agree4597 p q h, agree4608 p q h]
theorem nonnegative4609 (p : Pattern) : 0 ≤ d4609 p :=
  nonnegative_ite (p 141) (nonnegative4597 p) (nonnegative4608 p)
def d4610 (p : Pattern) : Int := if p 138 then d12 p else d4609 p
theorem agree4610 (p q : Pattern) (h : Agree support p q) : d4610 p = d4610 q := by
  simp only [d4610, h 138 (by decide), agree12 p q h, agree4609 p q h]
theorem nonnegative4610 (p : Pattern) : 0 ≤ d4610 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4609 p)
def d4611 (p : Pattern) : Int := if p 116 then d4610 p else d4599 p
theorem agree4611 (p q : Pattern) (h : Agree support p q) : d4611 p = d4611 q := by
  simp only [d4611, h 116 (by decide), agree4610 p q h, agree4599 p q h]
theorem nonnegative4611 (p : Pattern) : 0 ≤ d4611 p :=
  nonnegative_ite (p 116) (nonnegative4610 p) (nonnegative4599 p)
def d4612 (p : Pattern) : Int := if p 115 then d4611 p else d4583 p
theorem agree4612 (p q : Pattern) (h : Agree support p q) : d4612 p = d4612 q := by
  simp only [d4612, h 115 (by decide), agree4611 p q h, agree4583 p q h]
theorem nonnegative4612 (p : Pattern) : 0 ≤ d4612 p :=
  nonnegative_ite (p 115) (nonnegative4611 p) (nonnegative4583 p)
def d4613 (p : Pattern) : Int := if p 71 then d4612 p else d4512 p
theorem agree4613 (p q : Pattern) (h : Agree support p q) : d4613 p = d4613 q := by
  simp only [d4613, h 71 (by decide), agree4612 p q h, agree4512 p q h]
theorem nonnegative4613 (p : Pattern) : 0 ≤ d4613 p :=
  nonnegative_ite (p 71) (nonnegative4612 p) (nonnegative4512 p)
def d4614 (p : Pattern) : Int := if p 49 then d4613 p else d4573 p
theorem agree4614 (p q : Pattern) (h : Agree support p q) : d4614 p = d4614 q := by
  simp only [d4614, h 49 (by decide), agree4613 p q h, agree4573 p q h]
theorem nonnegative4614 (p : Pattern) : 0 ≤ d4614 p :=
  nonnegative_ite (p 49) (nonnegative4613 p) (nonnegative4573 p)
def d4615 (p : Pattern) : Int := if p 48 then d4614 p else d4545 p
theorem agree4615 (p q : Pattern) (h : Agree support p q) : d4615 p = d4615 q := by
  simp only [d4615, h 48 (by decide), agree4614 p q h, agree4545 p q h]
theorem nonnegative4615 (p : Pattern) : 0 ≤ d4615 p :=
  nonnegative_ite (p 48) (nonnegative4614 p) (nonnegative4545 p)
def d4616 (p : Pattern) : Int := if p 160 then d0 p else d4298 p
theorem agree4616 (p q : Pattern) (h : Agree support p q) : d4616 p = d4616 q := by
  simp only [d4616, h 160 (by decide), agree0 p q h, agree4298 p q h]
theorem nonnegative4616 (p : Pattern) : 0 ≤ d4616 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4298 p)
def d4617 (p : Pattern) : Int := if p 161 then d4395 p else d0 p
theorem agree4617 (p q : Pattern) (h : Agree support p q) : d4617 p = d4617 q := by
  simp only [d4617, h 161 (by decide), agree4395 p q h, agree0 p q h]
theorem nonnegative4617 (p : Pattern) : 0 ≤ d4617 p :=
  nonnegative_ite (p 161) (nonnegative4395 p) (nonnegative0 p)
def d4618 (p : Pattern) : Int := if p 160 then d0 p else d4617 p
theorem agree4618 (p q : Pattern) (h : Agree support p q) : d4618 p = d4618 q := by
  simp only [d4618, h 160 (by decide), agree0 p q h, agree4617 p q h]
theorem nonnegative4618 (p : Pattern) : 0 ≤ d4618 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative4617 p)
def d4619 (p : Pattern) : Int := if p 160 then d79 p else d21 p
theorem agree4619 (p q : Pattern) (h : Agree support p q) : d4619 p = d4619 q := by
  simp only [d4619, h 160 (by decide), agree79 p q h, agree21 p q h]
theorem nonnegative4619 (p : Pattern) : 0 ≤ d4619 p :=
  nonnegative_ite (p 160) (nonnegative79 p) (nonnegative21 p)
def d4620 (p : Pattern) : Int := if p 160 then d798 p else d55 p
theorem agree4620 (p q : Pattern) (h : Agree support p q) : d4620 p = d4620 q := by
  simp only [d4620, h 160 (by decide), agree798 p q h, agree55 p q h]
theorem nonnegative4620 (p : Pattern) : 0 ≤ d4620 p :=
  nonnegative_ite (p 160) (nonnegative798 p) (nonnegative55 p)
def d4621 (p : Pattern) : Int := if p 141 then d4620 p else d4619 p
theorem agree4621 (p q : Pattern) (h : Agree support p q) : d4621 p = d4621 q := by
  simp only [d4621, h 141 (by decide), agree4620 p q h, agree4619 p q h]
theorem nonnegative4621 (p : Pattern) : 0 ≤ d4621 p :=
  nonnegative_ite (p 141) (nonnegative4620 p) (nonnegative4619 p)
def d4622 (p : Pattern) : Int := if p 160 then d809 p else d55 p
theorem agree4622 (p q : Pattern) (h : Agree support p q) : d4622 p = d4622 q := by
  simp only [d4622, h 160 (by decide), agree809 p q h, agree55 p q h]
theorem nonnegative4622 (p : Pattern) : 0 ≤ d4622 p :=
  nonnegative_ite (p 160) (nonnegative809 p) (nonnegative55 p)
def d4623 (p : Pattern) : Int := if p 141 then d4622 p else d4619 p
theorem agree4623 (p q : Pattern) (h : Agree support p q) : d4623 p = d4623 q := by
  simp only [d4623, h 141 (by decide), agree4622 p q h, agree4619 p q h]
theorem nonnegative4623 (p : Pattern) : 0 ≤ d4623 p :=
  nonnegative_ite (p 141) (nonnegative4622 p) (nonnegative4619 p)
def d4624 (p : Pattern) : Int := if p 138 then d4623 p else d4621 p
theorem agree4624 (p q : Pattern) (h : Agree support p q) : d4624 p = d4624 q := by
  simp only [d4624, h 138 (by decide), agree4623 p q h, agree4621 p q h]
theorem nonnegative4624 (p : Pattern) : 0 ≤ d4624 p :=
  nonnegative_ite (p 138) (nonnegative4623 p) (nonnegative4621 p)
def d4625 (p : Pattern) : Int := if p 160 then d12 p else d63 p
theorem agree4625 (p q : Pattern) (h : Agree support p q) : d4625 p = d4625 q := by
  simp only [d4625, h 160 (by decide), agree12 p q h, agree63 p q h]
theorem nonnegative4625 (p : Pattern) : 0 ≤ d4625 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative63 p)
def d4626 (p : Pattern) : Int := if p 141 then d12 p else d4625 p
theorem agree4626 (p q : Pattern) (h : Agree support p q) : d4626 p = d4626 q := by
  simp only [d4626, h 141 (by decide), agree12 p q h, agree4625 p q h]
theorem nonnegative4626 (p : Pattern) : 0 ≤ d4626 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative4625 p)
def d4627 (p : Pattern) : Int := if p 138 then d4626 p else d4623 p
theorem agree4627 (p q : Pattern) (h : Agree support p q) : d4627 p = d4627 q := by
  simp only [d4627, h 138 (by decide), agree4626 p q h, agree4623 p q h]
theorem nonnegative4627 (p : Pattern) : 0 ≤ d4627 p :=
  nonnegative_ite (p 138) (nonnegative4626 p) (nonnegative4623 p)
def d4628 (p : Pattern) : Int := if p 116 then d4627 p else d4624 p
theorem agree4628 (p q : Pattern) (h : Agree support p q) : d4628 p = d4628 q := by
  simp only [d4628, h 116 (by decide), agree4627 p q h, agree4624 p q h]
theorem nonnegative4628 (p : Pattern) : 0 ≤ d4628 p :=
  nonnegative_ite (p 116) (nonnegative4627 p) (nonnegative4624 p)
def d4629 (p : Pattern) : Int := if p 138 then d12 p else d4623 p
theorem agree4629 (p q : Pattern) (h : Agree support p q) : d4629 p = d4629 q := by
  simp only [d4629, h 138 (by decide), agree12 p q h, agree4623 p q h]
theorem nonnegative4629 (p : Pattern) : 0 ≤ d4629 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4623 p)
def d4630 (p : Pattern) : Int := if p 116 then d4629 p else d4624 p
theorem agree4630 (p q : Pattern) (h : Agree support p q) : d4630 p = d4630 q := by
  simp only [d4630, h 116 (by decide), agree4629 p q h, agree4624 p q h]
theorem nonnegative4630 (p : Pattern) : 0 ≤ d4630 p :=
  nonnegative_ite (p 116) (nonnegative4629 p) (nonnegative4624 p)
def d4631 (p : Pattern) : Int := if p 115 then d4630 p else d4628 p
theorem agree4631 (p q : Pattern) (h : Agree support p q) : d4631 p = d4631 q := by
  simp only [d4631, h 115 (by decide), agree4630 p q h, agree4628 p q h]
theorem nonnegative4631 (p : Pattern) : 0 ≤ d4631 p :=
  nonnegative_ite (p 115) (nonnegative4630 p) (nonnegative4628 p)
def d4632 (p : Pattern) : Int := if p 160 then d149 p else d110 p
theorem agree4632 (p q : Pattern) (h : Agree support p q) : d4632 p = d4632 q := by
  simp only [d4632, h 160 (by decide), agree149 p q h, agree110 p q h]
theorem nonnegative4632 (p : Pattern) : 0 ≤ d4632 p :=
  nonnegative_ite (p 160) (nonnegative149 p) (nonnegative110 p)
def d4633 (p : Pattern) : Int := if p 160 then d863 p else d134 p
theorem agree4633 (p q : Pattern) (h : Agree support p q) : d4633 p = d4633 q := by
  simp only [d4633, h 160 (by decide), agree863 p q h, agree134 p q h]
theorem nonnegative4633 (p : Pattern) : 0 ≤ d4633 p :=
  nonnegative_ite (p 160) (nonnegative863 p) (nonnegative134 p)
def d4634 (p : Pattern) : Int := if p 141 then d4633 p else d4632 p
theorem agree4634 (p q : Pattern) (h : Agree support p q) : d4634 p = d4634 q := by
  simp only [d4634, h 141 (by decide), agree4633 p q h, agree4632 p q h]
theorem nonnegative4634 (p : Pattern) : 0 ≤ d4634 p :=
  nonnegative_ite (p 141) (nonnegative4633 p) (nonnegative4632 p)
def d4635 (p : Pattern) : Int := if p 160 then d153 p else d134 p
theorem agree4635 (p q : Pattern) (h : Agree support p q) : d4635 p = d4635 q := by
  simp only [d4635, h 160 (by decide), agree153 p q h, agree134 p q h]
theorem nonnegative4635 (p : Pattern) : 0 ≤ d4635 p :=
  nonnegative_ite (p 160) (nonnegative153 p) (nonnegative134 p)
def d4636 (p : Pattern) : Int := if p 141 then d4635 p else d4632 p
theorem agree4636 (p q : Pattern) (h : Agree support p q) : d4636 p = d4636 q := by
  simp only [d4636, h 141 (by decide), agree4635 p q h, agree4632 p q h]
theorem nonnegative4636 (p : Pattern) : 0 ≤ d4636 p :=
  nonnegative_ite (p 141) (nonnegative4635 p) (nonnegative4632 p)
def d4637 (p : Pattern) : Int := if p 138 then d4636 p else d4634 p
theorem agree4637 (p q : Pattern) (h : Agree support p q) : d4637 p = d4637 q := by
  simp only [d4637, h 138 (by decide), agree4636 p q h, agree4634 p q h]
theorem nonnegative4637 (p : Pattern) : 0 ≤ d4637 p :=
  nonnegative_ite (p 138) (nonnegative4636 p) (nonnegative4634 p)
def d4638 (p : Pattern) : Int := if p 138 then d12 p else d4636 p
theorem agree4638 (p q : Pattern) (h : Agree support p q) : d4638 p = d4638 q := by
  simp only [d4638, h 138 (by decide), agree12 p q h, agree4636 p q h]
theorem nonnegative4638 (p : Pattern) : 0 ≤ d4638 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4636 p)
def d4639 (p : Pattern) : Int := if p 116 then d4638 p else d4637 p
theorem agree4639 (p q : Pattern) (h : Agree support p q) : d4639 p = d4639 q := by
  simp only [d4639, h 116 (by decide), agree4638 p q h, agree4637 p q h]
theorem nonnegative4639 (p : Pattern) : 0 ≤ d4639 p :=
  nonnegative_ite (p 116) (nonnegative4638 p) (nonnegative4637 p)
def d4640 (p : Pattern) : Int := if p 71 then d4639 p else d4631 p
theorem agree4640 (p q : Pattern) (h : Agree support p q) : d4640 p = d4640 q := by
  simp only [d4640, h 71 (by decide), agree4639 p q h, agree4631 p q h]
theorem nonnegative4640 (p : Pattern) : 0 ≤ d4640 p :=
  nonnegative_ite (p 71) (nonnegative4639 p) (nonnegative4631 p)
def d4641 (p : Pattern) : Int := if p 49 then d4640 p else d4631 p
theorem agree4641 (p q : Pattern) (h : Agree support p q) : d4641 p = d4641 q := by
  simp only [d4641, h 49 (by decide), agree4640 p q h, agree4631 p q h]
theorem nonnegative4641 (p : Pattern) : 0 ≤ d4641 p :=
  nonnegative_ite (p 49) (nonnegative4640 p) (nonnegative4631 p)
def d4642 (p : Pattern) : Int := if p 160 then d194 p else d79 p
theorem agree4642 (p q : Pattern) (h : Agree support p q) : d4642 p = d4642 q := by
  simp only [d4642, h 160 (by decide), agree194 p q h, agree79 p q h]
theorem nonnegative4642 (p : Pattern) : 0 ≤ d4642 p :=
  nonnegative_ite (p 160) (nonnegative194 p) (nonnegative79 p)
def d4643 (p : Pattern) : Int := if p 160 then d83 p else d198 p
theorem agree4643 (p q : Pattern) (h : Agree support p q) : d4643 p = d4643 q := by
  simp only [d4643, h 160 (by decide), agree83 p q h, agree198 p q h]
theorem nonnegative4643 (p : Pattern) : 0 ≤ d4643 p :=
  nonnegative_ite (p 160) (nonnegative83 p) (nonnegative198 p)
def d4644 (p : Pattern) : Int := if p 141 then d4643 p else d4642 p
theorem agree4644 (p q : Pattern) (h : Agree support p q) : d4644 p = d4644 q := by
  simp only [d4644, h 141 (by decide), agree4643 p q h, agree4642 p q h]
theorem nonnegative4644 (p : Pattern) : 0 ≤ d4644 p :=
  nonnegative_ite (p 141) (nonnegative4643 p) (nonnegative4642 p)
def d4645 (p : Pattern) : Int := if p 138 then d4644 p else d4621 p
theorem agree4645 (p q : Pattern) (h : Agree support p q) : d4645 p = d4645 q := by
  simp only [d4645, h 138 (by decide), agree4644 p q h, agree4621 p q h]
theorem nonnegative4645 (p : Pattern) : 0 ≤ d4645 p :=
  nonnegative_ite (p 138) (nonnegative4644 p) (nonnegative4621 p)
def d4646 (p : Pattern) : Int := if p 138 then d12 p else d4644 p
theorem agree4646 (p q : Pattern) (h : Agree support p q) : d4646 p = d4646 q := by
  simp only [d4646, h 138 (by decide), agree12 p q h, agree4644 p q h]
theorem nonnegative4646 (p : Pattern) : 0 ≤ d4646 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4644 p)
def d4647 (p : Pattern) : Int := if p 116 then d4646 p else d4645 p
theorem agree4647 (p q : Pattern) (h : Agree support p q) : d4647 p = d4647 q := by
  simp only [d4647, h 116 (by decide), agree4646 p q h, agree4645 p q h]
theorem nonnegative4647 (p : Pattern) : 0 ≤ d4647 p :=
  nonnegative_ite (p 116) (nonnegative4646 p) (nonnegative4645 p)
def d4648 (p : Pattern) : Int := if p 115 then d4647 p else d4628 p
theorem agree4648 (p q : Pattern) (h : Agree support p q) : d4648 p = d4648 q := by
  simp only [d4648, h 115 (by decide), agree4647 p q h, agree4628 p q h]
theorem nonnegative4648 (p : Pattern) : 0 ≤ d4648 p :=
  nonnegative_ite (p 115) (nonnegative4647 p) (nonnegative4628 p)
def d4649 (p : Pattern) : Int := if p 71 then d4648 p else d4631 p
theorem agree4649 (p q : Pattern) (h : Agree support p q) : d4649 p = d4649 q := by
  simp only [d4649, h 71 (by decide), agree4648 p q h, agree4631 p q h]
theorem nonnegative4649 (p : Pattern) : 0 ≤ d4649 p :=
  nonnegative_ite (p 71) (nonnegative4648 p) (nonnegative4631 p)
def d4650 (p : Pattern) : Int := if p 160 then d863 p else d211 p
theorem agree4650 (p q : Pattern) (h : Agree support p q) : d4650 p = d4650 q := by
  simp only [d4650, h 160 (by decide), agree863 p q h, agree211 p q h]
theorem nonnegative4650 (p : Pattern) : 0 ≤ d4650 p :=
  nonnegative_ite (p 160) (nonnegative863 p) (nonnegative211 p)
def d4651 (p : Pattern) : Int := if p 141 then d4650 p else d4632 p
theorem agree4651 (p q : Pattern) (h : Agree support p q) : d4651 p = d4651 q := by
  simp only [d4651, h 141 (by decide), agree4650 p q h, agree4632 p q h]
theorem nonnegative4651 (p : Pattern) : 0 ≤ d4651 p :=
  nonnegative_ite (p 141) (nonnegative4650 p) (nonnegative4632 p)
def d4652 (p : Pattern) : Int := if p 160 then d153 p else d211 p
theorem agree4652 (p q : Pattern) (h : Agree support p q) : d4652 p = d4652 q := by
  simp only [d4652, h 160 (by decide), agree153 p q h, agree211 p q h]
theorem nonnegative4652 (p : Pattern) : 0 ≤ d4652 p :=
  nonnegative_ite (p 160) (nonnegative153 p) (nonnegative211 p)
def d4653 (p : Pattern) : Int := if p 141 then d4652 p else d4632 p
theorem agree4653 (p q : Pattern) (h : Agree support p q) : d4653 p = d4653 q := by
  simp only [d4653, h 141 (by decide), agree4652 p q h, agree4632 p q h]
theorem nonnegative4653 (p : Pattern) : 0 ≤ d4653 p :=
  nonnegative_ite (p 141) (nonnegative4652 p) (nonnegative4632 p)
def d4654 (p : Pattern) : Int := if p 138 then d4653 p else d4651 p
theorem agree4654 (p q : Pattern) (h : Agree support p q) : d4654 p = d4654 q := by
  simp only [d4654, h 138 (by decide), agree4653 p q h, agree4651 p q h]
theorem nonnegative4654 (p : Pattern) : 0 ≤ d4654 p :=
  nonnegative_ite (p 138) (nonnegative4653 p) (nonnegative4651 p)
def d4655 (p : Pattern) : Int := if p 138 then d12 p else d4653 p
theorem agree4655 (p q : Pattern) (h : Agree support p q) : d4655 p = d4655 q := by
  simp only [d4655, h 138 (by decide), agree12 p q h, agree4653 p q h]
theorem nonnegative4655 (p : Pattern) : 0 ≤ d4655 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4653 p)
def d4656 (p : Pattern) : Int := if p 116 then d4655 p else d4654 p
theorem agree4656 (p q : Pattern) (h : Agree support p q) : d4656 p = d4656 q := by
  simp only [d4656, h 116 (by decide), agree4655 p q h, agree4654 p q h]
theorem nonnegative4656 (p : Pattern) : 0 ≤ d4656 p :=
  nonnegative_ite (p 116) (nonnegative4655 p) (nonnegative4654 p)
def d4657 (p : Pattern) : Int := if p 160 then d300 p else d211 p
theorem agree4657 (p q : Pattern) (h : Agree support p q) : d4657 p = d4657 q := by
  simp only [d4657, h 160 (by decide), agree300 p q h, agree211 p q h]
theorem nonnegative4657 (p : Pattern) : 0 ≤ d4657 p :=
  nonnegative_ite (p 160) (nonnegative300 p) (nonnegative211 p)
def d4658 (p : Pattern) : Int := if p 141 then d4657 p else d4632 p
theorem agree4658 (p q : Pattern) (h : Agree support p q) : d4658 p = d4658 q := by
  simp only [d4658, h 141 (by decide), agree4657 p q h, agree4632 p q h]
theorem nonnegative4658 (p : Pattern) : 0 ≤ d4658 p :=
  nonnegative_ite (p 141) (nonnegative4657 p) (nonnegative4632 p)
def d4659 (p : Pattern) : Int := if p 160 then d211 p else d241 p
theorem agree4659 (p q : Pattern) (h : Agree support p q) : d4659 p = d4659 q := by
  simp only [d4659, h 160 (by decide), agree211 p q h, agree241 p q h]
theorem nonnegative4659 (p : Pattern) : 0 ≤ d4659 p :=
  nonnegative_ite (p 160) (nonnegative211 p) (nonnegative241 p)
def d4660 (p : Pattern) : Int := if p 141 then d4652 p else d4659 p
theorem agree4660 (p q : Pattern) (h : Agree support p q) : d4660 p = d4660 q := by
  simp only [d4660, h 141 (by decide), agree4652 p q h, agree4659 p q h]
theorem nonnegative4660 (p : Pattern) : 0 ≤ d4660 p :=
  nonnegative_ite (p 141) (nonnegative4652 p) (nonnegative4659 p)
def d4661 (p : Pattern) : Int := if p 138 then d4660 p else d4658 p
theorem agree4661 (p q : Pattern) (h : Agree support p q) : d4661 p = d4661 q := by
  simp only [d4661, h 138 (by decide), agree4660 p q h, agree4658 p q h]
theorem nonnegative4661 (p : Pattern) : 0 ≤ d4661 p :=
  nonnegative_ite (p 138) (nonnegative4660 p) (nonnegative4658 p)
def d4662 (p : Pattern) : Int := if p 160 then d136 p else d252 p
theorem agree4662 (p q : Pattern) (h : Agree support p q) : d4662 p = d4662 q := by
  simp only [d4662, h 160 (by decide), agree136 p q h, agree252 p q h]
theorem nonnegative4662 (p : Pattern) : 0 ≤ d4662 p :=
  nonnegative_ite (p 160) (nonnegative136 p) (nonnegative252 p)
def d4663 (p : Pattern) : Int := if p 141 then d4652 p else d4662 p
theorem agree4663 (p q : Pattern) (h : Agree support p q) : d4663 p = d4663 q := by
  simp only [d4663, h 141 (by decide), agree4652 p q h, agree4662 p q h]
theorem nonnegative4663 (p : Pattern) : 0 ≤ d4663 p :=
  nonnegative_ite (p 141) (nonnegative4652 p) (nonnegative4662 p)
def d4664 (p : Pattern) : Int := if p 138 then d12 p else d4663 p
theorem agree4664 (p q : Pattern) (h : Agree support p q) : d4664 p = d4664 q := by
  simp only [d4664, h 138 (by decide), agree12 p q h, agree4663 p q h]
theorem nonnegative4664 (p : Pattern) : 0 ≤ d4664 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4663 p)
def d4665 (p : Pattern) : Int := if p 116 then d4664 p else d4661 p
theorem agree4665 (p q : Pattern) (h : Agree support p q) : d4665 p = d4665 q := by
  simp only [d4665, h 116 (by decide), agree4664 p q h, agree4661 p q h]
theorem nonnegative4665 (p : Pattern) : 0 ≤ d4665 p :=
  nonnegative_ite (p 116) (nonnegative4664 p) (nonnegative4661 p)
def d4666 (p : Pattern) : Int := if p 115 then d4665 p else d4656 p
theorem agree4666 (p q : Pattern) (h : Agree support p q) : d4666 p = d4666 q := by
  simp only [d4666, h 115 (by decide), agree4665 p q h, agree4656 p q h]
theorem nonnegative4666 (p : Pattern) : 0 ≤ d4666 p :=
  nonnegative_ite (p 115) (nonnegative4665 p) (nonnegative4656 p)
def d4667 (p : Pattern) : Int := if p 71 then d4666 p else d4631 p
theorem agree4667 (p q : Pattern) (h : Agree support p q) : d4667 p = d4667 q := by
  simp only [d4667, h 71 (by decide), agree4666 p q h, agree4631 p q h]
theorem nonnegative4667 (p : Pattern) : 0 ≤ d4667 p :=
  nonnegative_ite (p 71) (nonnegative4666 p) (nonnegative4631 p)
def d4668 (p : Pattern) : Int := if p 49 then d4667 p else d4649 p
theorem agree4668 (p q : Pattern) (h : Agree support p q) : d4668 p = d4668 q := by
  simp only [d4668, h 49 (by decide), agree4667 p q h, agree4649 p q h]
theorem nonnegative4668 (p : Pattern) : 0 ≤ d4668 p :=
  nonnegative_ite (p 49) (nonnegative4667 p) (nonnegative4649 p)
def d4669 (p : Pattern) : Int := if p 48 then d4668 p else d4641 p
theorem agree4669 (p q : Pattern) (h : Agree support p q) : d4669 p = d4669 q := by
  simp only [d4669, h 48 (by decide), agree4668 p q h, agree4641 p q h]
theorem nonnegative4669 (p : Pattern) : 0 ≤ d4669 p :=
  nonnegative_ite (p 48) (nonnegative4668 p) (nonnegative4641 p)
def d4670 (p : Pattern) : Int := if p 161 then d0 p else d4395 p
theorem agree4670 (p q : Pattern) (h : Agree support p q) : d4670 p = d4670 q := by
  simp only [d4670, h 161 (by decide), agree0 p q h, agree4395 p q h]
theorem nonnegative4670 (p : Pattern) : 0 ≤ d4670 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative4395 p)
def d4671 (p : Pattern) : Int := if p 161 then d0 p else d4394 p
theorem agree4671 (p q : Pattern) (h : Agree support p q) : d4671 p = d4671 q := by
  simp only [d4671, h 161 (by decide), agree0 p q h, agree4394 p q h]
theorem nonnegative4671 (p : Pattern) : 0 ≤ d4671 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative4394 p)
def d4672 (p : Pattern) : Int := if p 162 then d4148 p else d0 p
theorem agree4672 (p q : Pattern) (h : Agree support p q) : d4672 p = d4672 q := by
  simp only [d4672, h 162 (by decide), agree4148 p q h, agree0 p q h]
theorem nonnegative4672 (p : Pattern) : 0 ≤ d4672 p :=
  nonnegative_ite (p 162) (nonnegative4148 p) (nonnegative0 p)
def d4673 (p : Pattern) : Int := if p 161 then d0 p else d4672 p
theorem agree4673 (p q : Pattern) (h : Agree support p q) : d4673 p = d4673 q := by
  simp only [d4673, h 161 (by decide), agree0 p q h, agree4672 p q h]
theorem nonnegative4673 (p : Pattern) : 0 ≤ d4673 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative4672 p)
def d4674 (p : Pattern) : Int := if p 161 then d33 p else d16 p
theorem agree4674 (p q : Pattern) (h : Agree support p q) : d4674 p = d4674 q := by
  simp only [d4674, h 161 (by decide), agree33 p q h, agree16 p q h]
theorem nonnegative4674 (p : Pattern) : 0 ≤ d4674 p :=
  nonnegative_ite (p 161) (nonnegative33 p) (nonnegative16 p)
def d4675 (p : Pattern) : Int := if p 161 then d43 p else d33 p
theorem agree4675 (p q : Pattern) (h : Agree support p q) : d4675 p = d4675 q := by
  simp only [d4675, h 161 (by decide), agree43 p q h, agree33 p q h]
theorem nonnegative4675 (p : Pattern) : 0 ≤ d4675 p :=
  nonnegative_ite (p 161) (nonnegative43 p) (nonnegative33 p)
def d4676 (p : Pattern) : Int := if p 160 then d4675 p else d4674 p
theorem agree4676 (p q : Pattern) (h : Agree support p q) : d4676 p = d4676 q := by
  simp only [d4676, h 160 (by decide), agree4675 p q h, agree4674 p q h]
theorem nonnegative4676 (p : Pattern) : 0 ≤ d4676 p :=
  nonnegative_ite (p 160) (nonnegative4675 p) (nonnegative4674 p)
def d4677 (p : Pattern) : Int := if p 161 then d795 p else d53 p
theorem agree4677 (p q : Pattern) (h : Agree support p q) : d4677 p = d4677 q := by
  simp only [d4677, h 161 (by decide), agree795 p q h, agree53 p q h]
theorem nonnegative4677 (p : Pattern) : 0 ≤ d4677 p :=
  nonnegative_ite (p 161) (nonnegative795 p) (nonnegative53 p)
def d4678 (p : Pattern) : Int := if p 161 then d173 p else d795 p
theorem agree4678 (p q : Pattern) (h : Agree support p q) : d4678 p = d4678 q := by
  simp only [d4678, h 161 (by decide), agree173 p q h, agree795 p q h]
theorem nonnegative4678 (p : Pattern) : 0 ≤ d4678 p :=
  nonnegative_ite (p 161) (nonnegative173 p) (nonnegative795 p)
def d4679 (p : Pattern) : Int := if p 160 then d4678 p else d4677 p
theorem agree4679 (p q : Pattern) (h : Agree support p q) : d4679 p = d4679 q := by
  simp only [d4679, h 160 (by decide), agree4678 p q h, agree4677 p q h]
theorem nonnegative4679 (p : Pattern) : 0 ≤ d4679 p :=
  nonnegative_ite (p 160) (nonnegative4678 p) (nonnegative4677 p)
end NetHack.Sokoban22Refined85
