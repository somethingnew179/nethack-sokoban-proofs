/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes29
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3600 (p : Pattern) : Int := if p 182 then d3599 p else d3582 p
theorem agree3600 (p q : Pattern) (h : Agree support p q) : d3600 p = d3600 q := by
  simp only [d3600, h 182 (by decide), agree3599 p q h, agree3582 p q h]
theorem nonnegative3600 (p : Pattern) : 0 ≤ d3600 p :=
  nonnegative_ite (p 182) (nonnegative3599 p) (nonnegative3582 p)
def d3601 (p : Pattern) : Int := if p 246 then d57 p else d17 p
theorem agree3601 (p q : Pattern) (h : Agree support p q) : d3601 p = d3601 q := by
  simp only [d3601, h 246 (by decide), agree57 p q h, agree17 p q h]
theorem nonnegative3601 (p : Pattern) : 0 ≤ d3601 p :=
  nonnegative_ite (p 246) (nonnegative57 p) (nonnegative17 p)
def d3602 (p : Pattern) : Int := if p 225 then d3601 p else d17 p
theorem agree3602 (p q : Pattern) (h : Agree support p q) : d3602 p = d3602 q := by
  simp only [d3602, h 225 (by decide), agree3601 p q h, agree17 p q h]
theorem nonnegative3602 (p : Pattern) : 0 ≤ d3602 p :=
  nonnegative_ite (p 225) (nonnegative3601 p) (nonnegative17 p)
def d3603 (p : Pattern) : Int := if p 225 then d339 p else d3555 p
theorem agree3603 (p q : Pattern) (h : Agree support p q) : d3603 p = d3603 q := by
  simp only [d3603, h 225 (by decide), agree339 p q h, agree3555 p q h]
theorem nonnegative3603 (p : Pattern) : 0 ≤ d3603 p :=
  nonnegative_ite (p 225) (nonnegative339 p) (nonnegative3555 p)
def d3604 (p : Pattern) : Int := if p 224 then d3603 p else d3602 p
theorem agree3604 (p q : Pattern) (h : Agree support p q) : d3604 p = d3604 q := by
  simp only [d3604, h 224 (by decide), agree3603 p q h, agree3602 p q h]
theorem nonnegative3604 (p : Pattern) : 0 ≤ d3604 p :=
  nonnegative_ite (p 224) (nonnegative3603 p) (nonnegative3602 p)
def d3605 (p : Pattern) : Int := if p 204 then d3604 p else d17 p
theorem agree3605 (p q : Pattern) (h : Agree support p q) : d3605 p = d3605 q := by
  simp only [d3605, h 204 (by decide), agree3604 p q h, agree17 p q h]
theorem nonnegative3605 (p : Pattern) : 0 ≤ d3605 p :=
  nonnegative_ite (p 204) (nonnegative3604 p) (nonnegative17 p)
def d3606 (p : Pattern) : Int := if p 182 then d12 p else d3605 p
theorem agree3606 (p q : Pattern) (h : Agree support p q) : d3606 p = d3606 q := by
  simp only [d3606, h 182 (by decide), agree12 p q h, agree3605 p q h]
theorem nonnegative3606 (p : Pattern) : 0 ≤ d3606 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3605 p)
def d3607 (p : Pattern) : Int := if p 163 then d3606 p else d3600 p
theorem agree3607 (p q : Pattern) (h : Agree support p q) : d3607 p = d3607 q := by
  simp only [d3607, h 163 (by decide), agree3606 p q h, agree3600 p q h]
theorem nonnegative3607 (p : Pattern) : 0 ≤ d3607 p :=
  nonnegative_ite (p 163) (nonnegative3606 p) (nonnegative3600 p)
def d3608 (p : Pattern) : Int := if p 162 then d3607 p else d3596 p
theorem agree3608 (p q : Pattern) (h : Agree support p q) : d3608 p = d3608 q := by
  simp only [d3608, h 162 (by decide), agree3607 p q h, agree3596 p q h]
theorem nonnegative3608 (p : Pattern) : 0 ≤ d3608 p :=
  nonnegative_ite (p 162) (nonnegative3607 p) (nonnegative3596 p)
def d3609 (p : Pattern) : Int := if p 182 then d12 p else d3582 p
theorem agree3609 (p q : Pattern) (h : Agree support p q) : d3609 p = d3609 q := by
  simp only [d3609, h 182 (by decide), agree12 p q h, agree3582 p q h]
theorem nonnegative3609 (p : Pattern) : 0 ≤ d3609 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3582 p)
def d3610 (p : Pattern) : Int := if p 163 then d3606 p else d3609 p
theorem agree3610 (p q : Pattern) (h : Agree support p q) : d3610 p = d3610 q := by
  simp only [d3610, h 163 (by decide), agree3606 p q h, agree3609 p q h]
theorem nonnegative3610 (p : Pattern) : 0 ≤ d3610 p :=
  nonnegative_ite (p 163) (nonnegative3606 p) (nonnegative3609 p)
def d3611 (p : Pattern) : Int := if p 182 then d12 p else d3568 p
theorem agree3611 (p q : Pattern) (h : Agree support p q) : d3611 p = d3611 q := by
  simp only [d3611, h 182 (by decide), agree12 p q h, agree3568 p q h]
theorem nonnegative3611 (p : Pattern) : 0 ≤ d3611 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3568 p)
def d3612 (p : Pattern) : Int := if p 163 then d12 p else d3611 p
theorem agree3612 (p q : Pattern) (h : Agree support p q) : d3612 p = d3612 q := by
  simp only [d3612, h 163 (by decide), agree12 p q h, agree3611 p q h]
theorem nonnegative3612 (p : Pattern) : 0 ≤ d3612 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3611 p)
def d3613 (p : Pattern) : Int := if p 162 then d3612 p else d3610 p
theorem agree3613 (p q : Pattern) (h : Agree support p q) : d3613 p = d3613 q := by
  simp only [d3613, h 162 (by decide), agree3612 p q h, agree3610 p q h]
theorem nonnegative3613 (p : Pattern) : 0 ≤ d3613 p :=
  nonnegative_ite (p 162) (nonnegative3612 p) (nonnegative3610 p)
def d3614 (p : Pattern) : Int := if p 161 then d3613 p else d3608 p
theorem agree3614 (p q : Pattern) (h : Agree support p q) : d3614 p = d3614 q := by
  simp only [d3614, h 161 (by decide), agree3613 p q h, agree3608 p q h]
theorem nonnegative3614 (p : Pattern) : 0 ≤ d3614 p :=
  nonnegative_ite (p 161) (nonnegative3613 p) (nonnegative3608 p)
def d3615 (p : Pattern) : Int := if p 160 then d3614 p else d3576 p
theorem agree3615 (p q : Pattern) (h : Agree support p q) : d3615 p = d3615 q := by
  simp only [d3615, h 160 (by decide), agree3614 p q h, agree3576 p q h]
theorem nonnegative3615 (p : Pattern) : 0 ≤ d3615 p :=
  nonnegative_ite (p 160) (nonnegative3614 p) (nonnegative3576 p)
def d3616 (p : Pattern) : Int := if p 246 then d13 p else d1785 p
theorem agree3616 (p q : Pattern) (h : Agree support p q) : d3616 p = d3616 q := by
  simp only [d3616, h 246 (by decide), agree13 p q h, agree1785 p q h]
theorem nonnegative3616 (p : Pattern) : 0 ≤ d3616 p :=
  nonnegative_ite (p 246) (nonnegative13 p) (nonnegative1785 p)
def d3617 (p : Pattern) : Int := if p 225 then d13 p else d3616 p
theorem agree3617 (p q : Pattern) (h : Agree support p q) : d3617 p = d3617 q := by
  simp only [d3617, h 225 (by decide), agree13 p q h, agree3616 p q h]
theorem nonnegative3617 (p : Pattern) : 0 ≤ d3617 p :=
  nonnegative_ite (p 225) (nonnegative13 p) (nonnegative3616 p)
def d3618 (p : Pattern) : Int := if p 224 then d13 p else d3617 p
theorem agree3618 (p q : Pattern) (h : Agree support p q) : d3618 p = d3618 q := by
  simp only [d3618, h 224 (by decide), agree13 p q h, agree3617 p q h]
theorem nonnegative3618 (p : Pattern) : 0 ≤ d3618 p :=
  nonnegative_ite (p 224) (nonnegative13 p) (nonnegative3617 p)
def d3619 (p : Pattern) : Int := if p 204 then d3545 p else d3618 p
theorem agree3619 (p q : Pattern) (h : Agree support p q) : d3619 p = d3619 q := by
  simp only [d3619, h 204 (by decide), agree3545 p q h, agree3618 p q h]
theorem nonnegative3619 (p : Pattern) : 0 ≤ d3619 p :=
  nonnegative_ite (p 204) (nonnegative3545 p) (nonnegative3618 p)
def d3620 (p : Pattern) : Int := if p 182 then d3550 p else d3619 p
theorem agree3620 (p q : Pattern) (h : Agree support p q) : d3620 p = d3620 q := by
  simp only [d3620, h 182 (by decide), agree3550 p q h, agree3619 p q h]
theorem nonnegative3620 (p : Pattern) : 0 ≤ d3620 p :=
  nonnegative_ite (p 182) (nonnegative3550 p) (nonnegative3619 p)
def d3621 (p : Pattern) : Int := if p 225 then d3585 p else d30 p
theorem agree3621 (p q : Pattern) (h : Agree support p q) : d3621 p = d3621 q := by
  simp only [d3621, h 225 (by decide), agree3585 p q h, agree30 p q h]
theorem nonnegative3621 (p : Pattern) : 0 ≤ d3621 p :=
  nonnegative_ite (p 225) (nonnegative3585 p) (nonnegative30 p)
def d3622 (p : Pattern) : Int := if p 224 then d3585 p else d3621 p
theorem agree3622 (p q : Pattern) (h : Agree support p q) : d3622 p = d3622 q := by
  simp only [d3622, h 224 (by decide), agree3585 p q h, agree3621 p q h]
theorem nonnegative3622 (p : Pattern) : 0 ≤ d3622 p :=
  nonnegative_ite (p 224) (nonnegative3585 p) (nonnegative3621 p)
def d3623 (p : Pattern) : Int := if p 204 then d3622 p else d30 p
theorem agree3623 (p q : Pattern) (h : Agree support p q) : d3623 p = d3623 q := by
  simp only [d3623, h 204 (by decide), agree3622 p q h, agree30 p q h]
theorem nonnegative3623 (p : Pattern) : 0 ≤ d3623 p :=
  nonnegative_ite (p 204) (nonnegative3622 p) (nonnegative30 p)
def d3624 (p : Pattern) : Int := if p 246 then d17 p else d30 p
theorem agree3624 (p q : Pattern) (h : Agree support p q) : d3624 p = d3624 q := by
  simp only [d3624, h 246 (by decide), agree17 p q h, agree30 p q h]
theorem nonnegative3624 (p : Pattern) : 0 ≤ d3624 p :=
  nonnegative_ite (p 246) (nonnegative17 p) (nonnegative30 p)
def d3625 (p : Pattern) : Int := if p 225 then d3624 p else d30 p
theorem agree3625 (p q : Pattern) (h : Agree support p q) : d3625 p = d3625 q := by
  simp only [d3625, h 225 (by decide), agree3624 p q h, agree30 p q h]
theorem nonnegative3625 (p : Pattern) : 0 ≤ d3625 p :=
  nonnegative_ite (p 225) (nonnegative3624 p) (nonnegative30 p)
def d3626 (p : Pattern) : Int := if p 224 then d3624 p else d3625 p
theorem agree3626 (p q : Pattern) (h : Agree support p q) : d3626 p = d3626 q := by
  simp only [d3626, h 224 (by decide), agree3624 p q h, agree3625 p q h]
theorem nonnegative3626 (p : Pattern) : 0 ≤ d3626 p :=
  nonnegative_ite (p 224) (nonnegative3624 p) (nonnegative3625 p)
def d3627 (p : Pattern) : Int := if p 204 then d12 p else d3626 p
theorem agree3627 (p q : Pattern) (h : Agree support p q) : d3627 p = d3627 q := by
  simp only [d3627, h 204 (by decide), agree12 p q h, agree3626 p q h]
theorem nonnegative3627 (p : Pattern) : 0 ≤ d3627 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3626 p)
def d3628 (p : Pattern) : Int := if p 182 then d3627 p else d3623 p
theorem agree3628 (p q : Pattern) (h : Agree support p q) : d3628 p = d3628 q := by
  simp only [d3628, h 182 (by decide), agree3627 p q h, agree3623 p q h]
theorem nonnegative3628 (p : Pattern) : 0 ≤ d3628 p :=
  nonnegative_ite (p 182) (nonnegative3627 p) (nonnegative3623 p)
def d3629 (p : Pattern) : Int := if p 163 then d3628 p else d3620 p
theorem agree3629 (p q : Pattern) (h : Agree support p q) : d3629 p = d3629 q := by
  simp only [d3629, h 163 (by decide), agree3628 p q h, agree3620 p q h]
theorem nonnegative3629 (p : Pattern) : 0 ≤ d3629 p :=
  nonnegative_ite (p 163) (nonnegative3628 p) (nonnegative3620 p)
def d3630 (p : Pattern) : Int := if p 163 then d3573 p else d3563 p
theorem agree3630 (p q : Pattern) (h : Agree support p q) : d3630 p = d3630 q := by
  simp only [d3630, h 163 (by decide), agree3573 p q h, agree3563 p q h]
theorem nonnegative3630 (p : Pattern) : 0 ≤ d3630 p :=
  nonnegative_ite (p 163) (nonnegative3573 p) (nonnegative3563 p)
def d3631 (p : Pattern) : Int := if p 162 then d3630 p else d3629 p
theorem agree3631 (p q : Pattern) (h : Agree support p q) : d3631 p = d3631 q := by
  simp only [d3631, h 162 (by decide), agree3630 p q h, agree3629 p q h]
theorem nonnegative3631 (p : Pattern) : 0 ≤ d3631 p :=
  nonnegative_ite (p 162) (nonnegative3630 p) (nonnegative3629 p)
def d3632 (p : Pattern) : Int := if p 225 then d329 p else d57 p
theorem agree3632 (p q : Pattern) (h : Agree support p q) : d3632 p = d3632 q := by
  simp only [d3632, h 225 (by decide), agree329 p q h, agree57 p q h]
theorem nonnegative3632 (p : Pattern) : 0 ≤ d3632 p :=
  nonnegative_ite (p 225) (nonnegative329 p) (nonnegative57 p)
def d3633 (p : Pattern) : Int := if p 224 then d329 p else d3632 p
theorem agree3633 (p q : Pattern) (h : Agree support p q) : d3633 p = d3633 q := by
  simp only [d3633, h 224 (by decide), agree329 p q h, agree3632 p q h]
theorem nonnegative3633 (p : Pattern) : 0 ≤ d3633 p :=
  nonnegative_ite (p 224) (nonnegative329 p) (nonnegative3632 p)
def d3634 (p : Pattern) : Int := if p 204 then d3633 p else d57 p
theorem agree3634 (p q : Pattern) (h : Agree support p q) : d3634 p = d3634 q := by
  simp only [d3634, h 204 (by decide), agree3633 p q h, agree57 p q h]
theorem nonnegative3634 (p : Pattern) : 0 ≤ d3634 p :=
  nonnegative_ite (p 204) (nonnegative3633 p) (nonnegative57 p)
def d3635 (p : Pattern) : Int := if p 204 then d12 p else d3633 p
theorem agree3635 (p q : Pattern) (h : Agree support p q) : d3635 p = d3635 q := by
  simp only [d3635, h 204 (by decide), agree12 p q h, agree3633 p q h]
theorem nonnegative3635 (p : Pattern) : 0 ≤ d3635 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3633 p)
def d3636 (p : Pattern) : Int := if p 182 then d3635 p else d3634 p
theorem agree3636 (p q : Pattern) (h : Agree support p q) : d3636 p = d3636 q := by
  simp only [d3636, h 182 (by decide), agree3635 p q h, agree3634 p q h]
theorem nonnegative3636 (p : Pattern) : 0 ≤ d3636 p :=
  nonnegative_ite (p 182) (nonnegative3635 p) (nonnegative3634 p)
def d3637 (p : Pattern) : Int := if p 163 then d3636 p else d3563 p
theorem agree3637 (p q : Pattern) (h : Agree support p q) : d3637 p = d3637 q := by
  simp only [d3637, h 163 (by decide), agree3636 p q h, agree3563 p q h]
theorem nonnegative3637 (p : Pattern) : 0 ≤ d3637 p :=
  nonnegative_ite (p 163) (nonnegative3636 p) (nonnegative3563 p)
def d3638 (p : Pattern) : Int := if p 204 then d3598 p else d39 p
theorem agree3638 (p q : Pattern) (h : Agree support p q) : d3638 p = d3638 q := by
  simp only [d3638, h 204 (by decide), agree3598 p q h, agree39 p q h]
theorem nonnegative3638 (p : Pattern) : 0 ≤ d3638 p :=
  nonnegative_ite (p 204) (nonnegative3598 p) (nonnegative39 p)
def d3639 (p : Pattern) : Int := if p 182 then d3599 p else d3638 p
theorem agree3639 (p q : Pattern) (h : Agree support p q) : d3639 p = d3639 q := by
  simp only [d3639, h 182 (by decide), agree3599 p q h, agree3638 p q h]
theorem nonnegative3639 (p : Pattern) : 0 ≤ d3639 p :=
  nonnegative_ite (p 182) (nonnegative3599 p) (nonnegative3638 p)
def d3640 (p : Pattern) : Int := if p 163 then d12 p else d3639 p
theorem agree3640 (p q : Pattern) (h : Agree support p q) : d3640 p = d3640 q := by
  simp only [d3640, h 163 (by decide), agree12 p q h, agree3639 p q h]
theorem nonnegative3640 (p : Pattern) : 0 ≤ d3640 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3639 p)
def d3641 (p : Pattern) : Int := if p 162 then d3640 p else d3637 p
theorem agree3641 (p q : Pattern) (h : Agree support p q) : d3641 p = d3641 q := by
  simp only [d3641, h 162 (by decide), agree3640 p q h, agree3637 p q h]
theorem nonnegative3641 (p : Pattern) : 0 ≤ d3641 p :=
  nonnegative_ite (p 162) (nonnegative3640 p) (nonnegative3637 p)
def d3642 (p : Pattern) : Int := if p 161 then d3641 p else d3631 p
theorem agree3642 (p q : Pattern) (h : Agree support p q) : d3642 p = d3642 q := by
  simp only [d3642, h 161 (by decide), agree3641 p q h, agree3631 p q h]
theorem nonnegative3642 (p : Pattern) : 0 ≤ d3642 p :=
  nonnegative_ite (p 161) (nonnegative3641 p) (nonnegative3631 p)
def d3643 (p : Pattern) : Int := if p 204 then d3587 p else d30 p
theorem agree3643 (p q : Pattern) (h : Agree support p q) : d3643 p = d3643 q := by
  simp only [d3643, h 204 (by decide), agree3587 p q h, agree30 p q h]
theorem nonnegative3643 (p : Pattern) : 0 ≤ d3643 p :=
  nonnegative_ite (p 204) (nonnegative3587 p) (nonnegative30 p)
def d3644 (p : Pattern) : Int := if p 182 then d12 p else d3643 p
theorem agree3644 (p q : Pattern) (h : Agree support p q) : d3644 p = d3644 q := by
  simp only [d3644, h 182 (by decide), agree12 p q h, agree3643 p q h]
theorem nonnegative3644 (p : Pattern) : 0 ≤ d3644 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3643 p)
def d3645 (p : Pattern) : Int := if p 163 then d3644 p else d3595 p
theorem agree3645 (p q : Pattern) (h : Agree support p q) : d3645 p = d3645 q := by
  simp only [d3645, h 163 (by decide), agree3644 p q h, agree3595 p q h]
theorem nonnegative3645 (p : Pattern) : 0 ≤ d3645 p :=
  nonnegative_ite (p 163) (nonnegative3644 p) (nonnegative3595 p)
def d3646 (p : Pattern) : Int := if p 163 then d3611 p else d3606 p
theorem agree3646 (p q : Pattern) (h : Agree support p q) : d3646 p = d3646 q := by
  simp only [d3646, h 163 (by decide), agree3611 p q h, agree3606 p q h]
theorem nonnegative3646 (p : Pattern) : 0 ≤ d3646 p :=
  nonnegative_ite (p 163) (nonnegative3611 p) (nonnegative3606 p)
def d3647 (p : Pattern) : Int := if p 162 then d3646 p else d3645 p
theorem agree3647 (p q : Pattern) (h : Agree support p q) : d3647 p = d3647 q := by
  simp only [d3647, h 162 (by decide), agree3646 p q h, agree3645 p q h]
theorem nonnegative3647 (p : Pattern) : 0 ≤ d3647 p :=
  nonnegative_ite (p 162) (nonnegative3646 p) (nonnegative3645 p)
def d3648 (p : Pattern) : Int := if p 182 then d12 p else d3634 p
theorem agree3648 (p q : Pattern) (h : Agree support p q) : d3648 p = d3648 q := by
  simp only [d3648, h 182 (by decide), agree12 p q h, agree3634 p q h]
theorem nonnegative3648 (p : Pattern) : 0 ≤ d3648 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3634 p)
def d3649 (p : Pattern) : Int := if p 163 then d3648 p else d3606 p
theorem agree3649 (p q : Pattern) (h : Agree support p q) : d3649 p = d3649 q := by
  simp only [d3649, h 163 (by decide), agree3648 p q h, agree3606 p q h]
theorem nonnegative3649 (p : Pattern) : 0 ≤ d3649 p :=
  nonnegative_ite (p 163) (nonnegative3648 p) (nonnegative3606 p)
def d3650 (p : Pattern) : Int := if p 182 then d12 p else d3638 p
theorem agree3650 (p q : Pattern) (h : Agree support p q) : d3650 p = d3650 q := by
  simp only [d3650, h 182 (by decide), agree12 p q h, agree3638 p q h]
theorem nonnegative3650 (p : Pattern) : 0 ≤ d3650 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3638 p)
def d3651 (p : Pattern) : Int := if p 163 then d12 p else d3650 p
theorem agree3651 (p q : Pattern) (h : Agree support p q) : d3651 p = d3651 q := by
  simp only [d3651, h 163 (by decide), agree12 p q h, agree3650 p q h]
theorem nonnegative3651 (p : Pattern) : 0 ≤ d3651 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3650 p)
def d3652 (p : Pattern) : Int := if p 162 then d3651 p else d3649 p
theorem agree3652 (p q : Pattern) (h : Agree support p q) : d3652 p = d3652 q := by
  simp only [d3652, h 162 (by decide), agree3651 p q h, agree3649 p q h]
theorem nonnegative3652 (p : Pattern) : 0 ≤ d3652 p :=
  nonnegative_ite (p 162) (nonnegative3651 p) (nonnegative3649 p)
def d3653 (p : Pattern) : Int := if p 161 then d3652 p else d3647 p
theorem agree3653 (p q : Pattern) (h : Agree support p q) : d3653 p = d3653 q := by
  simp only [d3653, h 161 (by decide), agree3652 p q h, agree3647 p q h]
theorem nonnegative3653 (p : Pattern) : 0 ≤ d3653 p :=
  nonnegative_ite (p 161) (nonnegative3652 p) (nonnegative3647 p)
def d3654 (p : Pattern) : Int := if p 160 then d3653 p else d3642 p
theorem agree3654 (p q : Pattern) (h : Agree support p q) : d3654 p = d3654 q := by
  simp only [d3654, h 160 (by decide), agree3653 p q h, agree3642 p q h]
theorem nonnegative3654 (p : Pattern) : 0 ≤ d3654 p :=
  nonnegative_ite (p 160) (nonnegative3653 p) (nonnegative3642 p)
def d3655 (p : Pattern) : Int := if p 141 then d3654 p else d3615 p
theorem agree3655 (p q : Pattern) (h : Agree support p q) : d3655 p = d3655 q := by
  simp only [d3655, h 141 (by decide), agree3654 p q h, agree3615 p q h]
theorem nonnegative3655 (p : Pattern) : 0 ≤ d3655 p :=
  nonnegative_ite (p 141) (nonnegative3654 p) (nonnegative3615 p)
def d3656 (p : Pattern) : Int := if p 225 then d3577 p else d3543 p
theorem agree3656 (p q : Pattern) (h : Agree support p q) : d3656 p = d3656 q := by
  simp only [d3656, h 225 (by decide), agree3577 p q h, agree3543 p q h]
theorem nonnegative3656 (p : Pattern) : 0 ≤ d3656 p :=
  nonnegative_ite (p 225) (nonnegative3577 p) (nonnegative3543 p)
def d3657 (p : Pattern) : Int := if p 224 then d3656 p else d3578 p
theorem agree3657 (p q : Pattern) (h : Agree support p q) : d3657 p = d3657 q := by
  simp only [d3657, h 224 (by decide), agree3656 p q h, agree3578 p q h]
theorem nonnegative3657 (p : Pattern) : 0 ≤ d3657 p :=
  nonnegative_ite (p 224) (nonnegative3656 p) (nonnegative3578 p)
def d3658 (p : Pattern) : Int := if p 204 then d3657 p else d13 p
theorem agree3658 (p q : Pattern) (h : Agree support p q) : d3658 p = d3658 q := by
  simp only [d3658, h 204 (by decide), agree3657 p q h, agree13 p q h]
theorem nonnegative3658 (p : Pattern) : 0 ≤ d3658 p :=
  nonnegative_ite (p 204) (nonnegative3657 p) (nonnegative13 p)
def d3659 (p : Pattern) : Int := if p 204 then d12 p else d3545 p
theorem agree3659 (p q : Pattern) (h : Agree support p q) : d3659 p = d3659 q := by
  simp only [d3659, h 204 (by decide), agree12 p q h, agree3545 p q h]
theorem nonnegative3659 (p : Pattern) : 0 ≤ d3659 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3545 p)
def d3660 (p : Pattern) : Int := if p 182 then d3659 p else d3658 p
theorem agree3660 (p q : Pattern) (h : Agree support p q) : d3660 p = d3660 q := by
  simp only [d3660, h 182 (by decide), agree3659 p q h, agree3658 p q h]
theorem nonnegative3660 (p : Pattern) : 0 ≤ d3660 p :=
  nonnegative_ite (p 182) (nonnegative3659 p) (nonnegative3658 p)
def d3661 (p : Pattern) : Int := if p 246 then d190 p else d13 p
theorem agree3661 (p q : Pattern) (h : Agree support p q) : d3661 p = d3661 q := by
  simp only [d3661, h 246 (by decide), agree190 p q h, agree13 p q h]
theorem nonnegative3661 (p : Pattern) : 0 ≤ d3661 p :=
  nonnegative_ite (p 246) (nonnegative190 p) (nonnegative13 p)
def d3662 (p : Pattern) : Int := if p 225 then d3661 p else d3543 p
theorem agree3662 (p q : Pattern) (h : Agree support p q) : d3662 p = d3662 q := by
  simp only [d3662, h 225 (by decide), agree3661 p q h, agree3543 p q h]
theorem nonnegative3662 (p : Pattern) : 0 ≤ d3662 p :=
  nonnegative_ite (p 225) (nonnegative3661 p) (nonnegative3543 p)
def d3663 (p : Pattern) : Int := if p 224 then d3662 p else d3578 p
theorem agree3663 (p q : Pattern) (h : Agree support p q) : d3663 p = d3663 q := by
  simp only [d3663, h 224 (by decide), agree3662 p q h, agree3578 p q h]
theorem nonnegative3663 (p : Pattern) : 0 ≤ d3663 p :=
  nonnegative_ite (p 224) (nonnegative3662 p) (nonnegative3578 p)
def d3664 (p : Pattern) : Int := if p 204 then d12 p else d3663 p
theorem agree3664 (p q : Pattern) (h : Agree support p q) : d3664 p = d3664 q := by
  simp only [d3664, h 204 (by decide), agree12 p q h, agree3663 p q h]
theorem nonnegative3664 (p : Pattern) : 0 ≤ d3664 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3663 p)
def d3665 (p : Pattern) : Int := if p 182 then d3664 p else d3582 p
theorem agree3665 (p q : Pattern) (h : Agree support p q) : d3665 p = d3665 q := by
  simp only [d3665, h 182 (by decide), agree3664 p q h, agree3582 p q h]
theorem nonnegative3665 (p : Pattern) : 0 ≤ d3665 p :=
  nonnegative_ite (p 182) (nonnegative3664 p) (nonnegative3582 p)
def d3666 (p : Pattern) : Int := if p 163 then d3665 p else d3660 p
theorem agree3666 (p q : Pattern) (h : Agree support p q) : d3666 p = d3666 q := by
  simp only [d3666, h 163 (by decide), agree3665 p q h, agree3660 p q h]
theorem nonnegative3666 (p : Pattern) : 0 ≤ d3666 p :=
  nonnegative_ite (p 163) (nonnegative3665 p) (nonnegative3660 p)
def d3667 (p : Pattern) : Int := if p 204 then d12 p else d3581 p
theorem agree3667 (p q : Pattern) (h : Agree support p q) : d3667 p = d3667 q := by
  simp only [d3667, h 204 (by decide), agree12 p q h, agree3581 p q h]
theorem nonnegative3667 (p : Pattern) : 0 ≤ d3667 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3581 p)
def d3668 (p : Pattern) : Int := if p 182 then d3667 p else d3582 p
theorem agree3668 (p q : Pattern) (h : Agree support p q) : d3668 p = d3668 q := by
  simp only [d3668, h 182 (by decide), agree3667 p q h, agree3582 p q h]
theorem nonnegative3668 (p : Pattern) : 0 ≤ d3668 p :=
  nonnegative_ite (p 182) (nonnegative3667 p) (nonnegative3582 p)
def d3669 (p : Pattern) : Int := if p 204 then d12 p else d3604 p
theorem agree3669 (p q : Pattern) (h : Agree support p q) : d3669 p = d3669 q := by
  simp only [d3669, h 204 (by decide), agree12 p q h, agree3604 p q h]
theorem nonnegative3669 (p : Pattern) : 0 ≤ d3669 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3604 p)
def d3670 (p : Pattern) : Int := if p 182 then d3669 p else d3605 p
theorem agree3670 (p q : Pattern) (h : Agree support p q) : d3670 p = d3670 q := by
  simp only [d3670, h 182 (by decide), agree3669 p q h, agree3605 p q h]
theorem nonnegative3670 (p : Pattern) : 0 ≤ d3670 p :=
  nonnegative_ite (p 182) (nonnegative3669 p) (nonnegative3605 p)
def d3671 (p : Pattern) : Int := if p 163 then d3670 p else d3668 p
theorem agree3671 (p q : Pattern) (h : Agree support p q) : d3671 p = d3671 q := by
  simp only [d3671, h 163 (by decide), agree3670 p q h, agree3668 p q h]
theorem nonnegative3671 (p : Pattern) : 0 ≤ d3671 p :=
  nonnegative_ite (p 163) (nonnegative3670 p) (nonnegative3668 p)
def d3672 (p : Pattern) : Int := if p 162 then d3671 p else d3666 p
theorem agree3672 (p q : Pattern) (h : Agree support p q) : d3672 p = d3672 q := by
  simp only [d3672, h 162 (by decide), agree3671 p q h, agree3666 p q h]
theorem nonnegative3672 (p : Pattern) : 0 ≤ d3672 p :=
  nonnegative_ite (p 162) (nonnegative3671 p) (nonnegative3666 p)
def d3673 (p : Pattern) : Int := if p 204 then d12 p else d3567 p
theorem agree3673 (p q : Pattern) (h : Agree support p q) : d3673 p = d3673 q := by
  simp only [d3673, h 204 (by decide), agree12 p q h, agree3567 p q h]
theorem nonnegative3673 (p : Pattern) : 0 ≤ d3673 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3567 p)
def d3674 (p : Pattern) : Int := if p 182 then d3673 p else d3568 p
theorem agree3674 (p q : Pattern) (h : Agree support p q) : d3674 p = d3674 q := by
  simp only [d3674, h 182 (by decide), agree3673 p q h, agree3568 p q h]
theorem nonnegative3674 (p : Pattern) : 0 ≤ d3674 p :=
  nonnegative_ite (p 182) (nonnegative3673 p) (nonnegative3568 p)
def d3675 (p : Pattern) : Int := if p 163 then d12 p else d3674 p
theorem agree3675 (p q : Pattern) (h : Agree support p q) : d3675 p = d3675 q := by
  simp only [d3675, h 163 (by decide), agree12 p q h, agree3674 p q h]
theorem nonnegative3675 (p : Pattern) : 0 ≤ d3675 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3674 p)
def d3676 (p : Pattern) : Int := if p 162 then d3675 p else d3671 p
theorem agree3676 (p q : Pattern) (h : Agree support p q) : d3676 p = d3676 q := by
  simp only [d3676, h 162 (by decide), agree3675 p q h, agree3671 p q h]
theorem nonnegative3676 (p : Pattern) : 0 ≤ d3676 p :=
  nonnegative_ite (p 162) (nonnegative3675 p) (nonnegative3671 p)
def d3677 (p : Pattern) : Int := if p 161 then d3676 p else d3672 p
theorem agree3677 (p q : Pattern) (h : Agree support p q) : d3677 p = d3677 q := by
  simp only [d3677, h 161 (by decide), agree3676 p q h, agree3672 p q h]
theorem nonnegative3677 (p : Pattern) : 0 ≤ d3677 p :=
  nonnegative_ite (p 161) (nonnegative3676 p) (nonnegative3672 p)
def d3678 (p : Pattern) : Int := if p 182 then d3588 p else d3643 p
theorem agree3678 (p q : Pattern) (h : Agree support p q) : d3678 p = d3678 q := by
  simp only [d3678, h 182 (by decide), agree3588 p q h, agree3643 p q h]
theorem nonnegative3678 (p : Pattern) : 0 ≤ d3678 p :=
  nonnegative_ite (p 182) (nonnegative3588 p) (nonnegative3643 p)
def d3679 (p : Pattern) : Int := if p 204 then d3593 p else d34 p
theorem agree3679 (p q : Pattern) (h : Agree support p q) : d3679 p = d3679 q := by
  simp only [d3679, h 204 (by decide), agree3593 p q h, agree34 p q h]
theorem nonnegative3679 (p : Pattern) : 0 ≤ d3679 p :=
  nonnegative_ite (p 204) (nonnegative3593 p) (nonnegative34 p)
def d3680 (p : Pattern) : Int := if p 182 then d3594 p else d3679 p
theorem agree3680 (p q : Pattern) (h : Agree support p q) : d3680 p = d3680 q := by
  simp only [d3680, h 182 (by decide), agree3594 p q h, agree3679 p q h]
theorem nonnegative3680 (p : Pattern) : 0 ≤ d3680 p :=
  nonnegative_ite (p 182) (nonnegative3594 p) (nonnegative3679 p)
def d3681 (p : Pattern) : Int := if p 163 then d3680 p else d3678 p
theorem agree3681 (p q : Pattern) (h : Agree support p q) : d3681 p = d3681 q := by
  simp only [d3681, h 163 (by decide), agree3680 p q h, agree3678 p q h]
theorem nonnegative3681 (p : Pattern) : 0 ≤ d3681 p :=
  nonnegative_ite (p 163) (nonnegative3680 p) (nonnegative3678 p)
def d3682 (p : Pattern) : Int := if p 162 then d3640 p else d3681 p
theorem agree3682 (p q : Pattern) (h : Agree support p q) : d3682 p = d3682 q := by
  simp only [d3682, h 162 (by decide), agree3640 p q h, agree3681 p q h]
theorem nonnegative3682 (p : Pattern) : 0 ≤ d3682 p :=
  nonnegative_ite (p 162) (nonnegative3640 p) (nonnegative3681 p)
def d3683 (p : Pattern) : Int := if p 161 then d12 p else d3682 p
theorem agree3683 (p q : Pattern) (h : Agree support p q) : d3683 p = d3683 q := by
  simp only [d3683, h 161 (by decide), agree12 p q h, agree3682 p q h]
theorem nonnegative3683 (p : Pattern) : 0 ≤ d3683 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3682 p)
def d3684 (p : Pattern) : Int := if p 160 then d3683 p else d3677 p
theorem agree3684 (p q : Pattern) (h : Agree support p q) : d3684 p = d3684 q := by
  simp only [d3684, h 160 (by decide), agree3683 p q h, agree3677 p q h]
theorem nonnegative3684 (p : Pattern) : 0 ≤ d3684 p :=
  nonnegative_ite (p 160) (nonnegative3683 p) (nonnegative3677 p)
def d3685 (p : Pattern) : Int := if p 163 then d3678 p else d3665 p
theorem agree3685 (p q : Pattern) (h : Agree support p q) : d3685 p = d3685 q := by
  simp only [d3685, h 163 (by decide), agree3678 p q h, agree3665 p q h]
theorem nonnegative3685 (p : Pattern) : 0 ≤ d3685 p :=
  nonnegative_ite (p 163) (nonnegative3678 p) (nonnegative3665 p)
def d3686 (p : Pattern) : Int := if p 163 then d3674 p else d3670 p
theorem agree3686 (p q : Pattern) (h : Agree support p q) : d3686 p = d3686 q := by
  simp only [d3686, h 163 (by decide), agree3674 p q h, agree3670 p q h]
theorem nonnegative3686 (p : Pattern) : 0 ≤ d3686 p :=
  nonnegative_ite (p 163) (nonnegative3674 p) (nonnegative3670 p)
def d3687 (p : Pattern) : Int := if p 162 then d3686 p else d3685 p
theorem agree3687 (p q : Pattern) (h : Agree support p q) : d3687 p = d3687 q := by
  simp only [d3687, h 162 (by decide), agree3686 p q h, agree3685 p q h]
theorem nonnegative3687 (p : Pattern) : 0 ≤ d3687 p :=
  nonnegative_ite (p 162) (nonnegative3686 p) (nonnegative3685 p)
def d3688 (p : Pattern) : Int := if p 163 then d3636 p else d3670 p
theorem agree3688 (p q : Pattern) (h : Agree support p q) : d3688 p = d3688 q := by
  simp only [d3688, h 163 (by decide), agree3636 p q h, agree3670 p q h]
theorem nonnegative3688 (p : Pattern) : 0 ≤ d3688 p :=
  nonnegative_ite (p 163) (nonnegative3636 p) (nonnegative3670 p)
def d3689 (p : Pattern) : Int := if p 162 then d3640 p else d3688 p
theorem agree3689 (p q : Pattern) (h : Agree support p q) : d3689 p = d3689 q := by
  simp only [d3689, h 162 (by decide), agree3640 p q h, agree3688 p q h]
theorem nonnegative3689 (p : Pattern) : 0 ≤ d3689 p :=
  nonnegative_ite (p 162) (nonnegative3640 p) (nonnegative3688 p)
def d3690 (p : Pattern) : Int := if p 161 then d3689 p else d3687 p
theorem agree3690 (p q : Pattern) (h : Agree support p q) : d3690 p = d3690 q := by
  simp only [d3690, h 161 (by decide), agree3689 p q h, agree3687 p q h]
theorem nonnegative3690 (p : Pattern) : 0 ≤ d3690 p :=
  nonnegative_ite (p 161) (nonnegative3689 p) (nonnegative3687 p)
def d3691 (p : Pattern) : Int := if p 163 then d12 p else d3680 p
theorem agree3691 (p q : Pattern) (h : Agree support p q) : d3691 p = d3691 q := by
  simp only [d3691, h 163 (by decide), agree12 p q h, agree3680 p q h]
theorem nonnegative3691 (p : Pattern) : 0 ≤ d3691 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3680 p)
def d3692 (p : Pattern) : Int := if p 162 then d12 p else d3691 p
theorem agree3692 (p q : Pattern) (h : Agree support p q) : d3692 p = d3692 q := by
  simp only [d3692, h 162 (by decide), agree12 p q h, agree3691 p q h]
theorem nonnegative3692 (p : Pattern) : 0 ≤ d3692 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3691 p)
def d3693 (p : Pattern) : Int := if p 161 then d12 p else d3692 p
theorem agree3693 (p q : Pattern) (h : Agree support p q) : d3693 p = d3693 q := by
  simp only [d3693, h 161 (by decide), agree12 p q h, agree3692 p q h]
theorem nonnegative3693 (p : Pattern) : 0 ≤ d3693 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3692 p)
def d3694 (p : Pattern) : Int := if p 160 then d3693 p else d3690 p
theorem agree3694 (p q : Pattern) (h : Agree support p q) : d3694 p = d3694 q := by
  simp only [d3694, h 160 (by decide), agree3693 p q h, agree3690 p q h]
theorem nonnegative3694 (p : Pattern) : 0 ≤ d3694 p :=
  nonnegative_ite (p 160) (nonnegative3693 p) (nonnegative3690 p)
def d3695 (p : Pattern) : Int := if p 141 then d3694 p else d3684 p
theorem agree3695 (p q : Pattern) (h : Agree support p q) : d3695 p = d3695 q := by
  simp only [d3695, h 141 (by decide), agree3694 p q h, agree3684 p q h]
theorem nonnegative3695 (p : Pattern) : 0 ≤ d3695 p :=
  nonnegative_ite (p 141) (nonnegative3694 p) (nonnegative3684 p)
def d3696 (p : Pattern) : Int := if p 138 then d3695 p else d3655 p
theorem agree3696 (p q : Pattern) (h : Agree support p q) : d3696 p = d3696 q := by
  simp only [d3696, h 138 (by decide), agree3695 p q h, agree3655 p q h]
theorem nonnegative3696 (p : Pattern) : 0 ≤ d3696 p :=
  nonnegative_ite (p 138) (nonnegative3695 p) (nonnegative3655 p)
def d3697 (p : Pattern) : Int := if p 163 then d3639 p else d3674 p
theorem agree3697 (p q : Pattern) (h : Agree support p q) : d3697 p = d3697 q := by
  simp only [d3697, h 163 (by decide), agree3639 p q h, agree3674 p q h]
theorem nonnegative3697 (p : Pattern) : 0 ≤ d3697 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3674 p)
def d3698 (p : Pattern) : Int := if p 162 then d3640 p else d3697 p
theorem agree3698 (p q : Pattern) (h : Agree support p q) : d3698 p = d3698 q := by
  simp only [d3698, h 162 (by decide), agree3640 p q h, agree3697 p q h]
theorem nonnegative3698 (p : Pattern) : 0 ≤ d3698 p :=
  nonnegative_ite (p 162) (nonnegative3640 p) (nonnegative3697 p)
def d3699 (p : Pattern) : Int := if p 162 then d12 p else d3640 p
theorem agree3699 (p q : Pattern) (h : Agree support p q) : d3699 p = d3699 q := by
  simp only [d3699, h 162 (by decide), agree12 p q h, agree3640 p q h]
theorem nonnegative3699 (p : Pattern) : 0 ≤ d3699 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3640 p)
def d3700 (p : Pattern) : Int := if p 161 then d3699 p else d3698 p
theorem agree3700 (p q : Pattern) (h : Agree support p q) : d3700 p = d3700 q := by
  simp only [d3700, h 161 (by decide), agree3699 p q h, agree3698 p q h]
theorem nonnegative3700 (p : Pattern) : 0 ≤ d3700 p :=
  nonnegative_ite (p 161) (nonnegative3699 p) (nonnegative3698 p)
def d3701 (p : Pattern) : Int := if p 161 then d12 p else d3699 p
theorem agree3701 (p q : Pattern) (h : Agree support p q) : d3701 p = d3701 q := by
  simp only [d3701, h 161 (by decide), agree12 p q h, agree3699 p q h]
theorem nonnegative3701 (p : Pattern) : 0 ≤ d3701 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative3699 p)
def d3702 (p : Pattern) : Int := if p 160 then d3701 p else d3700 p
theorem agree3702 (p q : Pattern) (h : Agree support p q) : d3702 p = d3702 q := by
  simp only [d3702, h 160 (by decide), agree3701 p q h, agree3700 p q h]
theorem nonnegative3702 (p : Pattern) : 0 ≤ d3702 p :=
  nonnegative_ite (p 160) (nonnegative3701 p) (nonnegative3700 p)
def d3703 (p : Pattern) : Int := if p 160 then d12 p else d3701 p
theorem agree3703 (p q : Pattern) (h : Agree support p q) : d3703 p = d3703 q := by
  simp only [d3703, h 160 (by decide), agree12 p q h, agree3701 p q h]
theorem nonnegative3703 (p : Pattern) : 0 ≤ d3703 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative3701 p)
def d3704 (p : Pattern) : Int := if p 141 then d3703 p else d3702 p
theorem agree3704 (p q : Pattern) (h : Agree support p q) : d3704 p = d3704 q := by
  simp only [d3704, h 141 (by decide), agree3703 p q h, agree3702 p q h]
theorem nonnegative3704 (p : Pattern) : 0 ≤ d3704 p :=
  nonnegative_ite (p 141) (nonnegative3703 p) (nonnegative3702 p)
def d3705 (p : Pattern) : Int := if p 138 then d3704 p else d3695 p
theorem agree3705 (p q : Pattern) (h : Agree support p q) : d3705 p = d3705 q := by
  simp only [d3705, h 138 (by decide), agree3704 p q h, agree3695 p q h]
theorem nonnegative3705 (p : Pattern) : 0 ≤ d3705 p :=
  nonnegative_ite (p 138) (nonnegative3704 p) (nonnegative3695 p)
def d3706 (p : Pattern) : Int := if p 116 then d3705 p else d3696 p
theorem agree3706 (p q : Pattern) (h : Agree support p q) : d3706 p = d3706 q := by
  simp only [d3706, h 116 (by decide), agree3705 p q h, agree3696 p q h]
theorem nonnegative3706 (p : Pattern) : 0 ≤ d3706 p :=
  nonnegative_ite (p 116) (nonnegative3705 p) (nonnegative3696 p)
def d3707 (p : Pattern) : Int := if p 162 then d3564 p else d3553 p
theorem agree3707 (p q : Pattern) (h : Agree support p q) : d3707 p = d3707 q := by
  simp only [d3707, h 162 (by decide), agree3564 p q h, agree3553 p q h]
theorem nonnegative3707 (p : Pattern) : 0 ≤ d3707 p :=
  nonnegative_ite (p 162) (nonnegative3564 p) (nonnegative3553 p)
def d3708 (p : Pattern) : Int := if p 161 then d3575 p else d3707 p
theorem agree3708 (p q : Pattern) (h : Agree support p q) : d3708 p = d3708 q := by
  simp only [d3708, h 161 (by decide), agree3575 p q h, agree3707 p q h]
theorem nonnegative3708 (p : Pattern) : 0 ≤ d3708 p :=
  nonnegative_ite (p 161) (nonnegative3575 p) (nonnegative3707 p)
def d3709 (p : Pattern) : Int := if p 160 then d3614 p else d3708 p
theorem agree3709 (p q : Pattern) (h : Agree support p q) : d3709 p = d3709 q := by
  simp only [d3709, h 160 (by decide), agree3614 p q h, agree3708 p q h]
theorem nonnegative3709 (p : Pattern) : 0 ≤ d3709 p :=
  nonnegative_ite (p 160) (nonnegative3614 p) (nonnegative3708 p)
def d3710 (p : Pattern) : Int := if p 163 then d3628 p else d3553 p
theorem agree3710 (p q : Pattern) (h : Agree support p q) : d3710 p = d3710 q := by
  simp only [d3710, h 163 (by decide), agree3628 p q h, agree3553 p q h]
theorem nonnegative3710 (p : Pattern) : 0 ≤ d3710 p :=
  nonnegative_ite (p 163) (nonnegative3628 p) (nonnegative3553 p)
def d3711 (p : Pattern) : Int := if p 162 then d3630 p else d3710 p
theorem agree3711 (p q : Pattern) (h : Agree support p q) : d3711 p = d3711 q := by
  simp only [d3711, h 162 (by decide), agree3630 p q h, agree3710 p q h]
theorem nonnegative3711 (p : Pattern) : 0 ≤ d3711 p :=
  nonnegative_ite (p 162) (nonnegative3630 p) (nonnegative3710 p)
def d3712 (p : Pattern) : Int := if p 161 then d3641 p else d3711 p
theorem agree3712 (p q : Pattern) (h : Agree support p q) : d3712 p = d3712 q := by
  simp only [d3712, h 161 (by decide), agree3641 p q h, agree3711 p q h]
theorem nonnegative3712 (p : Pattern) : 0 ≤ d3712 p :=
  nonnegative_ite (p 161) (nonnegative3641 p) (nonnegative3711 p)
def d3713 (p : Pattern) : Int := if p 160 then d3653 p else d3712 p
theorem agree3713 (p q : Pattern) (h : Agree support p q) : d3713 p = d3713 q := by
  simp only [d3713, h 160 (by decide), agree3653 p q h, agree3712 p q h]
theorem nonnegative3713 (p : Pattern) : 0 ≤ d3713 p :=
  nonnegative_ite (p 160) (nonnegative3653 p) (nonnegative3712 p)
def d3714 (p : Pattern) : Int := if p 141 then d3713 p else d3709 p
theorem agree3714 (p q : Pattern) (h : Agree support p q) : d3714 p = d3714 q := by
  simp only [d3714, h 141 (by decide), agree3713 p q h, agree3709 p q h]
theorem nonnegative3714 (p : Pattern) : 0 ≤ d3714 p :=
  nonnegative_ite (p 141) (nonnegative3713 p) (nonnegative3709 p)
def d3715 (p : Pattern) : Int := if p 138 then d3695 p else d3714 p
theorem agree3715 (p q : Pattern) (h : Agree support p q) : d3715 p = d3715 q := by
  simp only [d3715, h 138 (by decide), agree3695 p q h, agree3714 p q h]
theorem nonnegative3715 (p : Pattern) : 0 ≤ d3715 p :=
  nonnegative_ite (p 138) (nonnegative3695 p) (nonnegative3714 p)
def d3716 (p : Pattern) : Int := if p 138 then d12 p else d3695 p
theorem agree3716 (p q : Pattern) (h : Agree support p q) : d3716 p = d3716 q := by
  simp only [d3716, h 138 (by decide), agree12 p q h, agree3695 p q h]
theorem nonnegative3716 (p : Pattern) : 0 ≤ d3716 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative3695 p)
def d3717 (p : Pattern) : Int := if p 116 then d3716 p else d3715 p
theorem agree3717 (p q : Pattern) (h : Agree support p q) : d3717 p = d3717 q := by
  simp only [d3717, h 116 (by decide), agree3716 p q h, agree3715 p q h]
theorem nonnegative3717 (p : Pattern) : 0 ≤ d3717 p :=
  nonnegative_ite (p 116) (nonnegative3716 p) (nonnegative3715 p)
def d3718 (p : Pattern) : Int := if p 115 then d3717 p else d3706 p
theorem agree3718 (p q : Pattern) (h : Agree support p q) : d3718 p = d3718 q := by
  simp only [d3718, h 115 (by decide), agree3717 p q h, agree3706 p q h]
theorem nonnegative3718 (p : Pattern) : 0 ≤ d3718 p :=
  nonnegative_ite (p 115) (nonnegative3717 p) (nonnegative3706 p)
def d3719 (p : Pattern) : Int := if p 246 then d13 p else d2051 p
theorem agree3719 (p q : Pattern) (h : Agree support p q) : d3719 p = d3719 q := by
  simp only [d3719, h 246 (by decide), agree13 p q h, agree2051 p q h]
theorem nonnegative3719 (p : Pattern) : 0 ≤ d3719 p :=
  nonnegative_ite (p 246) (nonnegative13 p) (nonnegative2051 p)
end NetHack.Sokoban22Refined85
