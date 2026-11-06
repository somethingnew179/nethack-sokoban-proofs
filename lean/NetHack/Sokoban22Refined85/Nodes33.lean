/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d3960 (p : Pattern) : Int := if p 138 then d3959 p else d3953 p
theorem agree3960 (p q : Pattern) (h : Agree support p q) : d3960 p = d3960 q := by
  simp only [d3960, h 138 (by decide), agree3959 p q h, agree3953 p q h]
theorem nonnegative3960 (p : Pattern) : 0 ≤ d3960 p :=
  nonnegative_ite (p 138) (nonnegative3959 p) (nonnegative3953 p)
def d3961 (p : Pattern) : Int := if p 138 then d3859 p else d3959 p
theorem agree3961 (p q : Pattern) (h : Agree support p q) : d3961 p = d3961 q := by
  simp only [d3961, h 138 (by decide), agree3859 p q h, agree3959 p q h]
theorem nonnegative3961 (p : Pattern) : 0 ≤ d3961 p :=
  nonnegative_ite (p 138) (nonnegative3859 p) (nonnegative3959 p)
def d3962 (p : Pattern) : Int := if p 116 then d3961 p else d3960 p
theorem agree3962 (p q : Pattern) (h : Agree support p q) : d3962 p = d3962 q := by
  simp only [d3962, h 116 (by decide), agree3961 p q h, agree3960 p q h]
theorem nonnegative3962 (p : Pattern) : 0 ≤ d3962 p :=
  nonnegative_ite (p 116) (nonnegative3961 p) (nonnegative3960 p)
def d3963 (p : Pattern) : Int := if p 204 then d3825 p else d102 p
theorem agree3963 (p q : Pattern) (h : Agree support p q) : d3963 p = d3963 q := by
  simp only [d3963, h 204 (by decide), agree3825 p q h, agree102 p q h]
theorem nonnegative3963 (p : Pattern) : 0 ≤ d3963 p :=
  nonnegative_ite (p 204) (nonnegative3825 p) (nonnegative102 p)
def d3964 (p : Pattern) : Int := if p 204 then d12 p else d3819 p
theorem agree3964 (p q : Pattern) (h : Agree support p q) : d3964 p = d3964 q := by
  simp only [d3964, h 204 (by decide), agree12 p q h, agree3819 p q h]
theorem nonnegative3964 (p : Pattern) : 0 ≤ d3964 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3819 p)
def d3965 (p : Pattern) : Int := if p 182 then d3964 p else d3963 p
theorem agree3965 (p q : Pattern) (h : Agree support p q) : d3965 p = d3965 q := by
  simp only [d3965, h 182 (by decide), agree3964 p q h, agree3963 p q h]
theorem nonnegative3965 (p : Pattern) : 0 ≤ d3965 p :=
  nonnegative_ite (p 182) (nonnegative3964 p) (nonnegative3963 p)
def d3966 (p : Pattern) : Int := if p 163 then d3832 p else d3965 p
theorem agree3966 (p q : Pattern) (h : Agree support p q) : d3966 p = d3966 q := by
  simp only [d3966, h 163 (by decide), agree3832 p q h, agree3965 p q h]
theorem nonnegative3966 (p : Pattern) : 0 ≤ d3966 p :=
  nonnegative_ite (p 163) (nonnegative3832 p) (nonnegative3965 p)
def d3967 (p : Pattern) : Int := if p 162 then d3966 p else d3822 p
theorem agree3967 (p q : Pattern) (h : Agree support p q) : d3967 p = d3967 q := by
  simp only [d3967, h 162 (by decide), agree3966 p q h, agree3822 p q h]
theorem nonnegative3967 (p : Pattern) : 0 ≤ d3967 p :=
  nonnegative_ite (p 162) (nonnegative3966 p) (nonnegative3822 p)
def d3968 (p : Pattern) : Int := if p 163 then d3832 p else d3827 p
theorem agree3968 (p q : Pattern) (h : Agree support p q) : d3968 p = d3968 q := by
  simp only [d3968, h 163 (by decide), agree3832 p q h, agree3827 p q h]
theorem nonnegative3968 (p : Pattern) : 0 ≤ d3968 p :=
  nonnegative_ite (p 163) (nonnegative3832 p) (nonnegative3827 p)
def d3969 (p : Pattern) : Int := if p 162 then d3759 p else d3968 p
theorem agree3969 (p q : Pattern) (h : Agree support p q) : d3969 p = d3969 q := by
  simp only [d3969, h 162 (by decide), agree3759 p q h, agree3968 p q h]
theorem nonnegative3969 (p : Pattern) : 0 ≤ d3969 p :=
  nonnegative_ite (p 162) (nonnegative3759 p) (nonnegative3968 p)
def d3970 (p : Pattern) : Int := if p 161 then d3969 p else d3967 p
theorem agree3970 (p q : Pattern) (h : Agree support p q) : d3970 p = d3970 q := by
  simp only [d3970, h 161 (by decide), agree3969 p q h, agree3967 p q h]
theorem nonnegative3970 (p : Pattern) : 0 ≤ d3970 p :=
  nonnegative_ite (p 161) (nonnegative3969 p) (nonnegative3967 p)
def d3971 (p : Pattern) : Int := if p 182 then d3778 p else d3808 p
theorem agree3971 (p q : Pattern) (h : Agree support p q) : d3971 p = d3971 q := by
  simp only [d3971, h 182 (by decide), agree3778 p q h, agree3808 p q h]
theorem nonnegative3971 (p : Pattern) : 0 ≤ d3971 p :=
  nonnegative_ite (p 182) (nonnegative3778 p) (nonnegative3808 p)
def d3972 (p : Pattern) : Int := if p 163 then d3971 p else d3837 p
theorem agree3972 (p q : Pattern) (h : Agree support p q) : d3972 p = d3972 q := by
  simp only [d3972, h 163 (by decide), agree3971 p q h, agree3837 p q h]
theorem nonnegative3972 (p : Pattern) : 0 ≤ d3972 p :=
  nonnegative_ite (p 163) (nonnegative3971 p) (nonnegative3837 p)
def d3973 (p : Pattern) : Int := if p 162 then d3948 p else d3972 p
theorem agree3973 (p q : Pattern) (h : Agree support p q) : d3973 p = d3973 q := by
  simp only [d3973, h 162 (by decide), agree3948 p q h, agree3972 p q h]
theorem nonnegative3973 (p : Pattern) : 0 ≤ d3973 p :=
  nonnegative_ite (p 162) (nonnegative3948 p) (nonnegative3972 p)
def d3974 (p : Pattern) : Int := if p 182 then d12 p else d3838 p
theorem agree3974 (p q : Pattern) (h : Agree support p q) : d3974 p = d3974 q := by
  simp only [d3974, h 182 (by decide), agree12 p q h, agree3838 p q h]
theorem nonnegative3974 (p : Pattern) : 0 ≤ d3974 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative3838 p)
def d3975 (p : Pattern) : Int := if p 163 then d12 p else d3974 p
theorem agree3975 (p q : Pattern) (h : Agree support p q) : d3975 p = d3975 q := by
  simp only [d3975, h 163 (by decide), agree12 p q h, agree3974 p q h]
theorem nonnegative3975 (p : Pattern) : 0 ≤ d3975 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3974 p)
def d3976 (p : Pattern) : Int := if p 162 then d12 p else d3975 p
theorem agree3976 (p q : Pattern) (h : Agree support p q) : d3976 p = d3976 q := by
  simp only [d3976, h 162 (by decide), agree12 p q h, agree3975 p q h]
theorem nonnegative3976 (p : Pattern) : 0 ≤ d3976 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3975 p)
def d3977 (p : Pattern) : Int := if p 161 then d3976 p else d3973 p
theorem agree3977 (p q : Pattern) (h : Agree support p q) : d3977 p = d3977 q := by
  simp only [d3977, h 161 (by decide), agree3976 p q h, agree3973 p q h]
theorem nonnegative3977 (p : Pattern) : 0 ≤ d3977 p :=
  nonnegative_ite (p 161) (nonnegative3976 p) (nonnegative3973 p)
def d3978 (p : Pattern) : Int := if p 160 then d3977 p else d3970 p
theorem agree3978 (p q : Pattern) (h : Agree support p q) : d3978 p = d3978 q := by
  simp only [d3978, h 160 (by decide), agree3977 p q h, agree3970 p q h]
theorem nonnegative3978 (p : Pattern) : 0 ≤ d3978 p :=
  nonnegative_ite (p 160) (nonnegative3977 p) (nonnegative3970 p)
def d3979 (p : Pattern) : Int := if p 225 then d3767 p else d3769 p
theorem agree3979 (p q : Pattern) (h : Agree support p q) : d3979 p = d3979 q := by
  simp only [d3979, h 225 (by decide), agree3767 p q h, agree3769 p q h]
theorem nonnegative3979 (p : Pattern) : 0 ≤ d3979 p :=
  nonnegative_ite (p 225) (nonnegative3767 p) (nonnegative3769 p)
def d3980 (p : Pattern) : Int := if p 224 then d3979 p else d3768 p
theorem agree3980 (p q : Pattern) (h : Agree support p q) : d3980 p = d3980 q := by
  simp only [d3980, h 224 (by decide), agree3979 p q h, agree3768 p q h]
theorem nonnegative3980 (p : Pattern) : 0 ≤ d3980 p :=
  nonnegative_ite (p 224) (nonnegative3979 p) (nonnegative3768 p)
def d3981 (p : Pattern) : Int := if p 204 then d3980 p else d115 p
theorem agree3981 (p q : Pattern) (h : Agree support p q) : d3981 p = d3981 q := by
  simp only [d3981, h 204 (by decide), agree3980 p q h, agree115 p q h]
theorem nonnegative3981 (p : Pattern) : 0 ≤ d3981 p :=
  nonnegative_ite (p 204) (nonnegative3980 p) (nonnegative115 p)
def d3982 (p : Pattern) : Int := if p 204 then d12 p else d3795 p
theorem agree3982 (p q : Pattern) (h : Agree support p q) : d3982 p = d3982 q := by
  simp only [d3982, h 204 (by decide), agree12 p q h, agree3795 p q h]
theorem nonnegative3982 (p : Pattern) : 0 ≤ d3982 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3795 p)
def d3983 (p : Pattern) : Int := if p 182 then d3982 p else d3981 p
theorem agree3983 (p q : Pattern) (h : Agree support p q) : d3983 p = d3983 q := by
  simp only [d3983, h 182 (by decide), agree3982 p q h, agree3981 p q h]
theorem nonnegative3983 (p : Pattern) : 0 ≤ d3983 p :=
  nonnegative_ite (p 182) (nonnegative3982 p) (nonnegative3981 p)
def d3984 (p : Pattern) : Int := if p 163 then d3983 p else d3965 p
theorem agree3984 (p q : Pattern) (h : Agree support p q) : d3984 p = d3984 q := by
  simp only [d3984, h 163 (by decide), agree3983 p q h, agree3965 p q h]
theorem nonnegative3984 (p : Pattern) : 0 ≤ d3984 p :=
  nonnegative_ite (p 163) (nonnegative3983 p) (nonnegative3965 p)
def d3985 (p : Pattern) : Int := if p 225 then d3782 p else d3748 p
theorem agree3985 (p q : Pattern) (h : Agree support p q) : d3985 p = d3985 q := by
  simp only [d3985, h 225 (by decide), agree3782 p q h, agree3748 p q h]
theorem nonnegative3985 (p : Pattern) : 0 ≤ d3985 p :=
  nonnegative_ite (p 225) (nonnegative3782 p) (nonnegative3748 p)
def d3986 (p : Pattern) : Int := if p 224 then d3985 p else d3783 p
theorem agree3986 (p q : Pattern) (h : Agree support p q) : d3986 p = d3986 q := by
  simp only [d3986, h 224 (by decide), agree3985 p q h, agree3783 p q h]
theorem nonnegative3986 (p : Pattern) : 0 ≤ d3986 p :=
  nonnegative_ite (p 224) (nonnegative3985 p) (nonnegative3783 p)
def d3987 (p : Pattern) : Int := if p 204 then d3986 p else d106 p
theorem agree3987 (p q : Pattern) (h : Agree support p q) : d3987 p = d3987 q := by
  simp only [d3987, h 204 (by decide), agree3986 p q h, agree106 p q h]
theorem nonnegative3987 (p : Pattern) : 0 ≤ d3987 p :=
  nonnegative_ite (p 204) (nonnegative3986 p) (nonnegative106 p)
def d3988 (p : Pattern) : Int := if p 204 then d12 p else d3750 p
theorem agree3988 (p q : Pattern) (h : Agree support p q) : d3988 p = d3988 q := by
  simp only [d3988, h 204 (by decide), agree12 p q h, agree3750 p q h]
theorem nonnegative3988 (p : Pattern) : 0 ≤ d3988 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3750 p)
def d3989 (p : Pattern) : Int := if p 182 then d3988 p else d3987 p
theorem agree3989 (p q : Pattern) (h : Agree support p q) : d3989 p = d3989 q := by
  simp only [d3989, h 182 (by decide), agree3988 p q h, agree3987 p q h]
theorem nonnegative3989 (p : Pattern) : 0 ≤ d3989 p :=
  nonnegative_ite (p 182) (nonnegative3988 p) (nonnegative3987 p)
def d3990 (p : Pattern) : Int := if p 163 then d12 p else d3989 p
theorem agree3990 (p q : Pattern) (h : Agree support p q) : d3990 p = d3990 q := by
  simp only [d3990, h 163 (by decide), agree12 p q h, agree3989 p q h]
theorem nonnegative3990 (p : Pattern) : 0 ≤ d3990 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3989 p)
def d3991 (p : Pattern) : Int := if p 162 then d3990 p else d3984 p
theorem agree3991 (p q : Pattern) (h : Agree support p q) : d3991 p = d3991 q := by
  simp only [d3991, h 162 (by decide), agree3990 p q h, agree3984 p q h]
theorem nonnegative3991 (p : Pattern) : 0 ≤ d3991 p :=
  nonnegative_ite (p 162) (nonnegative3990 p) (nonnegative3984 p)
def d3992 (p : Pattern) : Int := if p 204 then d12 p else d3986 p
theorem agree3992 (p q : Pattern) (h : Agree support p q) : d3992 p = d3992 q := by
  simp only [d3992, h 204 (by decide), agree12 p q h, agree3986 p q h]
theorem nonnegative3992 (p : Pattern) : 0 ≤ d3992 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative3986 p)
def d3993 (p : Pattern) : Int := if p 182 then d3992 p else d3786 p
theorem agree3993 (p q : Pattern) (h : Agree support p q) : d3993 p = d3993 q := by
  simp only [d3993, h 182 (by decide), agree3992 p q h, agree3786 p q h]
theorem nonnegative3993 (p : Pattern) : 0 ≤ d3993 p :=
  nonnegative_ite (p 182) (nonnegative3992 p) (nonnegative3786 p)
def d3994 (p : Pattern) : Int := if p 163 then d12 p else d3993 p
theorem agree3994 (p q : Pattern) (h : Agree support p q) : d3994 p = d3994 q := by
  simp only [d3994, h 163 (by decide), agree12 p q h, agree3993 p q h]
theorem nonnegative3994 (p : Pattern) : 0 ≤ d3994 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative3993 p)
def d3995 (p : Pattern) : Int := if p 162 then d12 p else d3994 p
theorem agree3995 (p q : Pattern) (h : Agree support p q) : d3995 p = d3995 q := by
  simp only [d3995, h 162 (by decide), agree12 p q h, agree3994 p q h]
theorem nonnegative3995 (p : Pattern) : 0 ≤ d3995 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3994 p)
def d3996 (p : Pattern) : Int := if p 161 then d3995 p else d3991 p
theorem agree3996 (p q : Pattern) (h : Agree support p q) : d3996 p = d3996 q := by
  simp only [d3996, h 161 (by decide), agree3995 p q h, agree3991 p q h]
theorem nonnegative3996 (p : Pattern) : 0 ≤ d3996 p :=
  nonnegative_ite (p 161) (nonnegative3995 p) (nonnegative3991 p)
def d3997 (p : Pattern) : Int := if p 182 then d3778 p else d3786 p
theorem agree3997 (p q : Pattern) (h : Agree support p q) : d3997 p = d3997 q := by
  simp only [d3997, h 182 (by decide), agree3778 p q h, agree3786 p q h]
theorem nonnegative3997 (p : Pattern) : 0 ≤ d3997 p :=
  nonnegative_ite (p 182) (nonnegative3778 p) (nonnegative3786 p)
def d3998 (p : Pattern) : Int := if p 163 then d3787 p else d3997 p
theorem agree3998 (p q : Pattern) (h : Agree support p q) : d3998 p = d3998 q := by
  simp only [d3998, h 163 (by decide), agree3787 p q h, agree3997 p q h]
theorem nonnegative3998 (p : Pattern) : 0 ≤ d3998 p :=
  nonnegative_ite (p 163) (nonnegative3787 p) (nonnegative3997 p)
def d3999 (p : Pattern) : Int := if p 162 then d3975 p else d3998 p
theorem agree3999 (p q : Pattern) (h : Agree support p q) : d3999 p = d3999 q := by
  simp only [d3999, h 162 (by decide), agree3975 p q h, agree3998 p q h]
theorem nonnegative3999 (p : Pattern) : 0 ≤ d3999 p :=
  nonnegative_ite (p 162) (nonnegative3975 p) (nonnegative3998 p)
def d4000 (p : Pattern) : Int := if p 162 then d12 p else d3612 p
theorem agree4000 (p q : Pattern) (h : Agree support p q) : d4000 p = d4000 q := by
  simp only [d4000, h 162 (by decide), agree12 p q h, agree3612 p q h]
theorem nonnegative4000 (p : Pattern) : 0 ≤ d4000 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3612 p)
def d4001 (p : Pattern) : Int := if p 161 then d4000 p else d3999 p
theorem agree4001 (p q : Pattern) (h : Agree support p q) : d4001 p = d4001 q := by
  simp only [d4001, h 161 (by decide), agree4000 p q h, agree3999 p q h]
theorem nonnegative4001 (p : Pattern) : 0 ≤ d4001 p :=
  nonnegative_ite (p 161) (nonnegative4000 p) (nonnegative3999 p)
def d4002 (p : Pattern) : Int := if p 160 then d4001 p else d3996 p
theorem agree4002 (p q : Pattern) (h : Agree support p q) : d4002 p = d4002 q := by
  simp only [d4002, h 160 (by decide), agree4001 p q h, agree3996 p q h]
theorem nonnegative4002 (p : Pattern) : 0 ≤ d4002 p :=
  nonnegative_ite (p 160) (nonnegative4001 p) (nonnegative3996 p)
def d4003 (p : Pattern) : Int := if p 141 then d4002 p else d3978 p
theorem agree4003 (p q : Pattern) (h : Agree support p q) : d4003 p = d4003 q := by
  simp only [d4003, h 141 (by decide), agree4002 p q h, agree3978 p q h]
theorem nonnegative4003 (p : Pattern) : 0 ≤ d4003 p :=
  nonnegative_ite (p 141) (nonnegative4002 p) (nonnegative3978 p)
def d4004 (p : Pattern) : Int := if p 163 then d3830 p else d3827 p
theorem agree4004 (p q : Pattern) (h : Agree support p q) : d4004 p = d4004 q := by
  simp only [d4004, h 163 (by decide), agree3830 p q h, agree3827 p q h]
theorem nonnegative4004 (p : Pattern) : 0 ≤ d4004 p :=
  nonnegative_ite (p 163) (nonnegative3830 p) (nonnegative3827 p)
def d4005 (p : Pattern) : Int := if p 163 then d3639 p else d3837 p
theorem agree4005 (p q : Pattern) (h : Agree support p q) : d4005 p = d4005 q := by
  simp only [d4005, h 163 (by decide), agree3639 p q h, agree3837 p q h]
theorem nonnegative4005 (p : Pattern) : 0 ≤ d4005 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3837 p)
def d4006 (p : Pattern) : Int := if p 162 then d4005 p else d4004 p
theorem agree4006 (p q : Pattern) (h : Agree support p q) : d4006 p = d4006 q := by
  simp only [d4006, h 162 (by decide), agree4005 p q h, agree4004 p q h]
theorem nonnegative4006 (p : Pattern) : 0 ≤ d4006 p :=
  nonnegative_ite (p 162) (nonnegative4005 p) (nonnegative4004 p)
def d4007 (p : Pattern) : Int := if p 161 then d3848 p else d4006 p
theorem agree4007 (p q : Pattern) (h : Agree support p q) : d4007 p = d4007 q := by
  simp only [d4007, h 161 (by decide), agree3848 p q h, agree4006 p q h]
theorem nonnegative4007 (p : Pattern) : 0 ≤ d4007 p :=
  nonnegative_ite (p 161) (nonnegative3848 p) (nonnegative4006 p)
def d4008 (p : Pattern) : Int := if p 160 then d3852 p else d4007 p
theorem agree4008 (p q : Pattern) (h : Agree support p q) : d4008 p = d4008 q := by
  simp only [d4008, h 160 (by decide), agree3852 p q h, agree4007 p q h]
theorem nonnegative4008 (p : Pattern) : 0 ≤ d4008 p :=
  nonnegative_ite (p 160) (nonnegative3852 p) (nonnegative4007 p)
def d4009 (p : Pattern) : Int := if p 225 then d326 p else d3769 p
theorem agree4009 (p q : Pattern) (h : Agree support p q) : d4009 p = d4009 q := by
  simp only [d4009, h 225 (by decide), agree326 p q h, agree3769 p q h]
theorem nonnegative4009 (p : Pattern) : 0 ≤ d4009 p :=
  nonnegative_ite (p 225) (nonnegative326 p) (nonnegative3769 p)
def d4010 (p : Pattern) : Int := if p 224 then d4009 p else d3768 p
theorem agree4010 (p q : Pattern) (h : Agree support p q) : d4010 p = d4010 q := by
  simp only [d4010, h 224 (by decide), agree4009 p q h, agree3768 p q h]
theorem nonnegative4010 (p : Pattern) : 0 ≤ d4010 p :=
  nonnegative_ite (p 224) (nonnegative4009 p) (nonnegative3768 p)
def d4011 (p : Pattern) : Int := if p 204 then d12 p else d4010 p
theorem agree4011 (p q : Pattern) (h : Agree support p q) : d4011 p = d4011 q := by
  simp only [d4011, h 204 (by decide), agree12 p q h, agree4010 p q h]
theorem nonnegative4011 (p : Pattern) : 0 ≤ d4011 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative4010 p)
def d4012 (p : Pattern) : Int := if p 182 then d4011 p else d3808 p
theorem agree4012 (p q : Pattern) (h : Agree support p q) : d4012 p = d4012 q := by
  simp only [d4012, h 182 (by decide), agree4011 p q h, agree3808 p q h]
theorem nonnegative4012 (p : Pattern) : 0 ≤ d4012 p :=
  nonnegative_ite (p 182) (nonnegative4011 p) (nonnegative3808 p)
def d4013 (p : Pattern) : Int := if p 163 then d3837 p else d4012 p
theorem agree4013 (p q : Pattern) (h : Agree support p q) : d4013 p = d4013 q := by
  simp only [d4013, h 163 (by decide), agree3837 p q h, agree4012 p q h]
theorem nonnegative4013 (p : Pattern) : 0 ≤ d4013 p :=
  nonnegative_ite (p 163) (nonnegative3837 p) (nonnegative4012 p)
def d4014 (p : Pattern) : Int := if p 162 then d3954 p else d4013 p
theorem agree4014 (p q : Pattern) (h : Agree support p q) : d4014 p = d4014 q := by
  simp only [d4014, h 162 (by decide), agree3954 p q h, agree4013 p q h]
theorem nonnegative4014 (p : Pattern) : 0 ≤ d4014 p :=
  nonnegative_ite (p 162) (nonnegative3954 p) (nonnegative4013 p)
def d4015 (p : Pattern) : Int := if p 161 then d3851 p else d4014 p
theorem agree4015 (p q : Pattern) (h : Agree support p q) : d4015 p = d4015 q := by
  simp only [d4015, h 161 (by decide), agree3851 p q h, agree4014 p q h]
theorem nonnegative4015 (p : Pattern) : 0 ≤ d4015 p :=
  nonnegative_ite (p 161) (nonnegative3851 p) (nonnegative4014 p)
def d4016 (p : Pattern) : Int := if p 162 then d12 p else d3675 p
theorem agree4016 (p q : Pattern) (h : Agree support p q) : d4016 p = d4016 q := by
  simp only [d4016, h 162 (by decide), agree12 p q h, agree3675 p q h]
theorem nonnegative4016 (p : Pattern) : 0 ≤ d4016 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative3675 p)
def d4017 (p : Pattern) : Int := if p 161 then d12 p else d4016 p
theorem agree4017 (p q : Pattern) (h : Agree support p q) : d4017 p = d4017 q := by
  simp only [d4017, h 161 (by decide), agree12 p q h, agree4016 p q h]
theorem nonnegative4017 (p : Pattern) : 0 ≤ d4017 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4016 p)
def d4018 (p : Pattern) : Int := if p 160 then d4017 p else d4015 p
theorem agree4018 (p q : Pattern) (h : Agree support p q) : d4018 p = d4018 q := by
  simp only [d4018, h 160 (by decide), agree4017 p q h, agree4015 p q h]
theorem nonnegative4018 (p : Pattern) : 0 ≤ d4018 p :=
  nonnegative_ite (p 160) (nonnegative4017 p) (nonnegative4015 p)
def d4019 (p : Pattern) : Int := if p 141 then d4018 p else d4008 p
theorem agree4019 (p q : Pattern) (h : Agree support p q) : d4019 p = d4019 q := by
  simp only [d4019, h 141 (by decide), agree4018 p q h, agree4008 p q h]
theorem nonnegative4019 (p : Pattern) : 0 ≤ d4019 p :=
  nonnegative_ite (p 141) (nonnegative4018 p) (nonnegative4008 p)
def d4020 (p : Pattern) : Int := if p 138 then d4019 p else d4003 p
theorem agree4020 (p q : Pattern) (h : Agree support p q) : d4020 p = d4020 q := by
  simp only [d4020, h 138 (by decide), agree4019 p q h, agree4003 p q h]
theorem nonnegative4020 (p : Pattern) : 0 ≤ d4020 p :=
  nonnegative_ite (p 138) (nonnegative4019 p) (nonnegative4003 p)
def d4021 (p : Pattern) : Int := if p 163 then d3674 p else d3837 p
theorem agree4021 (p q : Pattern) (h : Agree support p q) : d4021 p = d4021 q := by
  simp only [d4021, h 163 (by decide), agree3674 p q h, agree3837 p q h]
theorem nonnegative4021 (p : Pattern) : 0 ≤ d4021 p :=
  nonnegative_ite (p 163) (nonnegative3674 p) (nonnegative3837 p)
def d4022 (p : Pattern) : Int := if p 162 then d4021 p else d4004 p
theorem agree4022 (p q : Pattern) (h : Agree support p q) : d4022 p = d4022 q := by
  simp only [d4022, h 162 (by decide), agree4021 p q h, agree4004 p q h]
theorem nonnegative4022 (p : Pattern) : 0 ≤ d4022 p :=
  nonnegative_ite (p 162) (nonnegative4021 p) (nonnegative4004 p)
def d4023 (p : Pattern) : Int := if p 163 then d3674 p else d3832 p
theorem agree4023 (p q : Pattern) (h : Agree support p q) : d4023 p = d4023 q := by
  simp only [d4023, h 163 (by decide), agree3674 p q h, agree3832 p q h]
theorem nonnegative4023 (p : Pattern) : 0 ≤ d4023 p :=
  nonnegative_ite (p 163) (nonnegative3674 p) (nonnegative3832 p)
def d4024 (p : Pattern) : Int := if p 162 then d12 p else d4023 p
theorem agree4024 (p q : Pattern) (h : Agree support p q) : d4024 p = d4024 q := by
  simp only [d4024, h 162 (by decide), agree12 p q h, agree4023 p q h]
theorem nonnegative4024 (p : Pattern) : 0 ≤ d4024 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4023 p)
def d4025 (p : Pattern) : Int := if p 161 then d4024 p else d4022 p
theorem agree4025 (p q : Pattern) (h : Agree support p q) : d4025 p = d4025 q := by
  simp only [d4025, h 161 (by decide), agree4024 p q h, agree4022 p q h]
theorem nonnegative4025 (p : Pattern) : 0 ≤ d4025 p :=
  nonnegative_ite (p 161) (nonnegative4024 p) (nonnegative4022 p)
def d4026 (p : Pattern) : Int := if p 163 then d3639 p else d3839 p
theorem agree4026 (p q : Pattern) (h : Agree support p q) : d4026 p = d4026 q := by
  simp only [d4026, h 163 (by decide), agree3639 p q h, agree3839 p q h]
theorem nonnegative4026 (p : Pattern) : 0 ≤ d4026 p :=
  nonnegative_ite (p 163) (nonnegative3639 p) (nonnegative3839 p)
def d4027 (p : Pattern) : Int := if p 162 then d12 p else d4026 p
theorem agree4027 (p q : Pattern) (h : Agree support p q) : d4027 p = d4027 q := by
  simp only [d4027, h 162 (by decide), agree12 p q h, agree4026 p q h]
theorem nonnegative4027 (p : Pattern) : 0 ≤ d4027 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative4026 p)
def d4028 (p : Pattern) : Int := if p 161 then d12 p else d4027 p
theorem agree4028 (p q : Pattern) (h : Agree support p q) : d4028 p = d4028 q := by
  simp only [d4028, h 161 (by decide), agree12 p q h, agree4027 p q h]
theorem nonnegative4028 (p : Pattern) : 0 ≤ d4028 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative4027 p)
def d4029 (p : Pattern) : Int := if p 160 then d4028 p else d4025 p
theorem agree4029 (p q : Pattern) (h : Agree support p q) : d4029 p = d4029 q := by
  simp only [d4029, h 160 (by decide), agree4028 p q h, agree4025 p q h]
theorem nonnegative4029 (p : Pattern) : 0 ≤ d4029 p :=
  nonnegative_ite (p 160) (nonnegative4028 p) (nonnegative4025 p)
def d4030 (p : Pattern) : Int := if p 141 then d4018 p else d4029 p
theorem agree4030 (p q : Pattern) (h : Agree support p q) : d4030 p = d4030 q := by
  simp only [d4030, h 141 (by decide), agree4018 p q h, agree4029 p q h]
theorem nonnegative4030 (p : Pattern) : 0 ≤ d4030 p :=
  nonnegative_ite (p 141) (nonnegative4018 p) (nonnegative4029 p)
def d4031 (p : Pattern) : Int := if p 138 then d12 p else d4030 p
theorem agree4031 (p q : Pattern) (h : Agree support p q) : d4031 p = d4031 q := by
  simp only [d4031, h 138 (by decide), agree12 p q h, agree4030 p q h]
theorem nonnegative4031 (p : Pattern) : 0 ≤ d4031 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative4030 p)
def d4032 (p : Pattern) : Int := if p 116 then d4031 p else d4020 p
theorem agree4032 (p q : Pattern) (h : Agree support p q) : d4032 p = d4032 q := by
  simp only [d4032, h 116 (by decide), agree4031 p q h, agree4020 p q h]
theorem nonnegative4032 (p : Pattern) : 0 ≤ d4032 p :=
  nonnegative_ite (p 116) (nonnegative4031 p) (nonnegative4020 p)
def d4033 (p : Pattern) : Int := if p 115 then d4032 p else d3962 p
theorem agree4033 (p q : Pattern) (h : Agree support p q) : d4033 p = d4033 q := by
  simp only [d4033, h 115 (by decide), agree4032 p q h, agree3962 p q h]
theorem nonnegative4033 (p : Pattern) : 0 ≤ d4033 p :=
  nonnegative_ite (p 115) (nonnegative4032 p) (nonnegative3962 p)
def d4034 (p : Pattern) : Int := if p 71 then d4033 p else d3718 p
theorem agree4034 (p q : Pattern) (h : Agree support p q) : d4034 p = d4034 q := by
  simp only [d4034, h 71 (by decide), agree4033 p q h, agree3718 p q h]
theorem nonnegative4034 (p : Pattern) : 0 ≤ d4034 p :=
  nonnegative_ite (p 71) (nonnegative4033 p) (nonnegative3718 p)
def d4035 (p : Pattern) : Int := if p 49 then d4034 p else d3943 p
theorem agree4035 (p q : Pattern) (h : Agree support p q) : d4035 p = d4035 q := by
  simp only [d4035, h 49 (by decide), agree4034 p q h, agree3943 p q h]
theorem nonnegative4035 (p : Pattern) : 0 ≤ d4035 p :=
  nonnegative_ite (p 49) (nonnegative4034 p) (nonnegative3943 p)
def d4036 (p : Pattern) : Int := if p 48 then d4035 p else d3871 p
theorem agree4036 (p q : Pattern) (h : Agree support p q) : d4036 p = d4036 q := by
  simp only [d4036, h 48 (by decide), agree4035 p q h, agree3871 p q h]
theorem nonnegative4036 (p : Pattern) : 0 ≤ d4036 p :=
  nonnegative_ite (p 48) (nonnegative4035 p) (nonnegative3871 p)
def d4037 (p : Pattern) : Int := if p 48 then d1 p else d0 p
theorem agree4037 (p q : Pattern) (h : Agree support p q) : d4037 p = d4037 q := by
  simp only [d4037, h 48 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4037 (p : Pattern) : 0 ≤ d4037 p :=
  nonnegative_ite (p 48) (nonnegative1 p) (nonnegative0 p)
def d4038 (p : Pattern) : Int := if p 48 then d0 p else d1 p
theorem agree4038 (p q : Pattern) (h : Agree support p q) : d4038 p = d4038 q := by
  simp only [d4038, h 48 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4038 (p : Pattern) : 0 ≤ d4038 p :=
  nonnegative_ite (p 48) (nonnegative0 p) (nonnegative1 p)
def d4039 (p : Pattern) : Int := if p 49 then d1 p else d0 p
theorem agree4039 (p q : Pattern) (h : Agree support p q) : d4039 p = d4039 q := by
  simp only [d4039, h 49 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4039 (p : Pattern) : 0 ≤ d4039 p :=
  nonnegative_ite (p 49) (nonnegative1 p) (nonnegative0 p)
def d4040 (p : Pattern) : Int := if p 49 then d0 p else d1 p
theorem agree4040 (p q : Pattern) (h : Agree support p q) : d4040 p = d4040 q := by
  simp only [d4040, h 49 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4040 (p : Pattern) : 0 ≤ d4040 p :=
  nonnegative_ite (p 49) (nonnegative0 p) (nonnegative1 p)
def d4041 (p : Pattern) : Int := if p 71 then d1 p else d0 p
theorem agree4041 (p q : Pattern) (h : Agree support p q) : d4041 p = d4041 q := by
  simp only [d4041, h 71 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4041 (p : Pattern) : 0 ≤ d4041 p :=
  nonnegative_ite (p 71) (nonnegative1 p) (nonnegative0 p)
def d4042 (p : Pattern) : Int := if p 71 then d0 p else d1 p
theorem agree4042 (p q : Pattern) (h : Agree support p q) : d4042 p = d4042 q := by
  simp only [d4042, h 71 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4042 (p : Pattern) : 0 ≤ d4042 p :=
  nonnegative_ite (p 71) (nonnegative0 p) (nonnegative1 p)
def d4043 (p : Pattern) : Int := if p 49 then d4042 p else d0 p
theorem agree4043 (p q : Pattern) (h : Agree support p q) : d4043 p = d4043 q := by
  simp only [d4043, h 49 (by decide), agree4042 p q h, agree0 p q h]
theorem nonnegative4043 (p : Pattern) : 0 ≤ d4043 p :=
  nonnegative_ite (p 49) (nonnegative4042 p) (nonnegative0 p)
def d4044 (p : Pattern) : Int := if p 48 then d0 p else d4040 p
theorem agree4044 (p q : Pattern) (h : Agree support p q) : d4044 p = d4044 q := by
  simp only [d4044, h 48 (by decide), agree0 p q h, agree4040 p q h]
theorem nonnegative4044 (p : Pattern) : 0 ≤ d4044 p :=
  nonnegative_ite (p 48) (nonnegative0 p) (nonnegative4040 p)
def d4045 (p : Pattern) : Int := if p 48 then d4040 p else d0 p
theorem agree4045 (p q : Pattern) (h : Agree support p q) : d4045 p = d4045 q := by
  simp only [d4045, h 48 (by decide), agree4040 p q h, agree0 p q h]
theorem nonnegative4045 (p : Pattern) : 0 ≤ d4045 p :=
  nonnegative_ite (p 48) (nonnegative4040 p) (nonnegative0 p)
def d4046 (p : Pattern) : Int := if p 48 then d0 p else d4039 p
theorem agree4046 (p q : Pattern) (h : Agree support p q) : d4046 p = d4046 q := by
  simp only [d4046, h 48 (by decide), agree0 p q h, agree4039 p q h]
theorem nonnegative4046 (p : Pattern) : 0 ≤ d4046 p :=
  nonnegative_ite (p 48) (nonnegative0 p) (nonnegative4039 p)
def d4047 (p : Pattern) : Int := if p 48 then d0 p else d4042 p
theorem agree4047 (p q : Pattern) (h : Agree support p q) : d4047 p = d4047 q := by
  simp only [d4047, h 48 (by decide), agree0 p q h, agree4042 p q h]
theorem nonnegative4047 (p : Pattern) : 0 ≤ d4047 p :=
  nonnegative_ite (p 48) (nonnegative0 p) (nonnegative4042 p)
def d4048 (p : Pattern) : Int := if p 49 then d0 p else d4042 p
theorem agree4048 (p q : Pattern) (h : Agree support p q) : d4048 p = d4048 q := by
  simp only [d4048, h 49 (by decide), agree0 p q h, agree4042 p q h]
theorem nonnegative4048 (p : Pattern) : 0 ≤ d4048 p :=
  nonnegative_ite (p 49) (nonnegative0 p) (nonnegative4042 p)
def d4049 (p : Pattern) : Int := if p 49 then d0 p else d4041 p
theorem agree4049 (p q : Pattern) (h : Agree support p q) : d4049 p = d4049 q := by
  simp only [d4049, h 49 (by decide), agree0 p q h, agree4041 p q h]
theorem nonnegative4049 (p : Pattern) : 0 ≤ d4049 p :=
  nonnegative_ite (p 49) (nonnegative0 p) (nonnegative4041 p)
def d4050 (p : Pattern) : Int := if p 48 then d4041 p else d0 p
theorem agree4050 (p q : Pattern) (h : Agree support p q) : d4050 p = d4050 q := by
  simp only [d4050, h 48 (by decide), agree4041 p q h, agree0 p q h]
theorem nonnegative4050 (p : Pattern) : 0 ≤ d4050 p :=
  nonnegative_ite (p 48) (nonnegative4041 p) (nonnegative0 p)
def d4051 (p : Pattern) : Int := if p 48 then d4042 p else d1 p
theorem agree4051 (p q : Pattern) (h : Agree support p q) : d4051 p = d4051 q := by
  simp only [d4051, h 48 (by decide), agree4042 p q h, agree1 p q h]
theorem nonnegative4051 (p : Pattern) : 0 ≤ d4051 p :=
  nonnegative_ite (p 48) (nonnegative4042 p) (nonnegative1 p)
def d4052 (p : Pattern) : Int := if p 48 then d4048 p else d4040 p
theorem agree4052 (p q : Pattern) (h : Agree support p q) : d4052 p = d4052 q := by
  simp only [d4052, h 48 (by decide), agree4048 p q h, agree4040 p q h]
theorem nonnegative4052 (p : Pattern) : 0 ≤ d4052 p :=
  nonnegative_ite (p 48) (nonnegative4048 p) (nonnegative4040 p)
def d4053 (p : Pattern) : Int := if p 48 then d310 p else d168 p
theorem agree4053 (p q : Pattern) (h : Agree support p q) : d4053 p = d4053 q := by
  simp only [d4053, h 48 (by decide), agree310 p q h, agree168 p q h]
theorem nonnegative4053 (p : Pattern) : 0 ≤ d4053 p :=
  nonnegative_ite (p 48) (nonnegative310 p) (nonnegative168 p)
def d4054 (p : Pattern) : Int := if p 49 then d167 p else d101 p
theorem agree4054 (p q : Pattern) (h : Agree support p q) : d4054 p = d4054 q := by
  simp only [d4054, h 49 (by decide), agree167 p q h, agree101 p q h]
theorem nonnegative4054 (p : Pattern) : 0 ≤ d4054 p :=
  nonnegative_ite (p 49) (nonnegative167 p) (nonnegative101 p)
def d4055 (p : Pattern) : Int := if p 49 then d264 p else d209 p
theorem agree4055 (p q : Pattern) (h : Agree support p q) : d4055 p = d4055 q := by
  simp only [d4055, h 49 (by decide), agree264 p q h, agree209 p q h]
theorem nonnegative4055 (p : Pattern) : 0 ≤ d4055 p :=
  nonnegative_ite (p 49) (nonnegative264 p) (nonnegative209 p)
def d4056 (p : Pattern) : Int := if p 48 then d4055 p else d4054 p
theorem agree4056 (p q : Pattern) (h : Agree support p q) : d4056 p = d4056 q := by
  simp only [d4056, h 48 (by decide), agree4055 p q h, agree4054 p q h]
theorem nonnegative4056 (p : Pattern) : 0 ≤ d4056 p :=
  nonnegative_ite (p 48) (nonnegative4055 p) (nonnegative4054 p)
def d4057 (p : Pattern) : Int := if p 115 then d1 p else d0 p
theorem agree4057 (p q : Pattern) (h : Agree support p q) : d4057 p = d4057 q := by
  simp only [d4057, h 115 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4057 (p : Pattern) : 0 ≤ d4057 p :=
  nonnegative_ite (p 115) (nonnegative1 p) (nonnegative0 p)
def d4058 (p : Pattern) : Int := if p 115 then d0 p else d1 p
theorem agree4058 (p q : Pattern) (h : Agree support p q) : d4058 p = d4058 q := by
  simp only [d4058, h 115 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4058 (p : Pattern) : 0 ≤ d4058 p :=
  nonnegative_ite (p 115) (nonnegative0 p) (nonnegative1 p)
def d4059 (p : Pattern) : Int := if p 71 then d0 p else d4058 p
theorem agree4059 (p q : Pattern) (h : Agree support p q) : d4059 p = d4059 q := by
  simp only [d4059, h 71 (by decide), agree0 p q h, agree4058 p q h]
theorem nonnegative4059 (p : Pattern) : 0 ≤ d4059 p :=
  nonnegative_ite (p 71) (nonnegative0 p) (nonnegative4058 p)
def d4060 (p : Pattern) : Int := if p 71 then d166 p else d100 p
theorem agree4060 (p q : Pattern) (h : Agree support p q) : d4060 p = d4060 q := by
  simp only [d4060, h 71 (by decide), agree166 p q h, agree100 p q h]
theorem nonnegative4060 (p : Pattern) : 0 ≤ d4060 p :=
  nonnegative_ite (p 71) (nonnegative166 p) (nonnegative100 p)
def d4061 (p : Pattern) : Int := if p 49 then d4060 p else d100 p
theorem agree4061 (p q : Pattern) (h : Agree support p q) : d4061 p = d4061 q := by
  simp only [d4061, h 49 (by decide), agree4060 p q h, agree100 p q h]
theorem nonnegative4061 (p : Pattern) : 0 ≤ d4061 p :=
  nonnegative_ite (p 49) (nonnegative4060 p) (nonnegative100 p)
def d4062 (p : Pattern) : Int := if p 71 then d308 p else d100 p
theorem agree4062 (p q : Pattern) (h : Agree support p q) : d4062 p = d4062 q := by
  simp only [d4062, h 71 (by decide), agree308 p q h, agree100 p q h]
theorem nonnegative4062 (p : Pattern) : 0 ≤ d4062 p :=
  nonnegative_ite (p 71) (nonnegative308 p) (nonnegative100 p)
def d4063 (p : Pattern) : Int := if p 49 then d4062 p else d100 p
theorem agree4063 (p q : Pattern) (h : Agree support p q) : d4063 p = d4063 q := by
  simp only [d4063, h 49 (by decide), agree4062 p q h, agree100 p q h]
theorem nonnegative4063 (p : Pattern) : 0 ≤ d4063 p :=
  nonnegative_ite (p 49) (nonnegative4062 p) (nonnegative100 p)
def d4064 (p : Pattern) : Int := if p 48 then d4063 p else d4061 p
theorem agree4064 (p q : Pattern) (h : Agree support p q) : d4064 p = d4064 q := by
  simp only [d4064, h 48 (by decide), agree4063 p q h, agree4061 p q h]
theorem nonnegative4064 (p : Pattern) : 0 ≤ d4064 p :=
  nonnegative_ite (p 48) (nonnegative4063 p) (nonnegative4061 p)
def d4065 (p : Pattern) : Int := if p 116 then d1 p else d0 p
theorem agree4065 (p q : Pattern) (h : Agree support p q) : d4065 p = d4065 q := by
  simp only [d4065, h 116 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4065 (p : Pattern) : 0 ≤ d4065 p :=
  nonnegative_ite (p 116) (nonnegative1 p) (nonnegative0 p)
def d4066 (p : Pattern) : Int := if p 116 then d0 p else d1 p
theorem agree4066 (p q : Pattern) (h : Agree support p q) : d4066 p = d4066 q := by
  simp only [d4066, h 116 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4066 (p : Pattern) : 0 ≤ d4066 p :=
  nonnegative_ite (p 116) (nonnegative0 p) (nonnegative1 p)
def d4067 (p : Pattern) : Int := if p 138 then d1 p else d0 p
theorem agree4067 (p q : Pattern) (h : Agree support p q) : d4067 p = d4067 q := by
  simp only [d4067, h 138 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4067 (p : Pattern) : 0 ≤ d4067 p :=
  nonnegative_ite (p 138) (nonnegative1 p) (nonnegative0 p)
def d4068 (p : Pattern) : Int := if p 138 then d0 p else d1 p
theorem agree4068 (p q : Pattern) (h : Agree support p q) : d4068 p = d4068 q := by
  simp only [d4068, h 138 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4068 (p : Pattern) : 0 ≤ d4068 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative1 p)
def d4069 (p : Pattern) : Int := if p 116 then d4068 p else d0 p
theorem agree4069 (p q : Pattern) (h : Agree support p q) : d4069 p = d4069 q := by
  simp only [d4069, h 116 (by decide), agree4068 p q h, agree0 p q h]
theorem nonnegative4069 (p : Pattern) : 0 ≤ d4069 p :=
  nonnegative_ite (p 116) (nonnegative4068 p) (nonnegative0 p)
def d4070 (p : Pattern) : Int := if p 71 then d157 p else d87 p
theorem agree4070 (p q : Pattern) (h : Agree support p q) : d4070 p = d4070 q := by
  simp only [d4070, h 71 (by decide), agree157 p q h, agree87 p q h]
theorem nonnegative4070 (p : Pattern) : 0 ≤ d4070 p :=
  nonnegative_ite (p 71) (nonnegative157 p) (nonnegative87 p)
def d4071 (p : Pattern) : Int := if p 49 then d4070 p else d87 p
theorem agree4071 (p q : Pattern) (h : Agree support p q) : d4071 p = d4071 q := by
  simp only [d4071, h 49 (by decide), agree4070 p q h, agree87 p q h]
theorem nonnegative4071 (p : Pattern) : 0 ≤ d4071 p :=
  nonnegative_ite (p 49) (nonnegative4070 p) (nonnegative87 p)
def d4072 (p : Pattern) : Int := if p 115 then d305 p else d222 p
theorem agree4072 (p q : Pattern) (h : Agree support p q) : d4072 p = d4072 q := by
  simp only [d4072, h 115 (by decide), agree305 p q h, agree222 p q h]
theorem nonnegative4072 (p : Pattern) : 0 ≤ d4072 p :=
  nonnegative_ite (p 115) (nonnegative305 p) (nonnegative222 p)
def d4073 (p : Pattern) : Int := if p 71 then d4072 p else d87 p
theorem agree4073 (p q : Pattern) (h : Agree support p q) : d4073 p = d4073 q := by
  simp only [d4073, h 71 (by decide), agree4072 p q h, agree87 p q h]
theorem nonnegative4073 (p : Pattern) : 0 ≤ d4073 p :=
  nonnegative_ite (p 71) (nonnegative4072 p) (nonnegative87 p)
def d4074 (p : Pattern) : Int := if p 49 then d4073 p else d87 p
theorem agree4074 (p q : Pattern) (h : Agree support p q) : d4074 p = d4074 q := by
  simp only [d4074, h 49 (by decide), agree4073 p q h, agree87 p q h]
theorem nonnegative4074 (p : Pattern) : 0 ≤ d4074 p :=
  nonnegative_ite (p 49) (nonnegative4073 p) (nonnegative87 p)
def d4075 (p : Pattern) : Int := if p 48 then d4074 p else d4071 p
theorem agree4075 (p q : Pattern) (h : Agree support p q) : d4075 p = d4075 q := by
  simp only [d4075, h 48 (by decide), agree4074 p q h, agree4071 p q h]
theorem nonnegative4075 (p : Pattern) : 0 ≤ d4075 p :=
  nonnegative_ite (p 48) (nonnegative4074 p) (nonnegative4071 p)
def d4076 (p : Pattern) : Int := if p 141 then d1 p else d0 p
theorem agree4076 (p q : Pattern) (h : Agree support p q) : d4076 p = d4076 q := by
  simp only [d4076, h 141 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative4076 (p : Pattern) : 0 ≤ d4076 p :=
  nonnegative_ite (p 141) (nonnegative1 p) (nonnegative0 p)
def d4077 (p : Pattern) : Int := if p 141 then d0 p else d1 p
theorem agree4077 (p q : Pattern) (h : Agree support p q) : d4077 p = d4077 q := by
  simp only [d4077, h 141 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative4077 (p : Pattern) : 0 ≤ d4077 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative1 p)
def d4078 (p : Pattern) : Int := if p 138 then d86 p else d76 p
theorem agree4078 (p q : Pattern) (h : Agree support p q) : d4078 p = d4078 q := by
  simp only [d4078, h 138 (by decide), agree86 p q h, agree76 p q h]
theorem nonnegative4078 (p : Pattern) : 0 ≤ d4078 p :=
  nonnegative_ite (p 138) (nonnegative86 p) (nonnegative76 p)
def d4079 (p : Pattern) : Int := if p 138 then d95 p else d86 p
theorem agree4079 (p q : Pattern) (h : Agree support p q) : d4079 p = d4079 q := by
  simp only [d4079, h 138 (by decide), agree95 p q h, agree86 p q h]
theorem nonnegative4079 (p : Pattern) : 0 ≤ d4079 p :=
  nonnegative_ite (p 138) (nonnegative95 p) (nonnegative86 p)
end NetHack.Sokoban22Refined85
