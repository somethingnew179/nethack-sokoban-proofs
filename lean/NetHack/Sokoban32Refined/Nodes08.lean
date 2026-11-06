/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d960 (p : Pattern) : Int := if p 112 then d959 p else d955 p
theorem agree960 (p q : Pattern) (h : Agree support p q) : d960 p = d960 q := by
  simp only [d960, h 112 (by decide), agree959 p q h, agree955 p q h]
theorem nonnegative960 (p : Pattern) : 0 ≤ d960 p :=
  nonnegative_ite (p 112) (nonnegative959 p) (nonnegative955 p)
def d961 (p : Pattern) : Int := if p 133 then d937 p else d951 p
theorem agree961 (p q : Pattern) (h : Agree support p q) : d961 p = d961 q := by
  simp only [d961, h 133 (by decide), agree937 p q h, agree951 p q h]
theorem nonnegative961 (p : Pattern) : 0 ≤ d961 p :=
  nonnegative_ite (p 133) (nonnegative937 p) (nonnegative951 p)
def d962 (p : Pattern) : Int := if p 132 then d961 p else d951 p
theorem agree962 (p q : Pattern) (h : Agree support p q) : d962 p = d962 q := by
  simp only [d962, h 132 (by decide), agree961 p q h, agree951 p q h]
theorem nonnegative962 (p : Pattern) : 0 ≤ d962 p :=
  nonnegative_ite (p 132) (nonnegative961 p) (nonnegative951 p)
def d963 (p : Pattern) : Int := if p 113 then d962 p else d942 p
theorem agree963 (p q : Pattern) (h : Agree support p q) : d963 p = d963 q := by
  simp only [d963, h 113 (by decide), agree962 p q h, agree942 p q h]
theorem nonnegative963 (p : Pattern) : 0 ≤ d963 p :=
  nonnegative_ite (p 113) (nonnegative962 p) (nonnegative942 p)
def d964 (p : Pattern) : Int := if p 133 then d2 p else d957 p
theorem agree964 (p q : Pattern) (h : Agree support p q) : d964 p = d964 q := by
  simp only [d964, h 133 (by decide), agree2 p q h, agree957 p q h]
theorem nonnegative964 (p : Pattern) : 0 ≤ d964 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative957 p)
def d965 (p : Pattern) : Int := if p 132 then d964 p else d957 p
theorem agree965 (p q : Pattern) (h : Agree support p q) : d965 p = d965 q := by
  simp only [d965, h 132 (by decide), agree964 p q h, agree957 p q h]
theorem nonnegative965 (p : Pattern) : 0 ≤ d965 p :=
  nonnegative_ite (p 132) (nonnegative964 p) (nonnegative957 p)
def d966 (p : Pattern) : Int := if p 133 then d2 p else d956 p
theorem agree966 (p q : Pattern) (h : Agree support p q) : d966 p = d966 q := by
  simp only [d966, h 133 (by decide), agree2 p q h, agree956 p q h]
theorem nonnegative966 (p : Pattern) : 0 ≤ d966 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative956 p)
def d967 (p : Pattern) : Int := if p 132 then d966 p else d956 p
theorem agree967 (p q : Pattern) (h : Agree support p q) : d967 p = d967 q := by
  simp only [d967, h 132 (by decide), agree966 p q h, agree956 p q h]
theorem nonnegative967 (p : Pattern) : 0 ≤ d967 p :=
  nonnegative_ite (p 132) (nonnegative966 p) (nonnegative956 p)
def d968 (p : Pattern) : Int := if p 113 then d967 p else d965 p
theorem agree968 (p q : Pattern) (h : Agree support p q) : d968 p = d968 q := by
  simp only [d968, h 113 (by decide), agree967 p q h, agree965 p q h]
theorem nonnegative968 (p : Pattern) : 0 ≤ d968 p :=
  nonnegative_ite (p 113) (nonnegative967 p) (nonnegative965 p)
def d969 (p : Pattern) : Int := if p 112 then d968 p else d963 p
theorem agree969 (p q : Pattern) (h : Agree support p q) : d969 p = d969 q := by
  simp only [d969, h 112 (by decide), agree968 p q h, agree963 p q h]
theorem nonnegative969 (p : Pattern) : 0 ≤ d969 p :=
  nonnegative_ite (p 112) (nonnegative968 p) (nonnegative963 p)
def d970 (p : Pattern) : Int := if p 106 then d969 p else d960 p
theorem agree970 (p q : Pattern) (h : Agree support p q) : d970 p = d970 q := by
  simp only [d970, h 106 (by decide), agree969 p q h, agree960 p q h]
theorem nonnegative970 (p : Pattern) : 0 ≤ d970 p :=
  nonnegative_ite (p 106) (nonnegative969 p) (nonnegative960 p)
def d971 (p : Pattern) : Int := if p 86 then d970 p else d950 p
theorem agree971 (p q : Pattern) (h : Agree support p q) : d971 p = d971 q := by
  simp only [d971, h 86 (by decide), agree970 p q h, agree950 p q h]
theorem nonnegative971 (p : Pattern) : 0 ≤ d971 p :=
  nonnegative_ite (p 86) (nonnegative970 p) (nonnegative950 p)
def d972 (p : Pattern) : Int := if p 112 then d948 p else d942 p
theorem agree972 (p q : Pattern) (h : Agree support p q) : d972 p = d972 q := by
  simp only [d972, h 112 (by decide), agree948 p q h, agree942 p q h]
theorem nonnegative972 (p : Pattern) : 0 ≤ d972 p :=
  nonnegative_ite (p 112) (nonnegative948 p) (nonnegative942 p)
def d973 (p : Pattern) : Int := if p 106 then d972 p else d936 p
theorem agree973 (p q : Pattern) (h : Agree support p q) : d973 p = d973 q := by
  simp only [d973, h 106 (by decide), agree972 p q h, agree936 p q h]
theorem nonnegative973 (p : Pattern) : 0 ≤ d973 p :=
  nonnegative_ite (p 106) (nonnegative972 p) (nonnegative936 p)
def d974 (p : Pattern) : Int := if p 133 then d937 p else d956 p
theorem agree974 (p q : Pattern) (h : Agree support p q) : d974 p = d974 q := by
  simp only [d974, h 133 (by decide), agree937 p q h, agree956 p q h]
theorem nonnegative974 (p : Pattern) : 0 ≤ d974 p :=
  nonnegative_ite (p 133) (nonnegative937 p) (nonnegative956 p)
def d975 (p : Pattern) : Int := if p 132 then d974 p else d956 p
theorem agree975 (p q : Pattern) (h : Agree support p q) : d975 p = d975 q := by
  simp only [d975, h 132 (by decide), agree974 p q h, agree956 p q h]
theorem nonnegative975 (p : Pattern) : 0 ≤ d975 p :=
  nonnegative_ite (p 132) (nonnegative974 p) (nonnegative956 p)
def d976 (p : Pattern) : Int := if p 113 then d975 p else d959 p
theorem agree976 (p q : Pattern) (h : Agree support p q) : d976 p = d976 q := by
  simp only [d976, h 113 (by decide), agree975 p q h, agree959 p q h]
theorem nonnegative976 (p : Pattern) : 0 ≤ d976 p :=
  nonnegative_ite (p 113) (nonnegative975 p) (nonnegative959 p)
def d977 (p : Pattern) : Int := if p 112 then d976 p else d955 p
theorem agree977 (p q : Pattern) (h : Agree support p q) : d977 p = d977 q := by
  simp only [d977, h 112 (by decide), agree976 p q h, agree955 p q h]
theorem nonnegative977 (p : Pattern) : 0 ≤ d977 p :=
  nonnegative_ite (p 112) (nonnegative976 p) (nonnegative955 p)
def d978 (p : Pattern) : Int := if p 113 then d947 p else d942 p
theorem agree978 (p q : Pattern) (h : Agree support p q) : d978 p = d978 q := by
  simp only [d978, h 113 (by decide), agree947 p q h, agree942 p q h]
theorem nonnegative978 (p : Pattern) : 0 ≤ d978 p :=
  nonnegative_ite (p 113) (nonnegative947 p) (nonnegative942 p)
def d979 (p : Pattern) : Int := if p 113 then d2 p else d967 p
theorem agree979 (p q : Pattern) (h : Agree support p q) : d979 p = d979 q := by
  simp only [d979, h 113 (by decide), agree2 p q h, agree967 p q h]
theorem nonnegative979 (p : Pattern) : 0 ≤ d979 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative967 p)
def d980 (p : Pattern) : Int := if p 112 then d979 p else d978 p
theorem agree980 (p q : Pattern) (h : Agree support p q) : d980 p = d980 q := by
  simp only [d980, h 112 (by decide), agree979 p q h, agree978 p q h]
theorem nonnegative980 (p : Pattern) : 0 ≤ d980 p :=
  nonnegative_ite (p 112) (nonnegative979 p) (nonnegative978 p)
def d981 (p : Pattern) : Int := if p 106 then d980 p else d977 p
theorem agree981 (p q : Pattern) (h : Agree support p q) : d981 p = d981 q := by
  simp only [d981, h 106 (by decide), agree980 p q h, agree977 p q h]
theorem nonnegative981 (p : Pattern) : 0 ≤ d981 p :=
  nonnegative_ite (p 106) (nonnegative980 p) (nonnegative977 p)
def d982 (p : Pattern) : Int := if p 86 then d981 p else d973 p
theorem agree982 (p q : Pattern) (h : Agree support p q) : d982 p = d982 q := by
  simp only [d982, h 86 (by decide), agree981 p q h, agree973 p q h]
theorem nonnegative982 (p : Pattern) : 0 ≤ d982 p :=
  nonnegative_ite (p 86) (nonnegative981 p) (nonnegative973 p)
def d983 (p : Pattern) : Int := if p 80 then d982 p else d971 p
theorem agree983 (p q : Pattern) (h : Agree support p q) : d983 p = d983 q := by
  simp only [d983, h 80 (by decide), agree982 p q h, agree971 p q h]
theorem nonnegative983 (p : Pattern) : 0 ≤ d983 p :=
  nonnegative_ite (p 80) (nonnegative982 p) (nonnegative971 p)
def d984 (p : Pattern) : Int := if p 133 then d0 p else d915 p
theorem agree984 (p q : Pattern) (h : Agree support p q) : d984 p = d984 q := by
  simp only [d984, h 133 (by decide), agree0 p q h, agree915 p q h]
theorem nonnegative984 (p : Pattern) : 0 ≤ d984 p :=
  nonnegative_ite (p 133) (nonnegative0 p) (nonnegative915 p)
def d985 (p : Pattern) : Int := if p 161 then d0 p else d1 p
theorem agree985 (p q : Pattern) (h : Agree support p q) : d985 p = d985 q := by
  simp only [d985, h 161 (by decide), agree0 p q h, agree1 p q h]
theorem nonnegative985 (p : Pattern) : 0 ≤ d985 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative1 p)
def d986 (p : Pattern) : Int := if p 158 then d2 p else d37 p
theorem agree986 (p q : Pattern) (h : Agree support p q) : d986 p = d986 q := by
  simp only [d986, h 158 (by decide), agree2 p q h, agree37 p q h]
theorem nonnegative986 (p : Pattern) : 0 ≤ d986 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative37 p)
def d987 (p : Pattern) : Int := if p 158 then d2 p else d39 p
theorem agree987 (p q : Pattern) (h : Agree support p q) : d987 p = d987 q := by
  simp only [d987, h 158 (by decide), agree2 p q h, agree39 p q h]
theorem nonnegative987 (p : Pattern) : 0 ≤ d987 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative39 p)
def d988 (p : Pattern) : Int := if p 139 then d987 p else d986 p
theorem agree988 (p q : Pattern) (h : Agree support p q) : d988 p = d988 q := by
  simp only [d988, h 139 (by decide), agree987 p q h, agree986 p q h]
theorem nonnegative988 (p : Pattern) : 0 ≤ d988 p :=
  nonnegative_ite (p 139) (nonnegative987 p) (nonnegative986 p)
def d989 (p : Pattern) : Int := if p 138 then d988 p else d986 p
theorem agree989 (p q : Pattern) (h : Agree support p q) : d989 p = d989 q := by
  simp only [d989, h 138 (by decide), agree988 p q h, agree986 p q h]
theorem nonnegative989 (p : Pattern) : 0 ≤ d989 p :=
  nonnegative_ite (p 138) (nonnegative988 p) (nonnegative986 p)
def d990 (p : Pattern) : Int := if p 134 then d989 p else d700 p
theorem agree990 (p q : Pattern) (h : Agree support p q) : d990 p = d990 q := by
  simp only [d990, h 134 (by decide), agree989 p q h, agree700 p q h]
theorem nonnegative990 (p : Pattern) : 0 ≤ d990 p :=
  nonnegative_ite (p 134) (nonnegative989 p) (nonnegative700 p)
def d991 (p : Pattern) : Int := if p 133 then d990 p else d700 p
theorem agree991 (p q : Pattern) (h : Agree support p q) : d991 p = d991 q := by
  simp only [d991, h 133 (by decide), agree990 p q h, agree700 p q h]
theorem nonnegative991 (p : Pattern) : 0 ≤ d991 p :=
  nonnegative_ite (p 133) (nonnegative990 p) (nonnegative700 p)
def d992 (p : Pattern) : Int := if p 159 then d11 p else d5 p
theorem agree992 (p q : Pattern) (h : Agree support p q) : d992 p = d992 q := by
  simp only [d992, h 159 (by decide), agree11 p q h, agree5 p q h]
theorem nonnegative992 (p : Pattern) : 0 ≤ d992 p :=
  nonnegative_ite (p 159) (nonnegative11 p) (nonnegative5 p)
def d993 (p : Pattern) : Int := if p 158 then d39 p else d992 p
theorem agree993 (p q : Pattern) (h : Agree support p q) : d993 p = d993 q := by
  simp only [d993, h 158 (by decide), agree39 p q h, agree992 p q h]
theorem nonnegative993 (p : Pattern) : 0 ≤ d993 p :=
  nonnegative_ite (p 158) (nonnegative39 p) (nonnegative992 p)
def d994 (p : Pattern) : Int := if p 139 then d987 p else d993 p
theorem agree994 (p q : Pattern) (h : Agree support p q) : d994 p = d994 q := by
  simp only [d994, h 139 (by decide), agree987 p q h, agree993 p q h]
theorem nonnegative994 (p : Pattern) : 0 ≤ d994 p :=
  nonnegative_ite (p 139) (nonnegative987 p) (nonnegative993 p)
def d995 (p : Pattern) : Int := if p 138 then d994 p else d993 p
theorem agree995 (p q : Pattern) (h : Agree support p q) : d995 p = d995 q := by
  simp only [d995, h 138 (by decide), agree994 p q h, agree993 p q h]
theorem nonnegative995 (p : Pattern) : 0 ≤ d995 p :=
  nonnegative_ite (p 138) (nonnegative994 p) (nonnegative993 p)
def d996 (p : Pattern) : Int := if p 134 then d995 p else d700 p
theorem agree996 (p q : Pattern) (h : Agree support p q) : d996 p = d996 q := by
  simp only [d996, h 134 (by decide), agree995 p q h, agree700 p q h]
theorem nonnegative996 (p : Pattern) : 0 ≤ d996 p :=
  nonnegative_ite (p 134) (nonnegative995 p) (nonnegative700 p)
def d997 (p : Pattern) : Int := if p 133 then d990 p else d996 p
theorem agree997 (p q : Pattern) (h : Agree support p q) : d997 p = d997 q := by
  simp only [d997, h 133 (by decide), agree990 p q h, agree996 p q h]
theorem nonnegative997 (p : Pattern) : 0 ≤ d997 p :=
  nonnegative_ite (p 133) (nonnegative990 p) (nonnegative996 p)
def d998 (p : Pattern) : Int := if p 132 then d997 p else d991 p
theorem agree998 (p q : Pattern) (h : Agree support p q) : d998 p = d998 q := by
  simp only [d998, h 132 (by decide), agree997 p q h, agree991 p q h]
theorem nonnegative998 (p : Pattern) : 0 ≤ d998 p :=
  nonnegative_ite (p 132) (nonnegative997 p) (nonnegative991 p)
def d999 (p : Pattern) : Int := if p 134 then d988 p else d699 p
theorem agree999 (p q : Pattern) (h : Agree support p q) : d999 p = d999 q := by
  simp only [d999, h 134 (by decide), agree988 p q h, agree699 p q h]
theorem nonnegative999 (p : Pattern) : 0 ≤ d999 p :=
  nonnegative_ite (p 134) (nonnegative988 p) (nonnegative699 p)
def d1000 (p : Pattern) : Int := if p 133 then d999 p else d699 p
theorem agree1000 (p q : Pattern) (h : Agree support p q) : d1000 p = d1000 q := by
  simp only [d1000, h 133 (by decide), agree999 p q h, agree699 p q h]
theorem nonnegative1000 (p : Pattern) : 0 ≤ d1000 p :=
  nonnegative_ite (p 133) (nonnegative999 p) (nonnegative699 p)
def d1001 (p : Pattern) : Int := if p 134 then d994 p else d699 p
theorem agree1001 (p q : Pattern) (h : Agree support p q) : d1001 p = d1001 q := by
  simp only [d1001, h 134 (by decide), agree994 p q h, agree699 p q h]
theorem nonnegative1001 (p : Pattern) : 0 ≤ d1001 p :=
  nonnegative_ite (p 134) (nonnegative994 p) (nonnegative699 p)
def d1002 (p : Pattern) : Int := if p 133 then d999 p else d1001 p
theorem agree1002 (p q : Pattern) (h : Agree support p q) : d1002 p = d1002 q := by
  simp only [d1002, h 133 (by decide), agree999 p q h, agree1001 p q h]
theorem nonnegative1002 (p : Pattern) : 0 ≤ d1002 p :=
  nonnegative_ite (p 133) (nonnegative999 p) (nonnegative1001 p)
def d1003 (p : Pattern) : Int := if p 132 then d1002 p else d1000 p
theorem agree1003 (p q : Pattern) (h : Agree support p q) : d1003 p = d1003 q := by
  simp only [d1003, h 132 (by decide), agree1002 p q h, agree1000 p q h]
theorem nonnegative1003 (p : Pattern) : 0 ≤ d1003 p :=
  nonnegative_ite (p 132) (nonnegative1002 p) (nonnegative1000 p)
def d1004 (p : Pattern) : Int := if p 139 then d2 p else d986 p
theorem agree1004 (p q : Pattern) (h : Agree support p q) : d1004 p = d1004 q := by
  simp only [d1004, h 139 (by decide), agree2 p q h, agree986 p q h]
theorem nonnegative1004 (p : Pattern) : 0 ≤ d1004 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative986 p)
def d1005 (p : Pattern) : Int := if p 138 then d1004 p else d988 p
theorem agree1005 (p q : Pattern) (h : Agree support p q) : d1005 p = d1005 q := by
  simp only [d1005, h 138 (by decide), agree1004 p q h, agree988 p q h]
theorem nonnegative1005 (p : Pattern) : 0 ≤ d1005 p :=
  nonnegative_ite (p 138) (nonnegative1004 p) (nonnegative988 p)
def d1006 (p : Pattern) : Int := if p 134 then d1005 p else d702 p
theorem agree1006 (p q : Pattern) (h : Agree support p q) : d1006 p = d1006 q := by
  simp only [d1006, h 134 (by decide), agree1005 p q h, agree702 p q h]
theorem nonnegative1006 (p : Pattern) : 0 ≤ d1006 p :=
  nonnegative_ite (p 134) (nonnegative1005 p) (nonnegative702 p)
def d1007 (p : Pattern) : Int := if p 133 then d1006 p else d702 p
theorem agree1007 (p q : Pattern) (h : Agree support p q) : d1007 p = d1007 q := by
  simp only [d1007, h 133 (by decide), agree1006 p q h, agree702 p q h]
theorem nonnegative1007 (p : Pattern) : 0 ≤ d1007 p :=
  nonnegative_ite (p 133) (nonnegative1006 p) (nonnegative702 p)
def d1008 (p : Pattern) : Int := if p 139 then d2 p else d993 p
theorem agree1008 (p q : Pattern) (h : Agree support p q) : d1008 p = d1008 q := by
  simp only [d1008, h 139 (by decide), agree2 p q h, agree993 p q h]
theorem nonnegative1008 (p : Pattern) : 0 ≤ d1008 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative993 p)
def d1009 (p : Pattern) : Int := if p 138 then d1008 p else d994 p
theorem agree1009 (p q : Pattern) (h : Agree support p q) : d1009 p = d1009 q := by
  simp only [d1009, h 138 (by decide), agree1008 p q h, agree994 p q h]
theorem nonnegative1009 (p : Pattern) : 0 ≤ d1009 p :=
  nonnegative_ite (p 138) (nonnegative1008 p) (nonnegative994 p)
def d1010 (p : Pattern) : Int := if p 134 then d1009 p else d702 p
theorem agree1010 (p q : Pattern) (h : Agree support p q) : d1010 p = d1010 q := by
  simp only [d1010, h 134 (by decide), agree1009 p q h, agree702 p q h]
theorem nonnegative1010 (p : Pattern) : 0 ≤ d1010 p :=
  nonnegative_ite (p 134) (nonnegative1009 p) (nonnegative702 p)
def d1011 (p : Pattern) : Int := if p 133 then d1006 p else d1010 p
theorem agree1011 (p q : Pattern) (h : Agree support p q) : d1011 p = d1011 q := by
  simp only [d1011, h 133 (by decide), agree1006 p q h, agree1010 p q h]
theorem nonnegative1011 (p : Pattern) : 0 ≤ d1011 p :=
  nonnegative_ite (p 133) (nonnegative1006 p) (nonnegative1010 p)
def d1012 (p : Pattern) : Int := if p 132 then d1011 p else d1007 p
theorem agree1012 (p q : Pattern) (h : Agree support p q) : d1012 p = d1012 q := by
  simp only [d1012, h 132 (by decide), agree1011 p q h, agree1007 p q h]
theorem nonnegative1012 (p : Pattern) : 0 ≤ d1012 p :=
  nonnegative_ite (p 132) (nonnegative1011 p) (nonnegative1007 p)
def d1013 (p : Pattern) : Int := if p 113 then d1012 p else d1003 p
theorem agree1013 (p q : Pattern) (h : Agree support p q) : d1013 p = d1013 q := by
  simp only [d1013, h 113 (by decide), agree1012 p q h, agree1003 p q h]
theorem nonnegative1013 (p : Pattern) : 0 ≤ d1013 p :=
  nonnegative_ite (p 113) (nonnegative1012 p) (nonnegative1003 p)
def d1014 (p : Pattern) : Int := if p 112 then d1013 p else d998 p
theorem agree1014 (p q : Pattern) (h : Agree support p q) : d1014 p = d1014 q := by
  simp only [d1014, h 112 (by decide), agree1013 p q h, agree998 p q h]
theorem nonnegative1014 (p : Pattern) : 0 ≤ d1014 p :=
  nonnegative_ite (p 112) (nonnegative1013 p) (nonnegative998 p)
def d1015 (p : Pattern) : Int := if p 139 then d2 p else d987 p
theorem agree1015 (p q : Pattern) (h : Agree support p q) : d1015 p = d1015 q := by
  simp only [d1015, h 139 (by decide), agree2 p q h, agree987 p q h]
theorem nonnegative1015 (p : Pattern) : 0 ≤ d1015 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative987 p)
def d1016 (p : Pattern) : Int := if p 138 then d1015 p else d987 p
theorem agree1016 (p q : Pattern) (h : Agree support p q) : d1016 p = d1016 q := by
  simp only [d1016, h 138 (by decide), agree1015 p q h, agree987 p q h]
theorem nonnegative1016 (p : Pattern) : 0 ≤ d1016 p :=
  nonnegative_ite (p 138) (nonnegative1015 p) (nonnegative987 p)
def d1017 (p : Pattern) : Int := if p 134 then d1016 p else d706 p
theorem agree1017 (p q : Pattern) (h : Agree support p q) : d1017 p = d1017 q := by
  simp only [d1017, h 134 (by decide), agree1016 p q h, agree706 p q h]
theorem nonnegative1017 (p : Pattern) : 0 ≤ d1017 p :=
  nonnegative_ite (p 134) (nonnegative1016 p) (nonnegative706 p)
def d1018 (p : Pattern) : Int := if p 133 then d1017 p else d990 p
theorem agree1018 (p q : Pattern) (h : Agree support p q) : d1018 p = d1018 q := by
  simp only [d1018, h 133 (by decide), agree1017 p q h, agree990 p q h]
theorem nonnegative1018 (p : Pattern) : 0 ≤ d1018 p :=
  nonnegative_ite (p 133) (nonnegative1017 p) (nonnegative990 p)
def d1019 (p : Pattern) : Int := if p 132 then d1018 p else d991 p
theorem agree1019 (p q : Pattern) (h : Agree support p q) : d1019 p = d1019 q := by
  simp only [d1019, h 132 (by decide), agree1018 p q h, agree991 p q h]
theorem nonnegative1019 (p : Pattern) : 0 ≤ d1019 p :=
  nonnegative_ite (p 132) (nonnegative1018 p) (nonnegative991 p)
def d1020 (p : Pattern) : Int := if p 134 then d1015 p else d705 p
theorem agree1020 (p q : Pattern) (h : Agree support p q) : d1020 p = d1020 q := by
  simp only [d1020, h 134 (by decide), agree1015 p q h, agree705 p q h]
theorem nonnegative1020 (p : Pattern) : 0 ≤ d1020 p :=
  nonnegative_ite (p 134) (nonnegative1015 p) (nonnegative705 p)
def d1021 (p : Pattern) : Int := if p 133 then d1020 p else d990 p
theorem agree1021 (p q : Pattern) (h : Agree support p q) : d1021 p = d1021 q := by
  simp only [d1021, h 133 (by decide), agree1020 p q h, agree990 p q h]
theorem nonnegative1021 (p : Pattern) : 0 ≤ d1021 p :=
  nonnegative_ite (p 133) (nonnegative1020 p) (nonnegative990 p)
def d1022 (p : Pattern) : Int := if p 132 then d1021 p else d991 p
theorem agree1022 (p q : Pattern) (h : Agree support p q) : d1022 p = d1022 q := by
  simp only [d1022, h 132 (by decide), agree1021 p q h, agree991 p q h]
theorem nonnegative1022 (p : Pattern) : 0 ≤ d1022 p :=
  nonnegative_ite (p 132) (nonnegative1021 p) (nonnegative991 p)
def d1023 (p : Pattern) : Int := if p 113 then d1022 p else d1019 p
theorem agree1023 (p q : Pattern) (h : Agree support p q) : d1023 p = d1023 q := by
  simp only [d1023, h 113 (by decide), agree1022 p q h, agree1019 p q h]
theorem nonnegative1023 (p : Pattern) : 0 ≤ d1023 p :=
  nonnegative_ite (p 113) (nonnegative1022 p) (nonnegative1019 p)
def d1024 (p : Pattern) : Int := if p 133 then d1020 p else d999 p
theorem agree1024 (p q : Pattern) (h : Agree support p q) : d1024 p = d1024 q := by
  simp only [d1024, h 133 (by decide), agree1020 p q h, agree999 p q h]
theorem nonnegative1024 (p : Pattern) : 0 ≤ d1024 p :=
  nonnegative_ite (p 133) (nonnegative1020 p) (nonnegative999 p)
def d1025 (p : Pattern) : Int := if p 132 then d1024 p else d1000 p
theorem agree1025 (p q : Pattern) (h : Agree support p q) : d1025 p = d1025 q := by
  simp only [d1025, h 132 (by decide), agree1024 p q h, agree1000 p q h]
theorem nonnegative1025 (p : Pattern) : 0 ≤ d1025 p :=
  nonnegative_ite (p 132) (nonnegative1024 p) (nonnegative1000 p)
def d1026 (p : Pattern) : Int := if p 133 then d1020 p else d1006 p
theorem agree1026 (p q : Pattern) (h : Agree support p q) : d1026 p = d1026 q := by
  simp only [d1026, h 133 (by decide), agree1020 p q h, agree1006 p q h]
theorem nonnegative1026 (p : Pattern) : 0 ≤ d1026 p :=
  nonnegative_ite (p 133) (nonnegative1020 p) (nonnegative1006 p)
def d1027 (p : Pattern) : Int := if p 132 then d1026 p else d1007 p
theorem agree1027 (p q : Pattern) (h : Agree support p q) : d1027 p = d1027 q := by
  simp only [d1027, h 132 (by decide), agree1026 p q h, agree1007 p q h]
theorem nonnegative1027 (p : Pattern) : 0 ≤ d1027 p :=
  nonnegative_ite (p 132) (nonnegative1026 p) (nonnegative1007 p)
def d1028 (p : Pattern) : Int := if p 113 then d1027 p else d1025 p
theorem agree1028 (p q : Pattern) (h : Agree support p q) : d1028 p = d1028 q := by
  simp only [d1028, h 113 (by decide), agree1027 p q h, agree1025 p q h]
theorem nonnegative1028 (p : Pattern) : 0 ≤ d1028 p :=
  nonnegative_ite (p 113) (nonnegative1027 p) (nonnegative1025 p)
def d1029 (p : Pattern) : Int := if p 112 then d1028 p else d1023 p
theorem agree1029 (p q : Pattern) (h : Agree support p q) : d1029 p = d1029 q := by
  simp only [d1029, h 112 (by decide), agree1028 p q h, agree1023 p q h]
theorem nonnegative1029 (p : Pattern) : 0 ≤ d1029 p :=
  nonnegative_ite (p 112) (nonnegative1028 p) (nonnegative1023 p)
def d1030 (p : Pattern) : Int := if p 106 then d1029 p else d1014 p
theorem agree1030 (p q : Pattern) (h : Agree support p q) : d1030 p = d1030 q := by
  simp only [d1030, h 106 (by decide), agree1029 p q h, agree1014 p q h]
theorem nonnegative1030 (p : Pattern) : 0 ≤ d1030 p :=
  nonnegative_ite (p 106) (nonnegative1029 p) (nonnegative1014 p)
def d1031 (p : Pattern) : Int := if p 138 then d1004 p else d986 p
theorem agree1031 (p q : Pattern) (h : Agree support p q) : d1031 p = d1031 q := by
  simp only [d1031, h 138 (by decide), agree1004 p q h, agree986 p q h]
theorem nonnegative1031 (p : Pattern) : 0 ≤ d1031 p :=
  nonnegative_ite (p 138) (nonnegative1004 p) (nonnegative986 p)
def d1032 (p : Pattern) : Int := if p 134 then d1031 p else d719 p
theorem agree1032 (p q : Pattern) (h : Agree support p q) : d1032 p = d1032 q := by
  simp only [d1032, h 134 (by decide), agree1031 p q h, agree719 p q h]
theorem nonnegative1032 (p : Pattern) : 0 ≤ d1032 p :=
  nonnegative_ite (p 134) (nonnegative1031 p) (nonnegative719 p)
def d1033 (p : Pattern) : Int := if p 133 then d1032 p else d719 p
theorem agree1033 (p q : Pattern) (h : Agree support p q) : d1033 p = d1033 q := by
  simp only [d1033, h 133 (by decide), agree1032 p q h, agree719 p q h]
theorem nonnegative1033 (p : Pattern) : 0 ≤ d1033 p :=
  nonnegative_ite (p 133) (nonnegative1032 p) (nonnegative719 p)
def d1034 (p : Pattern) : Int := if p 138 then d1008 p else d993 p
theorem agree1034 (p q : Pattern) (h : Agree support p q) : d1034 p = d1034 q := by
  simp only [d1034, h 138 (by decide), agree1008 p q h, agree993 p q h]
theorem nonnegative1034 (p : Pattern) : 0 ≤ d1034 p :=
  nonnegative_ite (p 138) (nonnegative1008 p) (nonnegative993 p)
def d1035 (p : Pattern) : Int := if p 134 then d1034 p else d719 p
theorem agree1035 (p q : Pattern) (h : Agree support p q) : d1035 p = d1035 q := by
  simp only [d1035, h 134 (by decide), agree1034 p q h, agree719 p q h]
theorem nonnegative1035 (p : Pattern) : 0 ≤ d1035 p :=
  nonnegative_ite (p 134) (nonnegative1034 p) (nonnegative719 p)
def d1036 (p : Pattern) : Int := if p 133 then d1032 p else d1035 p
theorem agree1036 (p q : Pattern) (h : Agree support p q) : d1036 p = d1036 q := by
  simp only [d1036, h 133 (by decide), agree1032 p q h, agree1035 p q h]
theorem nonnegative1036 (p : Pattern) : 0 ≤ d1036 p :=
  nonnegative_ite (p 133) (nonnegative1032 p) (nonnegative1035 p)
def d1037 (p : Pattern) : Int := if p 132 then d1036 p else d1033 p
theorem agree1037 (p q : Pattern) (h : Agree support p q) : d1037 p = d1037 q := by
  simp only [d1037, h 132 (by decide), agree1036 p q h, agree1033 p q h]
theorem nonnegative1037 (p : Pattern) : 0 ≤ d1037 p :=
  nonnegative_ite (p 132) (nonnegative1036 p) (nonnegative1033 p)
def d1038 (p : Pattern) : Int := if p 113 then d1037 p else d998 p
theorem agree1038 (p q : Pattern) (h : Agree support p q) : d1038 p = d1038 q := by
  simp only [d1038, h 113 (by decide), agree1037 p q h, agree998 p q h]
theorem nonnegative1038 (p : Pattern) : 0 ≤ d1038 p :=
  nonnegative_ite (p 113) (nonnegative1037 p) (nonnegative998 p)
def d1039 (p : Pattern) : Int := if p 133 then d1017 p else d706 p
theorem agree1039 (p q : Pattern) (h : Agree support p q) : d1039 p = d1039 q := by
  simp only [d1039, h 133 (by decide), agree1017 p q h, agree706 p q h]
theorem nonnegative1039 (p : Pattern) : 0 ≤ d1039 p :=
  nonnegative_ite (p 133) (nonnegative1017 p) (nonnegative706 p)
def d1040 (p : Pattern) : Int := if p 132 then d1017 p else d1039 p
theorem agree1040 (p q : Pattern) (h : Agree support p q) : d1040 p = d1040 q := by
  simp only [d1040, h 132 (by decide), agree1017 p q h, agree1039 p q h]
theorem nonnegative1040 (p : Pattern) : 0 ≤ d1040 p :=
  nonnegative_ite (p 132) (nonnegative1017 p) (nonnegative1039 p)
def d1041 (p : Pattern) : Int := if p 112 then d1040 p else d1038 p
theorem agree1041 (p q : Pattern) (h : Agree support p q) : d1041 p = d1041 q := by
  simp only [d1041, h 112 (by decide), agree1040 p q h, agree1038 p q h]
theorem nonnegative1041 (p : Pattern) : 0 ≤ d1041 p :=
  nonnegative_ite (p 112) (nonnegative1040 p) (nonnegative1038 p)
def d1042 (p : Pattern) : Int := if p 133 then d1020 p else d1032 p
theorem agree1042 (p q : Pattern) (h : Agree support p q) : d1042 p = d1042 q := by
  simp only [d1042, h 133 (by decide), agree1020 p q h, agree1032 p q h]
theorem nonnegative1042 (p : Pattern) : 0 ≤ d1042 p :=
  nonnegative_ite (p 133) (nonnegative1020 p) (nonnegative1032 p)
def d1043 (p : Pattern) : Int := if p 132 then d1042 p else d1033 p
theorem agree1043 (p q : Pattern) (h : Agree support p q) : d1043 p = d1043 q := by
  simp only [d1043, h 132 (by decide), agree1042 p q h, agree1033 p q h]
theorem nonnegative1043 (p : Pattern) : 0 ≤ d1043 p :=
  nonnegative_ite (p 132) (nonnegative1042 p) (nonnegative1033 p)
def d1044 (p : Pattern) : Int := if p 113 then d1043 p else d1022 p
theorem agree1044 (p q : Pattern) (h : Agree support p q) : d1044 p = d1044 q := by
  simp only [d1044, h 113 (by decide), agree1043 p q h, agree1022 p q h]
theorem nonnegative1044 (p : Pattern) : 0 ≤ d1044 p :=
  nonnegative_ite (p 113) (nonnegative1043 p) (nonnegative1022 p)
def d1045 (p : Pattern) : Int := if p 133 then d2 p else d1017 p
theorem agree1045 (p q : Pattern) (h : Agree support p q) : d1045 p = d1045 q := by
  simp only [d1045, h 133 (by decide), agree2 p q h, agree1017 p q h]
theorem nonnegative1045 (p : Pattern) : 0 ≤ d1045 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1017 p)
def d1046 (p : Pattern) : Int := if p 132 then d1045 p else d1039 p
theorem agree1046 (p q : Pattern) (h : Agree support p q) : d1046 p = d1046 q := by
  simp only [d1046, h 132 (by decide), agree1045 p q h, agree1039 p q h]
theorem nonnegative1046 (p : Pattern) : 0 ≤ d1046 p :=
  nonnegative_ite (p 132) (nonnegative1045 p) (nonnegative1039 p)
def d1047 (p : Pattern) : Int := if p 133 then d1020 p else d705 p
theorem agree1047 (p q : Pattern) (h : Agree support p q) : d1047 p = d1047 q := by
  simp only [d1047, h 133 (by decide), agree1020 p q h, agree705 p q h]
theorem nonnegative1047 (p : Pattern) : 0 ≤ d1047 p :=
  nonnegative_ite (p 133) (nonnegative1020 p) (nonnegative705 p)
def d1048 (p : Pattern) : Int := if p 133 then d2 p else d1020 p
theorem agree1048 (p q : Pattern) (h : Agree support p q) : d1048 p = d1048 q := by
  simp only [d1048, h 133 (by decide), agree2 p q h, agree1020 p q h]
theorem nonnegative1048 (p : Pattern) : 0 ≤ d1048 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1020 p)
def d1049 (p : Pattern) : Int := if p 132 then d1048 p else d1047 p
theorem agree1049 (p q : Pattern) (h : Agree support p q) : d1049 p = d1049 q := by
  simp only [d1049, h 132 (by decide), agree1048 p q h, agree1047 p q h]
theorem nonnegative1049 (p : Pattern) : 0 ≤ d1049 p :=
  nonnegative_ite (p 132) (nonnegative1048 p) (nonnegative1047 p)
def d1050 (p : Pattern) : Int := if p 113 then d1049 p else d1046 p
theorem agree1050 (p q : Pattern) (h : Agree support p q) : d1050 p = d1050 q := by
  simp only [d1050, h 113 (by decide), agree1049 p q h, agree1046 p q h]
theorem nonnegative1050 (p : Pattern) : 0 ≤ d1050 p :=
  nonnegative_ite (p 113) (nonnegative1049 p) (nonnegative1046 p)
def d1051 (p : Pattern) : Int := if p 112 then d1050 p else d1044 p
theorem agree1051 (p q : Pattern) (h : Agree support p q) : d1051 p = d1051 q := by
  simp only [d1051, h 112 (by decide), agree1050 p q h, agree1044 p q h]
theorem nonnegative1051 (p : Pattern) : 0 ≤ d1051 p :=
  nonnegative_ite (p 112) (nonnegative1050 p) (nonnegative1044 p)
def d1052 (p : Pattern) : Int := if p 106 then d1051 p else d1041 p
theorem agree1052 (p q : Pattern) (h : Agree support p q) : d1052 p = d1052 q := by
  simp only [d1052, h 106 (by decide), agree1051 p q h, agree1041 p q h]
theorem nonnegative1052 (p : Pattern) : 0 ≤ d1052 p :=
  nonnegative_ite (p 106) (nonnegative1051 p) (nonnegative1041 p)
def d1053 (p : Pattern) : Int := if p 86 then d1052 p else d1030 p
theorem agree1053 (p q : Pattern) (h : Agree support p q) : d1053 p = d1053 q := by
  simp only [d1053, h 86 (by decide), agree1052 p q h, agree1030 p q h]
theorem nonnegative1053 (p : Pattern) : 0 ≤ d1053 p :=
  nonnegative_ite (p 86) (nonnegative1052 p) (nonnegative1030 p)
def d1054 (p : Pattern) : Int := if p 112 then d1028 p else d1022 p
theorem agree1054 (p q : Pattern) (h : Agree support p q) : d1054 p = d1054 q := by
  simp only [d1054, h 112 (by decide), agree1028 p q h, agree1022 p q h]
theorem nonnegative1054 (p : Pattern) : 0 ≤ d1054 p :=
  nonnegative_ite (p 112) (nonnegative1028 p) (nonnegative1022 p)
def d1055 (p : Pattern) : Int := if p 106 then d1054 p else d1014 p
theorem agree1055 (p q : Pattern) (h : Agree support p q) : d1055 p = d1055 q := by
  simp only [d1055, h 106 (by decide), agree1054 p q h, agree1014 p q h]
theorem nonnegative1055 (p : Pattern) : 0 ≤ d1055 p :=
  nonnegative_ite (p 106) (nonnegative1054 p) (nonnegative1014 p)
def d1056 (p : Pattern) : Int := if p 139 then d986 p else d993 p
theorem agree1056 (p q : Pattern) (h : Agree support p q) : d1056 p = d1056 q := by
  simp only [d1056, h 139 (by decide), agree986 p q h, agree993 p q h]
theorem nonnegative1056 (p : Pattern) : 0 ≤ d1056 p :=
  nonnegative_ite (p 139) (nonnegative986 p) (nonnegative993 p)
def d1057 (p : Pattern) : Int := if p 138 then d1008 p else d1056 p
theorem agree1057 (p q : Pattern) (h : Agree support p q) : d1057 p = d1057 q := by
  simp only [d1057, h 138 (by decide), agree1008 p q h, agree1056 p q h]
theorem nonnegative1057 (p : Pattern) : 0 ≤ d1057 p :=
  nonnegative_ite (p 138) (nonnegative1008 p) (nonnegative1056 p)
def d1058 (p : Pattern) : Int := if p 134 then d1057 p else d719 p
theorem agree1058 (p q : Pattern) (h : Agree support p q) : d1058 p = d1058 q := by
  simp only [d1058, h 134 (by decide), agree1057 p q h, agree719 p q h]
theorem nonnegative1058 (p : Pattern) : 0 ≤ d1058 p :=
  nonnegative_ite (p 134) (nonnegative1057 p) (nonnegative719 p)
def d1059 (p : Pattern) : Int := if p 133 then d1032 p else d1058 p
theorem agree1059 (p q : Pattern) (h : Agree support p q) : d1059 p = d1059 q := by
  simp only [d1059, h 133 (by decide), agree1032 p q h, agree1058 p q h]
theorem nonnegative1059 (p : Pattern) : 0 ≤ d1059 p :=
  nonnegative_ite (p 133) (nonnegative1032 p) (nonnegative1058 p)
def d1060 (p : Pattern) : Int := if p 132 then d1059 p else d1033 p
theorem agree1060 (p q : Pattern) (h : Agree support p q) : d1060 p = d1060 q := by
  simp only [d1060, h 132 (by decide), agree1059 p q h, agree1033 p q h]
theorem nonnegative1060 (p : Pattern) : 0 ≤ d1060 p :=
  nonnegative_ite (p 132) (nonnegative1059 p) (nonnegative1033 p)
def d1061 (p : Pattern) : Int := if p 113 then d1060 p else d998 p
theorem agree1061 (p q : Pattern) (h : Agree support p q) : d1061 p = d1061 q := by
  simp only [d1061, h 113 (by decide), agree1060 p q h, agree998 p q h]
theorem nonnegative1061 (p : Pattern) : 0 ≤ d1061 p :=
  nonnegative_ite (p 113) (nonnegative1060 p) (nonnegative998 p)
def d1062 (p : Pattern) : Int := if p 132 then d1020 p else d1047 p
theorem agree1062 (p q : Pattern) (h : Agree support p q) : d1062 p = d1062 q := by
  simp only [d1062, h 132 (by decide), agree1020 p q h, agree1047 p q h]
theorem nonnegative1062 (p : Pattern) : 0 ≤ d1062 p :=
  nonnegative_ite (p 132) (nonnegative1020 p) (nonnegative1047 p)
def d1063 (p : Pattern) : Int := if p 113 then d1062 p else d1040 p
theorem agree1063 (p q : Pattern) (h : Agree support p q) : d1063 p = d1063 q := by
  simp only [d1063, h 113 (by decide), agree1062 p q h, agree1040 p q h]
theorem nonnegative1063 (p : Pattern) : 0 ≤ d1063 p :=
  nonnegative_ite (p 113) (nonnegative1062 p) (nonnegative1040 p)
def d1064 (p : Pattern) : Int := if p 112 then d1063 p else d1061 p
theorem agree1064 (p q : Pattern) (h : Agree support p q) : d1064 p = d1064 q := by
  simp only [d1064, h 112 (by decide), agree1063 p q h, agree1061 p q h]
theorem nonnegative1064 (p : Pattern) : 0 ≤ d1064 p :=
  nonnegative_ite (p 112) (nonnegative1063 p) (nonnegative1061 p)
def d1065 (p : Pattern) : Int := if p 113 then d1027 p else d1022 p
theorem agree1065 (p q : Pattern) (h : Agree support p q) : d1065 p = d1065 q := by
  simp only [d1065, h 113 (by decide), agree1027 p q h, agree1022 p q h]
theorem nonnegative1065 (p : Pattern) : 0 ≤ d1065 p :=
  nonnegative_ite (p 113) (nonnegative1027 p) (nonnegative1022 p)
def d1066 (p : Pattern) : Int := if p 113 then d2 p else d1049 p
theorem agree1066 (p q : Pattern) (h : Agree support p q) : d1066 p = d1066 q := by
  simp only [d1066, h 113 (by decide), agree2 p q h, agree1049 p q h]
theorem nonnegative1066 (p : Pattern) : 0 ≤ d1066 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1049 p)
def d1067 (p : Pattern) : Int := if p 112 then d1066 p else d1065 p
theorem agree1067 (p q : Pattern) (h : Agree support p q) : d1067 p = d1067 q := by
  simp only [d1067, h 112 (by decide), agree1066 p q h, agree1065 p q h]
theorem nonnegative1067 (p : Pattern) : 0 ≤ d1067 p :=
  nonnegative_ite (p 112) (nonnegative1066 p) (nonnegative1065 p)
def d1068 (p : Pattern) : Int := if p 106 then d1067 p else d1064 p
theorem agree1068 (p q : Pattern) (h : Agree support p q) : d1068 p = d1068 q := by
  simp only [d1068, h 106 (by decide), agree1067 p q h, agree1064 p q h]
theorem nonnegative1068 (p : Pattern) : 0 ≤ d1068 p :=
  nonnegative_ite (p 106) (nonnegative1067 p) (nonnegative1064 p)
def d1069 (p : Pattern) : Int := if p 86 then d1068 p else d1055 p
theorem agree1069 (p q : Pattern) (h : Agree support p q) : d1069 p = d1069 q := by
  simp only [d1069, h 86 (by decide), agree1068 p q h, agree1055 p q h]
theorem nonnegative1069 (p : Pattern) : 0 ≤ d1069 p :=
  nonnegative_ite (p 86) (nonnegative1068 p) (nonnegative1055 p)
def d1070 (p : Pattern) : Int := if p 80 then d1069 p else d1053 p
theorem agree1070 (p q : Pattern) (h : Agree support p q) : d1070 p = d1070 q := by
  simp only [d1070, h 80 (by decide), agree1069 p q h, agree1053 p q h]
theorem nonnegative1070 (p : Pattern) : 0 ≤ d1070 p :=
  nonnegative_ite (p 80) (nonnegative1069 p) (nonnegative1053 p)
def d1071 (p : Pattern) : Int := if p 80 then d118 p else d85 p
theorem agree1071 (p q : Pattern) (h : Agree support p q) : d1071 p = d1071 q := by
  simp only [d1071, h 80 (by decide), agree118 p q h, agree85 p q h]
theorem nonnegative1071 (p : Pattern) : 0 ≤ d1071 p :=
  nonnegative_ite (p 80) (nonnegative118 p) (nonnegative85 p)
def d1072 (p : Pattern) : Int := if p 112 then d0 p else d857 p
theorem agree1072 (p q : Pattern) (h : Agree support p q) : d1072 p = d1072 q := by
  simp only [d1072, h 112 (by decide), agree0 p q h, agree857 p q h]
theorem nonnegative1072 (p : Pattern) : 0 ≤ d1072 p :=
  nonnegative_ite (p 112) (nonnegative0 p) (nonnegative857 p)
def d1073 (p : Pattern) : Int := if p 112 then d0 p else d865 p
theorem agree1073 (p q : Pattern) (h : Agree support p q) : d1073 p = d1073 q := by
  simp only [d1073, h 112 (by decide), agree0 p q h, agree865 p q h]
theorem nonnegative1073 (p : Pattern) : 0 ≤ d1073 p :=
  nonnegative_ite (p 112) (nonnegative0 p) (nonnegative865 p)
def d1074 (p : Pattern) : Int := if p 112 then d51 p else d45 p
theorem agree1074 (p q : Pattern) (h : Agree support p q) : d1074 p = d1074 q := by
  simp only [d1074, h 112 (by decide), agree51 p q h, agree45 p q h]
theorem nonnegative1074 (p : Pattern) : 0 ≤ d1074 p :=
  nonnegative_ite (p 112) (nonnegative51 p) (nonnegative45 p)
def d1075 (p : Pattern) : Int := if p 112 then d80 p else d74 p
theorem agree1075 (p q : Pattern) (h : Agree support p q) : d1075 p = d1075 q := by
  simp only [d1075, h 112 (by decide), agree80 p q h, agree74 p q h]
theorem nonnegative1075 (p : Pattern) : 0 ≤ d1075 p :=
  nonnegative_ite (p 112) (nonnegative80 p) (nonnegative74 p)
def d1076 (p : Pattern) : Int := if p 106 then d1075 p else d1074 p
theorem agree1076 (p q : Pattern) (h : Agree support p q) : d1076 p = d1076 q := by
  simp only [d1076, h 106 (by decide), agree1075 p q h, agree1074 p q h]
theorem nonnegative1076 (p : Pattern) : 0 ≤ d1076 p :=
  nonnegative_ite (p 106) (nonnegative1075 p) (nonnegative1074 p)
def d1077 (p : Pattern) : Int := if p 112 then d102 p else d45 p
theorem agree1077 (p q : Pattern) (h : Agree support p q) : d1077 p = d1077 q := by
  simp only [d1077, h 112 (by decide), agree102 p q h, agree45 p q h]
theorem nonnegative1077 (p : Pattern) : 0 ≤ d1077 p :=
  nonnegative_ite (p 112) (nonnegative102 p) (nonnegative45 p)
def d1078 (p : Pattern) : Int := if p 112 then d108 p else d77 p
theorem agree1078 (p q : Pattern) (h : Agree support p q) : d1078 p = d1078 q := by
  simp only [d1078, h 112 (by decide), agree108 p q h, agree77 p q h]
theorem nonnegative1078 (p : Pattern) : 0 ≤ d1078 p :=
  nonnegative_ite (p 112) (nonnegative108 p) (nonnegative77 p)
def d1079 (p : Pattern) : Int := if p 106 then d1078 p else d1077 p
theorem agree1079 (p q : Pattern) (h : Agree support p q) : d1079 p = d1079 q := by
  simp only [d1079, h 106 (by decide), agree1078 p q h, agree1077 p q h]
theorem nonnegative1079 (p : Pattern) : 0 ≤ d1079 p :=
  nonnegative_ite (p 106) (nonnegative1078 p) (nonnegative1077 p)
end NetHack.Sokoban32Refined
