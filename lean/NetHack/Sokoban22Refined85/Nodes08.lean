/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d960 (p : Pattern) : Int := if p 162 then d12 p else d796 p
theorem agree960 (p q : Pattern) (h : Agree support p q) : d960 p = d960 q := by
  simp only [d960, h 162 (by decide), agree12 p q h, agree796 p q h]
theorem nonnegative960 (p : Pattern) : 0 ≤ d960 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative796 p)
def d961 (p : Pattern) : Int := if p 162 then d12 p else d176 p
theorem agree961 (p q : Pattern) (h : Agree support p q) : d961 p = d961 q := by
  simp only [d961, h 162 (by decide), agree12 p q h, agree176 p q h]
theorem nonnegative961 (p : Pattern) : 0 ≤ d961 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative176 p)
def d962 (p : Pattern) : Int := if p 161 then d961 p else d960 p
theorem agree962 (p q : Pattern) (h : Agree support p q) : d962 p = d962 q := by
  simp only [d962, h 161 (by decide), agree961 p q h, agree960 p q h]
theorem nonnegative962 (p : Pattern) : 0 ≤ d962 p :=
  nonnegative_ite (p 161) (nonnegative961 p) (nonnegative960 p)
def d963 (p : Pattern) : Int := if p 160 then d962 p else d959 p
theorem agree963 (p q : Pattern) (h : Agree support p q) : d963 p = d963 q := by
  simp only [d963, h 160 (by decide), agree962 p q h, agree959 p q h]
theorem nonnegative963 (p : Pattern) : 0 ≤ d963 p :=
  nonnegative_ite (p 160) (nonnegative962 p) (nonnegative959 p)
def d964 (p : Pattern) : Int := if p 141 then d963 p else d956 p
theorem agree964 (p q : Pattern) (h : Agree support p q) : d964 p = d964 q := by
  simp only [d964, h 141 (by decide), agree963 p q h, agree956 p q h]
theorem nonnegative964 (p : Pattern) : 0 ≤ d964 p :=
  nonnegative_ite (p 141) (nonnegative963 p) (nonnegative956 p)
def d965 (p : Pattern) : Int := if p 162 then d361 p else d16 p
theorem agree965 (p q : Pattern) (h : Agree support p q) : d965 p = d965 q := by
  simp only [d965, h 162 (by decide), agree361 p q h, agree16 p q h]
theorem nonnegative965 (p : Pattern) : 0 ≤ d965 p :=
  nonnegative_ite (p 162) (nonnegative361 p) (nonnegative16 p)
def d966 (p : Pattern) : Int := if p 162 then d12 p else d54 p
theorem agree966 (p q : Pattern) (h : Agree support p q) : d966 p = d966 q := by
  simp only [d966, h 162 (by decide), agree12 p q h, agree54 p q h]
theorem nonnegative966 (p : Pattern) : 0 ≤ d966 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative54 p)
def d967 (p : Pattern) : Int := if p 161 then d966 p else d965 p
theorem agree967 (p q : Pattern) (h : Agree support p q) : d967 p = d967 q := by
  simp only [d967, h 161 (by decide), agree966 p q h, agree965 p q h]
theorem nonnegative967 (p : Pattern) : 0 ≤ d967 p :=
  nonnegative_ite (p 161) (nonnegative966 p) (nonnegative965 p)
def d968 (p : Pattern) : Int := if p 162 then d12 p else d53 p
theorem agree968 (p q : Pattern) (h : Agree support p q) : d968 p = d968 q := by
  simp only [d968, h 162 (by decide), agree12 p q h, agree53 p q h]
theorem nonnegative968 (p : Pattern) : 0 ≤ d968 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative53 p)
def d969 (p : Pattern) : Int := if p 161 then d12 p else d968 p
theorem agree969 (p q : Pattern) (h : Agree support p q) : d969 p = d969 q := by
  simp only [d969, h 161 (by decide), agree12 p q h, agree968 p q h]
theorem nonnegative969 (p : Pattern) : 0 ≤ d969 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative968 p)
def d970 (p : Pattern) : Int := if p 160 then d969 p else d967 p
theorem agree970 (p q : Pattern) (h : Agree support p q) : d970 p = d970 q := by
  simp only [d970, h 160 (by decide), agree969 p q h, agree967 p q h]
theorem nonnegative970 (p : Pattern) : 0 ≤ d970 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative967 p)
def d971 (p : Pattern) : Int := if p 162 then d374 p else d54 p
theorem agree971 (p q : Pattern) (h : Agree support p q) : d971 p = d971 q := by
  simp only [d971, h 162 (by decide), agree374 p q h, agree54 p q h]
theorem nonnegative971 (p : Pattern) : 0 ≤ d971 p :=
  nonnegative_ite (p 162) (nonnegative374 p) (nonnegative54 p)
def d972 (p : Pattern) : Int := if p 162 then d12 p else d808 p
theorem agree972 (p q : Pattern) (h : Agree support p q) : d972 p = d972 q := by
  simp only [d972, h 162 (by decide), agree12 p q h, agree808 p q h]
theorem nonnegative972 (p : Pattern) : 0 ≤ d972 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative808 p)
def d973 (p : Pattern) : Int := if p 161 then d972 p else d971 p
theorem agree973 (p q : Pattern) (h : Agree support p q) : d973 p = d973 q := by
  simp only [d973, h 161 (by decide), agree972 p q h, agree971 p q h]
theorem nonnegative973 (p : Pattern) : 0 ≤ d973 p :=
  nonnegative_ite (p 161) (nonnegative972 p) (nonnegative971 p)
def d974 (p : Pattern) : Int := if p 161 then d12 p else d972 p
theorem agree974 (p q : Pattern) (h : Agree support p q) : d974 p = d974 q := by
  simp only [d974, h 161 (by decide), agree12 p q h, agree972 p q h]
theorem nonnegative974 (p : Pattern) : 0 ≤ d974 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative972 p)
def d975 (p : Pattern) : Int := if p 160 then d974 p else d973 p
theorem agree975 (p q : Pattern) (h : Agree support p q) : d975 p = d975 q := by
  simp only [d975, h 160 (by decide), agree974 p q h, agree973 p q h]
theorem nonnegative975 (p : Pattern) : 0 ≤ d975 p :=
  nonnegative_ite (p 160) (nonnegative974 p) (nonnegative973 p)
def d976 (p : Pattern) : Int := if p 141 then d975 p else d970 p
theorem agree976 (p q : Pattern) (h : Agree support p q) : d976 p = d976 q := by
  simp only [d976, h 141 (by decide), agree975 p q h, agree970 p q h]
theorem nonnegative976 (p : Pattern) : 0 ≤ d976 p :=
  nonnegative_ite (p 141) (nonnegative975 p) (nonnegative970 p)
def d977 (p : Pattern) : Int := if p 138 then d976 p else d964 p
theorem agree977 (p q : Pattern) (h : Agree support p q) : d977 p = d977 q := by
  simp only [d977, h 138 (by decide), agree976 p q h, agree964 p q h]
theorem nonnegative977 (p : Pattern) : 0 ≤ d977 p :=
  nonnegative_ite (p 138) (nonnegative976 p) (nonnegative964 p)
def d978 (p : Pattern) : Int := if p 162 then d389 p else d16 p
theorem agree978 (p q : Pattern) (h : Agree support p q) : d978 p = d978 q := by
  simp only [d978, h 162 (by decide), agree389 p q h, agree16 p q h]
theorem nonnegative978 (p : Pattern) : 0 ≤ d978 p :=
  nonnegative_ite (p 162) (nonnegative389 p) (nonnegative16 p)
def d979 (p : Pattern) : Int := if p 161 then d966 p else d978 p
theorem agree979 (p q : Pattern) (h : Agree support p q) : d979 p = d979 q := by
  simp only [d979, h 161 (by decide), agree966 p q h, agree978 p q h]
theorem nonnegative979 (p : Pattern) : 0 ≤ d979 p :=
  nonnegative_ite (p 161) (nonnegative966 p) (nonnegative978 p)
def d980 (p : Pattern) : Int := if p 160 then d969 p else d979 p
theorem agree980 (p q : Pattern) (h : Agree support p q) : d980 p = d980 q := by
  simp only [d980, h 160 (by decide), agree969 p q h, agree979 p q h]
theorem nonnegative980 (p : Pattern) : 0 ≤ d980 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative979 p)
def d981 (p : Pattern) : Int := if p 162 then d371 p else d54 p
theorem agree981 (p q : Pattern) (h : Agree support p q) : d981 p = d981 q := by
  simp only [d981, h 162 (by decide), agree371 p q h, agree54 p q h]
theorem nonnegative981 (p : Pattern) : 0 ≤ d981 p :=
  nonnegative_ite (p 162) (nonnegative371 p) (nonnegative54 p)
def d982 (p : Pattern) : Int := if p 161 then d972 p else d981 p
theorem agree982 (p q : Pattern) (h : Agree support p q) : d982 p = d982 q := by
  simp only [d982, h 161 (by decide), agree972 p q h, agree981 p q h]
theorem nonnegative982 (p : Pattern) : 0 ≤ d982 p :=
  nonnegative_ite (p 161) (nonnegative972 p) (nonnegative981 p)
def d983 (p : Pattern) : Int := if p 160 then d974 p else d982 p
theorem agree983 (p q : Pattern) (h : Agree support p q) : d983 p = d983 q := by
  simp only [d983, h 160 (by decide), agree974 p q h, agree982 p q h]
theorem nonnegative983 (p : Pattern) : 0 ≤ d983 p :=
  nonnegative_ite (p 160) (nonnegative974 p) (nonnegative982 p)
def d984 (p : Pattern) : Int := if p 141 then d983 p else d980 p
theorem agree984 (p q : Pattern) (h : Agree support p q) : d984 p = d984 q := by
  simp only [d984, h 141 (by decide), agree983 p q h, agree980 p q h]
theorem nonnegative984 (p : Pattern) : 0 ≤ d984 p :=
  nonnegative_ite (p 141) (nonnegative983 p) (nonnegative980 p)
def d985 (p : Pattern) : Int := if p 162 then d12 p else d89 p
theorem agree985 (p q : Pattern) (h : Agree support p q) : d985 p = d985 q := by
  simp only [d985, h 162 (by decide), agree12 p q h, agree89 p q h]
theorem nonnegative985 (p : Pattern) : 0 ≤ d985 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative89 p)
def d986 (p : Pattern) : Int := if p 161 then d91 p else d985 p
theorem agree986 (p q : Pattern) (h : Agree support p q) : d986 p = d986 q := by
  simp only [d986, h 161 (by decide), agree91 p q h, agree985 p q h]
theorem nonnegative986 (p : Pattern) : 0 ≤ d986 p :=
  nonnegative_ite (p 161) (nonnegative91 p) (nonnegative985 p)
def d987 (p : Pattern) : Int := if p 160 then d93 p else d986 p
theorem agree987 (p q : Pattern) (h : Agree support p q) : d987 p = d987 q := by
  simp only [d987, h 160 (by decide), agree93 p q h, agree986 p q h]
theorem nonnegative987 (p : Pattern) : 0 ≤ d987 p :=
  nonnegative_ite (p 160) (nonnegative93 p) (nonnegative986 p)
def d988 (p : Pattern) : Int := if p 141 then d95 p else d987 p
theorem agree988 (p q : Pattern) (h : Agree support p q) : d988 p = d988 q := by
  simp only [d988, h 141 (by decide), agree95 p q h, agree987 p q h]
theorem nonnegative988 (p : Pattern) : 0 ≤ d988 p :=
  nonnegative_ite (p 141) (nonnegative95 p) (nonnegative987 p)
def d989 (p : Pattern) : Int := if p 138 then d988 p else d984 p
theorem agree989 (p q : Pattern) (h : Agree support p q) : d989 p = d989 q := by
  simp only [d989, h 138 (by decide), agree988 p q h, agree984 p q h]
theorem nonnegative989 (p : Pattern) : 0 ≤ d989 p :=
  nonnegative_ite (p 138) (nonnegative988 p) (nonnegative984 p)
def d990 (p : Pattern) : Int := if p 116 then d989 p else d977 p
theorem agree990 (p q : Pattern) (h : Agree support p q) : d990 p = d990 q := by
  simp only [d990, h 116 (by decide), agree989 p q h, agree977 p q h]
theorem nonnegative990 (p : Pattern) : 0 ≤ d990 p :=
  nonnegative_ite (p 116) (nonnegative989 p) (nonnegative977 p)
def d991 (p : Pattern) : Int := if p 162 then d386 p else d16 p
theorem agree991 (p q : Pattern) (h : Agree support p q) : d991 p = d991 q := by
  simp only [d991, h 162 (by decide), agree386 p q h, agree16 p q h]
theorem nonnegative991 (p : Pattern) : 0 ≤ d991 p :=
  nonnegative_ite (p 162) (nonnegative386 p) (nonnegative16 p)
def d992 (p : Pattern) : Int := if p 162 then d12 p else d950 p
theorem agree992 (p q : Pattern) (h : Agree support p q) : d992 p = d992 q := by
  simp only [d992, h 162 (by decide), agree12 p q h, agree950 p q h]
theorem nonnegative992 (p : Pattern) : 0 ≤ d992 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative950 p)
def d993 (p : Pattern) : Int := if p 161 then d992 p else d991 p
theorem agree993 (p q : Pattern) (h : Agree support p q) : d993 p = d993 q := by
  simp only [d993, h 161 (by decide), agree992 p q h, agree991 p q h]
theorem nonnegative993 (p : Pattern) : 0 ≤ d993 p :=
  nonnegative_ite (p 161) (nonnegative992 p) (nonnegative991 p)
def d994 (p : Pattern) : Int := if p 162 then d12 p else d33 p
theorem agree994 (p q : Pattern) (h : Agree support p q) : d994 p = d994 q := by
  simp only [d994, h 162 (by decide), agree12 p q h, agree33 p q h]
theorem nonnegative994 (p : Pattern) : 0 ≤ d994 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative33 p)
def d995 (p : Pattern) : Int := if p 161 then d954 p else d994 p
theorem agree995 (p q : Pattern) (h : Agree support p q) : d995 p = d995 q := by
  simp only [d995, h 161 (by decide), agree954 p q h, agree994 p q h]
theorem nonnegative995 (p : Pattern) : 0 ≤ d995 p :=
  nonnegative_ite (p 161) (nonnegative954 p) (nonnegative994 p)
def d996 (p : Pattern) : Int := if p 160 then d995 p else d993 p
theorem agree996 (p q : Pattern) (h : Agree support p q) : d996 p = d996 q := by
  simp only [d996, h 160 (by decide), agree995 p q h, agree993 p q h]
theorem nonnegative996 (p : Pattern) : 0 ≤ d996 p :=
  nonnegative_ite (p 160) (nonnegative995 p) (nonnegative993 p)
def d997 (p : Pattern) : Int := if p 162 then d361 p else d54 p
theorem agree997 (p q : Pattern) (h : Agree support p q) : d997 p = d997 q := by
  simp only [d997, h 162 (by decide), agree361 p q h, agree54 p q h]
theorem nonnegative997 (p : Pattern) : 0 ≤ d997 p :=
  nonnegative_ite (p 162) (nonnegative361 p) (nonnegative54 p)
def d998 (p : Pattern) : Int := if p 161 then d960 p else d997 p
theorem agree998 (p q : Pattern) (h : Agree support p q) : d998 p = d998 q := by
  simp only [d998, h 161 (by decide), agree960 p q h, agree997 p q h]
theorem nonnegative998 (p : Pattern) : 0 ≤ d998 p :=
  nonnegative_ite (p 161) (nonnegative960 p) (nonnegative997 p)
def d999 (p : Pattern) : Int := if p 160 then d962 p else d998 p
theorem agree999 (p q : Pattern) (h : Agree support p q) : d999 p = d999 q := by
  simp only [d999, h 160 (by decide), agree962 p q h, agree998 p q h]
theorem nonnegative999 (p : Pattern) : 0 ≤ d999 p :=
  nonnegative_ite (p 160) (nonnegative962 p) (nonnegative998 p)
def d1000 (p : Pattern) : Int := if p 141 then d999 p else d996 p
theorem agree1000 (p q : Pattern) (h : Agree support p q) : d1000 p = d1000 q := by
  simp only [d1000, h 141 (by decide), agree999 p q h, agree996 p q h]
theorem nonnegative1000 (p : Pattern) : 0 ≤ d1000 p :=
  nonnegative_ite (p 141) (nonnegative999 p) (nonnegative996 p)
def d1001 (p : Pattern) : Int := if p 162 then d12 p else d16 p
theorem agree1001 (p q : Pattern) (h : Agree support p q) : d1001 p = d1001 q := by
  simp only [d1001, h 162 (by decide), agree12 p q h, agree16 p q h]
theorem nonnegative1001 (p : Pattern) : 0 ≤ d1001 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative16 p)
def d1002 (p : Pattern) : Int := if p 161 then d966 p else d1001 p
theorem agree1002 (p q : Pattern) (h : Agree support p q) : d1002 p = d1002 q := by
  simp only [d1002, h 161 (by decide), agree966 p q h, agree1001 p q h]
theorem nonnegative1002 (p : Pattern) : 0 ≤ d1002 p :=
  nonnegative_ite (p 161) (nonnegative966 p) (nonnegative1001 p)
def d1003 (p : Pattern) : Int := if p 160 then d969 p else d1002 p
theorem agree1003 (p q : Pattern) (h : Agree support p q) : d1003 p = d1003 q := by
  simp only [d1003, h 160 (by decide), agree969 p q h, agree1002 p q h]
theorem nonnegative1003 (p : Pattern) : 0 ≤ d1003 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative1002 p)
def d1004 (p : Pattern) : Int := if p 161 then d972 p else d966 p
theorem agree1004 (p q : Pattern) (h : Agree support p q) : d1004 p = d1004 q := by
  simp only [d1004, h 161 (by decide), agree972 p q h, agree966 p q h]
theorem nonnegative1004 (p : Pattern) : 0 ≤ d1004 p :=
  nonnegative_ite (p 161) (nonnegative972 p) (nonnegative966 p)
def d1005 (p : Pattern) : Int := if p 160 then d974 p else d1004 p
theorem agree1005 (p q : Pattern) (h : Agree support p q) : d1005 p = d1005 q := by
  simp only [d1005, h 160 (by decide), agree974 p q h, agree1004 p q h]
theorem nonnegative1005 (p : Pattern) : 0 ≤ d1005 p :=
  nonnegative_ite (p 160) (nonnegative974 p) (nonnegative1004 p)
def d1006 (p : Pattern) : Int := if p 141 then d1005 p else d1003 p
theorem agree1006 (p q : Pattern) (h : Agree support p q) : d1006 p = d1006 q := by
  simp only [d1006, h 141 (by decide), agree1005 p q h, agree1003 p q h]
theorem nonnegative1006 (p : Pattern) : 0 ≤ d1006 p :=
  nonnegative_ite (p 141) (nonnegative1005 p) (nonnegative1003 p)
def d1007 (p : Pattern) : Int := if p 138 then d1006 p else d1000 p
theorem agree1007 (p q : Pattern) (h : Agree support p q) : d1007 p = d1007 q := by
  simp only [d1007, h 138 (by decide), agree1006 p q h, agree1000 p q h]
theorem nonnegative1007 (p : Pattern) : 0 ≤ d1007 p :=
  nonnegative_ite (p 138) (nonnegative1006 p) (nonnegative1000 p)
def d1008 (p : Pattern) : Int := if p 162 then d374 p else d16 p
theorem agree1008 (p q : Pattern) (h : Agree support p q) : d1008 p = d1008 q := by
  simp only [d1008, h 162 (by decide), agree374 p q h, agree16 p q h]
theorem nonnegative1008 (p : Pattern) : 0 ≤ d1008 p :=
  nonnegative_ite (p 162) (nonnegative374 p) (nonnegative16 p)
def d1009 (p : Pattern) : Int := if p 161 then d966 p else d1008 p
theorem agree1009 (p q : Pattern) (h : Agree support p q) : d1009 p = d1009 q := by
  simp only [d1009, h 161 (by decide), agree966 p q h, agree1008 p q h]
theorem nonnegative1009 (p : Pattern) : 0 ≤ d1009 p :=
  nonnegative_ite (p 161) (nonnegative966 p) (nonnegative1008 p)
def d1010 (p : Pattern) : Int := if p 160 then d969 p else d1009 p
theorem agree1010 (p q : Pattern) (h : Agree support p q) : d1010 p = d1010 q := by
  simp only [d1010, h 160 (by decide), agree969 p q h, agree1009 p q h]
theorem nonnegative1010 (p : Pattern) : 0 ≤ d1010 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative1009 p)
def d1011 (p : Pattern) : Int := if p 141 then d1005 p else d1010 p
theorem agree1011 (p q : Pattern) (h : Agree support p q) : d1011 p = d1011 q := by
  simp only [d1011, h 141 (by decide), agree1005 p q h, agree1010 p q h]
theorem nonnegative1011 (p : Pattern) : 0 ≤ d1011 p :=
  nonnegative_ite (p 141) (nonnegative1005 p) (nonnegative1010 p)
def d1012 (p : Pattern) : Int := if p 138 then d12 p else d1011 p
theorem agree1012 (p q : Pattern) (h : Agree support p q) : d1012 p = d1012 q := by
  simp only [d1012, h 138 (by decide), agree12 p q h, agree1011 p q h]
theorem nonnegative1012 (p : Pattern) : 0 ≤ d1012 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1011 p)
def d1013 (p : Pattern) : Int := if p 116 then d1012 p else d1007 p
theorem agree1013 (p q : Pattern) (h : Agree support p q) : d1013 p = d1013 q := by
  simp only [d1013, h 116 (by decide), agree1012 p q h, agree1007 p q h]
theorem nonnegative1013 (p : Pattern) : 0 ≤ d1013 p :=
  nonnegative_ite (p 116) (nonnegative1012 p) (nonnegative1007 p)
def d1014 (p : Pattern) : Int := if p 115 then d1013 p else d990 p
theorem agree1014 (p q : Pattern) (h : Agree support p q) : d1014 p = d1014 q := by
  simp only [d1014, h 115 (by decide), agree1013 p q h, agree990 p q h]
theorem nonnegative1014 (p : Pattern) : 0 ≤ d1014 p :=
  nonnegative_ite (p 115) (nonnegative1013 p) (nonnegative990 p)
def d1015 (p : Pattern) : Int := if p 162 then d355 p else d16 p
theorem agree1015 (p q : Pattern) (h : Agree support p q) : d1015 p = d1015 q := by
  simp only [d1015, h 162 (by decide), agree355 p q h, agree16 p q h]
theorem nonnegative1015 (p : Pattern) : 0 ≤ d1015 p :=
  nonnegative_ite (p 162) (nonnegative355 p) (nonnegative16 p)
def d1016 (p : Pattern) : Int := if p 162 then d371 p else d950 p
theorem agree1016 (p q : Pattern) (h : Agree support p q) : d1016 p = d1016 q := by
  simp only [d1016, h 162 (by decide), agree371 p q h, agree950 p q h]
theorem nonnegative1016 (p : Pattern) : 0 ≤ d1016 p :=
  nonnegative_ite (p 162) (nonnegative371 p) (nonnegative950 p)
def d1017 (p : Pattern) : Int := if p 161 then d1016 p else d1015 p
theorem agree1017 (p q : Pattern) (h : Agree support p q) : d1017 p = d1017 q := by
  simp only [d1017, h 161 (by decide), agree1016 p q h, agree1015 p q h]
theorem nonnegative1017 (p : Pattern) : 0 ≤ d1017 p :=
  nonnegative_ite (p 161) (nonnegative1016 p) (nonnegative1015 p)
def d1018 (p : Pattern) : Int := if p 162 then d374 p else d33 p
theorem agree1018 (p q : Pattern) (h : Agree support p q) : d1018 p = d1018 q := by
  simp only [d1018, h 162 (by decide), agree374 p q h, agree33 p q h]
theorem nonnegative1018 (p : Pattern) : 0 ≤ d1018 p :=
  nonnegative_ite (p 162) (nonnegative374 p) (nonnegative33 p)
def d1019 (p : Pattern) : Int := if p 161 then d954 p else d1018 p
theorem agree1019 (p q : Pattern) (h : Agree support p q) : d1019 p = d1019 q := by
  simp only [d1019, h 161 (by decide), agree954 p q h, agree1018 p q h]
theorem nonnegative1019 (p : Pattern) : 0 ≤ d1019 p :=
  nonnegative_ite (p 161) (nonnegative954 p) (nonnegative1018 p)
def d1020 (p : Pattern) : Int := if p 160 then d1019 p else d1017 p
theorem agree1020 (p q : Pattern) (h : Agree support p q) : d1020 p = d1020 q := by
  simp only [d1020, h 160 (by decide), agree1019 p q h, agree1017 p q h]
theorem nonnegative1020 (p : Pattern) : 0 ≤ d1020 p :=
  nonnegative_ite (p 160) (nonnegative1019 p) (nonnegative1017 p)
def d1021 (p : Pattern) : Int := if p 162 then d386 p else d54 p
theorem agree1021 (p q : Pattern) (h : Agree support p q) : d1021 p = d1021 q := by
  simp only [d1021, h 162 (by decide), agree386 p q h, agree54 p q h]
theorem nonnegative1021 (p : Pattern) : 0 ≤ d1021 p :=
  nonnegative_ite (p 162) (nonnegative386 p) (nonnegative54 p)
def d1022 (p : Pattern) : Int := if p 161 then d960 p else d1021 p
theorem agree1022 (p q : Pattern) (h : Agree support p q) : d1022 p = d1022 q := by
  simp only [d1022, h 161 (by decide), agree960 p q h, agree1021 p q h]
theorem nonnegative1022 (p : Pattern) : 0 ≤ d1022 p :=
  nonnegative_ite (p 161) (nonnegative960 p) (nonnegative1021 p)
def d1023 (p : Pattern) : Int := if p 160 then d962 p else d1022 p
theorem agree1023 (p q : Pattern) (h : Agree support p q) : d1023 p = d1023 q := by
  simp only [d1023, h 160 (by decide), agree962 p q h, agree1022 p q h]
theorem nonnegative1023 (p : Pattern) : 0 ≤ d1023 p :=
  nonnegative_ite (p 160) (nonnegative962 p) (nonnegative1022 p)
def d1024 (p : Pattern) : Int := if p 141 then d1023 p else d1020 p
theorem agree1024 (p q : Pattern) (h : Agree support p q) : d1024 p = d1024 q := by
  simp only [d1024, h 141 (by decide), agree1023 p q h, agree1020 p q h]
theorem nonnegative1024 (p : Pattern) : 0 ≤ d1024 p :=
  nonnegative_ite (p 141) (nonnegative1023 p) (nonnegative1020 p)
def d1025 (p : Pattern) : Int := if p 162 then d371 p else d16 p
theorem agree1025 (p q : Pattern) (h : Agree support p q) : d1025 p = d1025 q := by
  simp only [d1025, h 162 (by decide), agree371 p q h, agree16 p q h]
theorem nonnegative1025 (p : Pattern) : 0 ≤ d1025 p :=
  nonnegative_ite (p 162) (nonnegative371 p) (nonnegative16 p)
def d1026 (p : Pattern) : Int := if p 161 then d966 p else d1025 p
theorem agree1026 (p q : Pattern) (h : Agree support p q) : d1026 p = d1026 q := by
  simp only [d1026, h 161 (by decide), agree966 p q h, agree1025 p q h]
theorem nonnegative1026 (p : Pattern) : 0 ≤ d1026 p :=
  nonnegative_ite (p 161) (nonnegative966 p) (nonnegative1025 p)
def d1027 (p : Pattern) : Int := if p 160 then d969 p else d1026 p
theorem agree1027 (p q : Pattern) (h : Agree support p q) : d1027 p = d1027 q := by
  simp only [d1027, h 160 (by decide), agree969 p q h, agree1026 p q h]
theorem nonnegative1027 (p : Pattern) : 0 ≤ d1027 p :=
  nonnegative_ite (p 160) (nonnegative969 p) (nonnegative1026 p)
def d1028 (p : Pattern) : Int := if p 141 then d1005 p else d1027 p
theorem agree1028 (p q : Pattern) (h : Agree support p q) : d1028 p = d1028 q := by
  simp only [d1028, h 141 (by decide), agree1005 p q h, agree1027 p q h]
theorem nonnegative1028 (p : Pattern) : 0 ≤ d1028 p :=
  nonnegative_ite (p 141) (nonnegative1005 p) (nonnegative1027 p)
def d1029 (p : Pattern) : Int := if p 138 then d1028 p else d1024 p
theorem agree1029 (p q : Pattern) (h : Agree support p q) : d1029 p = d1029 q := by
  simp only [d1029, h 138 (by decide), agree1028 p q h, agree1024 p q h]
theorem nonnegative1029 (p : Pattern) : 0 ≤ d1029 p :=
  nonnegative_ite (p 138) (nonnegative1028 p) (nonnegative1024 p)
def d1030 (p : Pattern) : Int := if p 138 then d988 p else d976 p
theorem agree1030 (p q : Pattern) (h : Agree support p q) : d1030 p = d1030 q := by
  simp only [d1030, h 138 (by decide), agree988 p q h, agree976 p q h]
theorem nonnegative1030 (p : Pattern) : 0 ≤ d1030 p :=
  nonnegative_ite (p 138) (nonnegative988 p) (nonnegative976 p)
def d1031 (p : Pattern) : Int := if p 116 then d1030 p else d1029 p
theorem agree1031 (p q : Pattern) (h : Agree support p q) : d1031 p = d1031 q := by
  simp only [d1031, h 116 (by decide), agree1030 p q h, agree1029 p q h]
theorem nonnegative1031 (p : Pattern) : 0 ≤ d1031 p :=
  nonnegative_ite (p 116) (nonnegative1030 p) (nonnegative1029 p)
def d1032 (p : Pattern) : Int := if p 161 then d992 p else d978 p
theorem agree1032 (p q : Pattern) (h : Agree support p q) : d1032 p = d1032 q := by
  simp only [d1032, h 161 (by decide), agree992 p q h, agree978 p q h]
theorem nonnegative1032 (p : Pattern) : 0 ≤ d1032 p :=
  nonnegative_ite (p 161) (nonnegative992 p) (nonnegative978 p)
def d1033 (p : Pattern) : Int := if p 160 then d995 p else d1032 p
theorem agree1033 (p q : Pattern) (h : Agree support p q) : d1033 p = d1033 q := by
  simp only [d1033, h 160 (by decide), agree995 p q h, agree1032 p q h]
theorem nonnegative1033 (p : Pattern) : 0 ≤ d1033 p :=
  nonnegative_ite (p 160) (nonnegative995 p) (nonnegative1032 p)
def d1034 (p : Pattern) : Int := if p 161 then d960 p else d981 p
theorem agree1034 (p q : Pattern) (h : Agree support p q) : d1034 p = d1034 q := by
  simp only [d1034, h 161 (by decide), agree960 p q h, agree981 p q h]
theorem nonnegative1034 (p : Pattern) : 0 ≤ d1034 p :=
  nonnegative_ite (p 161) (nonnegative960 p) (nonnegative981 p)
def d1035 (p : Pattern) : Int := if p 160 then d962 p else d1034 p
theorem agree1035 (p q : Pattern) (h : Agree support p q) : d1035 p = d1035 q := by
  simp only [d1035, h 160 (by decide), agree962 p q h, agree1034 p q h]
theorem nonnegative1035 (p : Pattern) : 0 ≤ d1035 p :=
  nonnegative_ite (p 160) (nonnegative962 p) (nonnegative1034 p)
def d1036 (p : Pattern) : Int := if p 141 then d1035 p else d1033 p
theorem agree1036 (p q : Pattern) (h : Agree support p q) : d1036 p = d1036 q := by
  simp only [d1036, h 141 (by decide), agree1035 p q h, agree1033 p q h]
theorem nonnegative1036 (p : Pattern) : 0 ≤ d1036 p :=
  nonnegative_ite (p 141) (nonnegative1035 p) (nonnegative1033 p)
def d1037 (p : Pattern) : Int := if p 138 then d1006 p else d1036 p
theorem agree1037 (p q : Pattern) (h : Agree support p q) : d1037 p = d1037 q := by
  simp only [d1037, h 138 (by decide), agree1006 p q h, agree1036 p q h]
theorem nonnegative1037 (p : Pattern) : 0 ≤ d1037 p :=
  nonnegative_ite (p 138) (nonnegative1006 p) (nonnegative1036 p)
def d1038 (p : Pattern) : Int := if p 138 then d12 p else d1006 p
theorem agree1038 (p q : Pattern) (h : Agree support p q) : d1038 p = d1038 q := by
  simp only [d1038, h 138 (by decide), agree12 p q h, agree1006 p q h]
theorem nonnegative1038 (p : Pattern) : 0 ≤ d1038 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative1006 p)
def d1039 (p : Pattern) : Int := if p 116 then d1038 p else d1037 p
theorem agree1039 (p q : Pattern) (h : Agree support p q) : d1039 p = d1039 q := by
  simp only [d1039, h 116 (by decide), agree1038 p q h, agree1037 p q h]
theorem nonnegative1039 (p : Pattern) : 0 ≤ d1039 p :=
  nonnegative_ite (p 116) (nonnegative1038 p) (nonnegative1037 p)
def d1040 (p : Pattern) : Int := if p 115 then d1039 p else d1031 p
theorem agree1040 (p q : Pattern) (h : Agree support p q) : d1040 p = d1040 q := by
  simp only [d1040, h 115 (by decide), agree1039 p q h, agree1031 p q h]
theorem nonnegative1040 (p : Pattern) : 0 ≤ d1040 p :=
  nonnegative_ite (p 115) (nonnegative1039 p) (nonnegative1031 p)
def d1041 (p : Pattern) : Int := if p 71 then d1040 p else d1014 p
theorem agree1041 (p q : Pattern) (h : Agree support p q) : d1041 p = d1041 q := by
  simp only [d1041, h 71 (by decide), agree1040 p q h, agree1014 p q h]
theorem nonnegative1041 (p : Pattern) : 0 ≤ d1041 p :=
  nonnegative_ite (p 71) (nonnegative1040 p) (nonnegative1014 p)
def d1042 (p : Pattern) : Int := if p 162 then d355 p else d105 p
theorem agree1042 (p q : Pattern) (h : Agree support p q) : d1042 p = d1042 q := by
  simp only [d1042, h 162 (by decide), agree355 p q h, agree105 p q h]
theorem nonnegative1042 (p : Pattern) : 0 ≤ d1042 p :=
  nonnegative_ite (p 162) (nonnegative355 p) (nonnegative105 p)
def d1043 (p : Pattern) : Int := if p 163 then d118 p else d105 p
theorem agree1043 (p q : Pattern) (h : Agree support p q) : d1043 p = d1043 q := by
  simp only [d1043, h 163 (by decide), agree118 p q h, agree105 p q h]
theorem nonnegative1043 (p : Pattern) : 0 ≤ d1043 p :=
  nonnegative_ite (p 163) (nonnegative118 p) (nonnegative105 p)
def d1044 (p : Pattern) : Int := if p 162 then d371 p else d1043 p
theorem agree1044 (p q : Pattern) (h : Agree support p q) : d1044 p = d1044 q := by
  simp only [d1044, h 162 (by decide), agree371 p q h, agree1043 p q h]
theorem nonnegative1044 (p : Pattern) : 0 ≤ d1044 p :=
  nonnegative_ite (p 162) (nonnegative371 p) (nonnegative1043 p)
def d1045 (p : Pattern) : Int := if p 161 then d1044 p else d1042 p
theorem agree1045 (p q : Pattern) (h : Agree support p q) : d1045 p = d1045 q := by
  simp only [d1045, h 161 (by decide), agree1044 p q h, agree1042 p q h]
theorem nonnegative1045 (p : Pattern) : 0 ≤ d1045 p :=
  nonnegative_ite (p 161) (nonnegative1044 p) (nonnegative1042 p)
def d1046 (p : Pattern) : Int := if p 162 then d374 p else d118 p
theorem agree1046 (p q : Pattern) (h : Agree support p q) : d1046 p = d1046 q := by
  simp only [d1046, h 162 (by decide), agree374 p q h, agree118 p q h]
theorem nonnegative1046 (p : Pattern) : 0 ≤ d1046 p :=
  nonnegative_ite (p 162) (nonnegative374 p) (nonnegative118 p)
def d1047 (p : Pattern) : Int := if p 162 then d12 p else d126 p
theorem agree1047 (p q : Pattern) (h : Agree support p q) : d1047 p = d1047 q := by
  simp only [d1047, h 162 (by decide), agree12 p q h, agree126 p q h]
theorem nonnegative1047 (p : Pattern) : 0 ≤ d1047 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative126 p)
def d1048 (p : Pattern) : Int := if p 161 then d1047 p else d1046 p
theorem agree1048 (p q : Pattern) (h : Agree support p q) : d1048 p = d1048 q := by
  simp only [d1048, h 161 (by decide), agree1047 p q h, agree1046 p q h]
theorem nonnegative1048 (p : Pattern) : 0 ≤ d1048 p :=
  nonnegative_ite (p 161) (nonnegative1047 p) (nonnegative1046 p)
def d1049 (p : Pattern) : Int := if p 160 then d1048 p else d1045 p
theorem agree1049 (p q : Pattern) (h : Agree support p q) : d1049 p = d1049 q := by
  simp only [d1049, h 160 (by decide), agree1048 p q h, agree1045 p q h]
theorem nonnegative1049 (p : Pattern) : 0 ≤ d1049 p :=
  nonnegative_ite (p 160) (nonnegative1048 p) (nonnegative1045 p)
def d1050 (p : Pattern) : Int := if p 162 then d386 p else d133 p
theorem agree1050 (p q : Pattern) (h : Agree support p q) : d1050 p = d1050 q := by
  simp only [d1050, h 162 (by decide), agree386 p q h, agree133 p q h]
theorem nonnegative1050 (p : Pattern) : 0 ≤ d1050 p :=
  nonnegative_ite (p 162) (nonnegative386 p) (nonnegative133 p)
def d1051 (p : Pattern) : Int := if p 162 then d12 p else d862 p
theorem agree1051 (p q : Pattern) (h : Agree support p q) : d1051 p = d1051 q := by
  simp only [d1051, h 162 (by decide), agree12 p q h, agree862 p q h]
theorem nonnegative1051 (p : Pattern) : 0 ≤ d1051 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative862 p)
def d1052 (p : Pattern) : Int := if p 161 then d1051 p else d1050 p
theorem agree1052 (p q : Pattern) (h : Agree support p q) : d1052 p = d1052 q := by
  simp only [d1052, h 161 (by decide), agree1051 p q h, agree1050 p q h]
theorem nonnegative1052 (p : Pattern) : 0 ≤ d1052 p :=
  nonnegative_ite (p 161) (nonnegative1051 p) (nonnegative1050 p)
def d1053 (p : Pattern) : Int := if p 163 then d229 p else d139 p
theorem agree1053 (p q : Pattern) (h : Agree support p q) : d1053 p = d1053 q := by
  simp only [d1053, h 163 (by decide), agree229 p q h, agree139 p q h]
theorem nonnegative1053 (p : Pattern) : 0 ≤ d1053 p :=
  nonnegative_ite (p 163) (nonnegative229 p) (nonnegative139 p)
def d1054 (p : Pattern) : Int := if p 162 then d12 p else d1053 p
theorem agree1054 (p q : Pattern) (h : Agree support p q) : d1054 p = d1054 q := by
  simp only [d1054, h 162 (by decide), agree12 p q h, agree1053 p q h]
theorem nonnegative1054 (p : Pattern) : 0 ≤ d1054 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative1053 p)
def d1055 (p : Pattern) : Int := if p 161 then d1054 p else d1051 p
theorem agree1055 (p q : Pattern) (h : Agree support p q) : d1055 p = d1055 q := by
  simp only [d1055, h 161 (by decide), agree1054 p q h, agree1051 p q h]
theorem nonnegative1055 (p : Pattern) : 0 ≤ d1055 p :=
  nonnegative_ite (p 161) (nonnegative1054 p) (nonnegative1051 p)
def d1056 (p : Pattern) : Int := if p 160 then d1055 p else d1052 p
theorem agree1056 (p q : Pattern) (h : Agree support p q) : d1056 p = d1056 q := by
  simp only [d1056, h 160 (by decide), agree1055 p q h, agree1052 p q h]
theorem nonnegative1056 (p : Pattern) : 0 ≤ d1056 p :=
  nonnegative_ite (p 160) (nonnegative1055 p) (nonnegative1052 p)
def d1057 (p : Pattern) : Int := if p 141 then d1056 p else d1049 p
theorem agree1057 (p q : Pattern) (h : Agree support p q) : d1057 p = d1057 q := by
  simp only [d1057, h 141 (by decide), agree1056 p q h, agree1049 p q h]
theorem nonnegative1057 (p : Pattern) : 0 ≤ d1057 p :=
  nonnegative_ite (p 141) (nonnegative1056 p) (nonnegative1049 p)
def d1058 (p : Pattern) : Int := if p 162 then d371 p else d105 p
theorem agree1058 (p q : Pattern) (h : Agree support p q) : d1058 p = d1058 q := by
  simp only [d1058, h 162 (by decide), agree371 p q h, agree105 p q h]
theorem nonnegative1058 (p : Pattern) : 0 ≤ d1058 p :=
  nonnegative_ite (p 162) (nonnegative371 p) (nonnegative105 p)
def d1059 (p : Pattern) : Int := if p 162 then d12 p else d133 p
theorem agree1059 (p q : Pattern) (h : Agree support p q) : d1059 p = d1059 q := by
  simp only [d1059, h 162 (by decide), agree12 p q h, agree133 p q h]
theorem nonnegative1059 (p : Pattern) : 0 ≤ d1059 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative133 p)
def d1060 (p : Pattern) : Int := if p 161 then d1059 p else d1058 p
theorem agree1060 (p q : Pattern) (h : Agree support p q) : d1060 p = d1060 q := by
  simp only [d1060, h 161 (by decide), agree1059 p q h, agree1058 p q h]
theorem nonnegative1060 (p : Pattern) : 0 ≤ d1060 p :=
  nonnegative_ite (p 161) (nonnegative1059 p) (nonnegative1058 p)
def d1061 (p : Pattern) : Int := if p 162 then d12 p else d132 p
theorem agree1061 (p q : Pattern) (h : Agree support p q) : d1061 p = d1061 q := by
  simp only [d1061, h 162 (by decide), agree12 p q h, agree132 p q h]
theorem nonnegative1061 (p : Pattern) : 0 ≤ d1061 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative132 p)
def d1062 (p : Pattern) : Int := if p 161 then d12 p else d1061 p
theorem agree1062 (p q : Pattern) (h : Agree support p q) : d1062 p = d1062 q := by
  simp only [d1062, h 161 (by decide), agree12 p q h, agree1061 p q h]
theorem nonnegative1062 (p : Pattern) : 0 ≤ d1062 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1061 p)
def d1063 (p : Pattern) : Int := if p 160 then d1062 p else d1060 p
theorem agree1063 (p q : Pattern) (h : Agree support p q) : d1063 p = d1063 q := by
  simp only [d1063, h 160 (by decide), agree1062 p q h, agree1060 p q h]
theorem nonnegative1063 (p : Pattern) : 0 ≤ d1063 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative1060 p)
def d1064 (p : Pattern) : Int := if p 162 then d12 p else d873 p
theorem agree1064 (p q : Pattern) (h : Agree support p q) : d1064 p = d1064 q := by
  simp only [d1064, h 162 (by decide), agree12 p q h, agree873 p q h]
theorem nonnegative1064 (p : Pattern) : 0 ≤ d1064 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative873 p)
def d1065 (p : Pattern) : Int := if p 161 then d1064 p else d1059 p
theorem agree1065 (p q : Pattern) (h : Agree support p q) : d1065 p = d1065 q := by
  simp only [d1065, h 161 (by decide), agree1064 p q h, agree1059 p q h]
theorem nonnegative1065 (p : Pattern) : 0 ≤ d1065 p :=
  nonnegative_ite (p 161) (nonnegative1064 p) (nonnegative1059 p)
def d1066 (p : Pattern) : Int := if p 161 then d12 p else d1064 p
theorem agree1066 (p q : Pattern) (h : Agree support p q) : d1066 p = d1066 q := by
  simp only [d1066, h 161 (by decide), agree12 p q h, agree1064 p q h]
theorem nonnegative1066 (p : Pattern) : 0 ≤ d1066 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative1064 p)
def d1067 (p : Pattern) : Int := if p 160 then d1066 p else d1065 p
theorem agree1067 (p q : Pattern) (h : Agree support p q) : d1067 p = d1067 q := by
  simp only [d1067, h 160 (by decide), agree1066 p q h, agree1065 p q h]
theorem nonnegative1067 (p : Pattern) : 0 ≤ d1067 p :=
  nonnegative_ite (p 160) (nonnegative1066 p) (nonnegative1065 p)
def d1068 (p : Pattern) : Int := if p 141 then d1067 p else d1063 p
theorem agree1068 (p q : Pattern) (h : Agree support p q) : d1068 p = d1068 q := by
  simp only [d1068, h 141 (by decide), agree1067 p q h, agree1063 p q h]
theorem nonnegative1068 (p : Pattern) : 0 ≤ d1068 p :=
  nonnegative_ite (p 141) (nonnegative1067 p) (nonnegative1063 p)
def d1069 (p : Pattern) : Int := if p 138 then d1068 p else d1057 p
theorem agree1069 (p q : Pattern) (h : Agree support p q) : d1069 p = d1069 q := by
  simp only [d1069, h 138 (by decide), agree1068 p q h, agree1057 p q h]
theorem nonnegative1069 (p : Pattern) : 0 ≤ d1069 p :=
  nonnegative_ite (p 138) (nonnegative1068 p) (nonnegative1057 p)
def d1070 (p : Pattern) : Int := if p 162 then d361 p else d105 p
theorem agree1070 (p q : Pattern) (h : Agree support p q) : d1070 p = d1070 q := by
  simp only [d1070, h 162 (by decide), agree361 p q h, agree105 p q h]
theorem nonnegative1070 (p : Pattern) : 0 ≤ d1070 p :=
  nonnegative_ite (p 162) (nonnegative361 p) (nonnegative105 p)
def d1071 (p : Pattern) : Int := if p 161 then d1059 p else d1070 p
theorem agree1071 (p q : Pattern) (h : Agree support p q) : d1071 p = d1071 q := by
  simp only [d1071, h 161 (by decide), agree1059 p q h, agree1070 p q h]
theorem nonnegative1071 (p : Pattern) : 0 ≤ d1071 p :=
  nonnegative_ite (p 161) (nonnegative1059 p) (nonnegative1070 p)
def d1072 (p : Pattern) : Int := if p 160 then d1062 p else d1071 p
theorem agree1072 (p q : Pattern) (h : Agree support p q) : d1072 p = d1072 q := by
  simp only [d1072, h 160 (by decide), agree1062 p q h, agree1071 p q h]
theorem nonnegative1072 (p : Pattern) : 0 ≤ d1072 p :=
  nonnegative_ite (p 160) (nonnegative1062 p) (nonnegative1071 p)
def d1073 (p : Pattern) : Int := if p 162 then d374 p else d133 p
theorem agree1073 (p q : Pattern) (h : Agree support p q) : d1073 p = d1073 q := by
  simp only [d1073, h 162 (by decide), agree374 p q h, agree133 p q h]
theorem nonnegative1073 (p : Pattern) : 0 ≤ d1073 p :=
  nonnegative_ite (p 162) (nonnegative374 p) (nonnegative133 p)
def d1074 (p : Pattern) : Int := if p 161 then d1064 p else d1073 p
theorem agree1074 (p q : Pattern) (h : Agree support p q) : d1074 p = d1074 q := by
  simp only [d1074, h 161 (by decide), agree1064 p q h, agree1073 p q h]
theorem nonnegative1074 (p : Pattern) : 0 ≤ d1074 p :=
  nonnegative_ite (p 161) (nonnegative1064 p) (nonnegative1073 p)
def d1075 (p : Pattern) : Int := if p 160 then d1066 p else d1074 p
theorem agree1075 (p q : Pattern) (h : Agree support p q) : d1075 p = d1075 q := by
  simp only [d1075, h 160 (by decide), agree1066 p q h, agree1074 p q h]
theorem nonnegative1075 (p : Pattern) : 0 ≤ d1075 p :=
  nonnegative_ite (p 160) (nonnegative1066 p) (nonnegative1074 p)
def d1076 (p : Pattern) : Int := if p 141 then d1075 p else d1072 p
theorem agree1076 (p q : Pattern) (h : Agree support p q) : d1076 p = d1076 q := by
  simp only [d1076, h 141 (by decide), agree1075 p q h, agree1072 p q h]
theorem nonnegative1076 (p : Pattern) : 0 ≤ d1076 p :=
  nonnegative_ite (p 141) (nonnegative1075 p) (nonnegative1072 p)
def d1077 (p : Pattern) : Int := if p 138 then d162 p else d1076 p
theorem agree1077 (p q : Pattern) (h : Agree support p q) : d1077 p = d1077 q := by
  simp only [d1077, h 138 (by decide), agree162 p q h, agree1076 p q h]
theorem nonnegative1077 (p : Pattern) : 0 ≤ d1077 p :=
  nonnegative_ite (p 138) (nonnegative162 p) (nonnegative1076 p)
def d1078 (p : Pattern) : Int := if p 116 then d1077 p else d1069 p
theorem agree1078 (p q : Pattern) (h : Agree support p q) : d1078 p = d1078 q := by
  simp only [d1078, h 116 (by decide), agree1077 p q h, agree1069 p q h]
theorem nonnegative1078 (p : Pattern) : 0 ≤ d1078 p :=
  nonnegative_ite (p 116) (nonnegative1077 p) (nonnegative1069 p)
def d1079 (p : Pattern) : Int := if p 162 then d389 p else d105 p
theorem agree1079 (p q : Pattern) (h : Agree support p q) : d1079 p = d1079 q := by
  simp only [d1079, h 162 (by decide), agree389 p q h, agree105 p q h]
theorem nonnegative1079 (p : Pattern) : 0 ≤ d1079 p :=
  nonnegative_ite (p 162) (nonnegative389 p) (nonnegative105 p)
end NetHack.Sokoban22Refined85
