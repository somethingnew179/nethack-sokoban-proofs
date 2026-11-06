/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes57
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d6960 (p : Pattern) : Int := if p 163 then d6959 p else d6941 p
theorem agree6960 (p q : Pattern) (h : Agree support p q) : d6960 p = d6960 q := by
  simp only [d6960, h 163 (by decide), agree6959 p q h, agree6941 p q h]
theorem nonnegative6960 (p : Pattern) : 0 ≤ d6960 p :=
  nonnegative_ite (p 163) (nonnegative6959 p) (nonnegative6941 p)
def d6961 (p : Pattern) : Int := if p 225 then d6763 p else d6728 p
theorem agree6961 (p q : Pattern) (h : Agree support p q) : d6961 p = d6961 q := by
  simp only [d6961, h 225 (by decide), agree6763 p q h, agree6728 p q h]
theorem nonnegative6961 (p : Pattern) : 0 ≤ d6961 p :=
  nonnegative_ite (p 225) (nonnegative6763 p) (nonnegative6728 p)
def d6962 (p : Pattern) : Int := if p 224 then d6961 p else d6764 p
theorem agree6962 (p q : Pattern) (h : Agree support p q) : d6962 p = d6962 q := by
  simp only [d6962, h 224 (by decide), agree6961 p q h, agree6764 p q h]
theorem nonnegative6962 (p : Pattern) : 0 ≤ d6962 p :=
  nonnegative_ite (p 224) (nonnegative6961 p) (nonnegative6764 p)
def d6963 (p : Pattern) : Int := if p 204 then d6962 p else d5 p
theorem agree6963 (p q : Pattern) (h : Agree support p q) : d6963 p = d6963 q := by
  simp only [d6963, h 204 (by decide), agree6962 p q h, agree5 p q h]
theorem nonnegative6963 (p : Pattern) : 0 ≤ d6963 p :=
  nonnegative_ite (p 204) (nonnegative6962 p) (nonnegative5 p)
def d6964 (p : Pattern) : Int := if p 204 then d12 p else d6730 p
theorem agree6964 (p q : Pattern) (h : Agree support p q) : d6964 p = d6964 q := by
  simp only [d6964, h 204 (by decide), agree12 p q h, agree6730 p q h]
theorem nonnegative6964 (p : Pattern) : 0 ≤ d6964 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6730 p)
def d6965 (p : Pattern) : Int := if p 182 then d6964 p else d6963 p
theorem agree6965 (p q : Pattern) (h : Agree support p q) : d6965 p = d6965 q := by
  simp only [d6965, h 182 (by decide), agree6964 p q h, agree6963 p q h]
theorem nonnegative6965 (p : Pattern) : 0 ≤ d6965 p :=
  nonnegative_ite (p 182) (nonnegative6964 p) (nonnegative6963 p)
def d6966 (p : Pattern) : Int := if p 163 then d12 p else d6965 p
theorem agree6966 (p q : Pattern) (h : Agree support p q) : d6966 p = d6966 q := by
  simp only [d6966, h 163 (by decide), agree12 p q h, agree6965 p q h]
theorem nonnegative6966 (p : Pattern) : 0 ≤ d6966 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6965 p)
def d6967 (p : Pattern) : Int := if p 162 then d6966 p else d6960 p
theorem agree6967 (p q : Pattern) (h : Agree support p q) : d6967 p = d6967 q := by
  simp only [d6967, h 162 (by decide), agree6966 p q h, agree6960 p q h]
theorem nonnegative6967 (p : Pattern) : 0 ≤ d6967 p :=
  nonnegative_ite (p 162) (nonnegative6966 p) (nonnegative6960 p)
def d6968 (p : Pattern) : Int := if p 204 then d12 p else d6962 p
theorem agree6968 (p q : Pattern) (h : Agree support p q) : d6968 p = d6968 q := by
  simp only [d6968, h 204 (by decide), agree12 p q h, agree6962 p q h]
theorem nonnegative6968 (p : Pattern) : 0 ≤ d6968 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6962 p)
def d6969 (p : Pattern) : Int := if p 182 then d6968 p else d6767 p
theorem agree6969 (p q : Pattern) (h : Agree support p q) : d6969 p = d6969 q := by
  simp only [d6969, h 182 (by decide), agree6968 p q h, agree6767 p q h]
theorem nonnegative6969 (p : Pattern) : 0 ≤ d6969 p :=
  nonnegative_ite (p 182) (nonnegative6968 p) (nonnegative6767 p)
def d6970 (p : Pattern) : Int := if p 163 then d12 p else d6969 p
theorem agree6970 (p q : Pattern) (h : Agree support p q) : d6970 p = d6970 q := by
  simp only [d6970, h 163 (by decide), agree12 p q h, agree6969 p q h]
theorem nonnegative6970 (p : Pattern) : 0 ≤ d6970 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative6969 p)
def d6971 (p : Pattern) : Int := if p 162 then d12 p else d6970 p
theorem agree6971 (p q : Pattern) (h : Agree support p q) : d6971 p = d6971 q := by
  simp only [d6971, h 162 (by decide), agree12 p q h, agree6970 p q h]
theorem nonnegative6971 (p : Pattern) : 0 ≤ d6971 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6970 p)
def d6972 (p : Pattern) : Int := if p 161 then d6971 p else d6967 p
theorem agree6972 (p q : Pattern) (h : Agree support p q) : d6972 p = d6972 q := by
  simp only [d6972, h 161 (by decide), agree6971 p q h, agree6967 p q h]
theorem nonnegative6972 (p : Pattern) : 0 ≤ d6972 p :=
  nonnegative_ite (p 161) (nonnegative6971 p) (nonnegative6967 p)
def d6973 (p : Pattern) : Int := if p 182 then d6759 p else d6767 p
theorem agree6973 (p q : Pattern) (h : Agree support p q) : d6973 p = d6973 q := by
  simp only [d6973, h 182 (by decide), agree6759 p q h, agree6767 p q h]
theorem nonnegative6973 (p : Pattern) : 0 ≤ d6973 p :=
  nonnegative_ite (p 182) (nonnegative6759 p) (nonnegative6767 p)
def d6974 (p : Pattern) : Int := if p 163 then d6768 p else d6973 p
theorem agree6974 (p q : Pattern) (h : Agree support p q) : d6974 p = d6974 q := by
  simp only [d6974, h 163 (by decide), agree6768 p q h, agree6973 p q h]
theorem nonnegative6974 (p : Pattern) : 0 ≤ d6974 p :=
  nonnegative_ite (p 163) (nonnegative6768 p) (nonnegative6973 p)
def d6975 (p : Pattern) : Int := if p 162 then d6951 p else d6974 p
theorem agree6975 (p q : Pattern) (h : Agree support p q) : d6975 p = d6975 q := by
  simp only [d6975, h 162 (by decide), agree6951 p q h, agree6974 p q h]
theorem nonnegative6975 (p : Pattern) : 0 ≤ d6975 p :=
  nonnegative_ite (p 162) (nonnegative6951 p) (nonnegative6974 p)
def d6976 (p : Pattern) : Int := if p 162 then d12 p else d6626 p
theorem agree6976 (p q : Pattern) (h : Agree support p q) : d6976 p = d6976 q := by
  simp only [d6976, h 162 (by decide), agree12 p q h, agree6626 p q h]
theorem nonnegative6976 (p : Pattern) : 0 ≤ d6976 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6626 p)
def d6977 (p : Pattern) : Int := if p 161 then d6976 p else d6975 p
theorem agree6977 (p q : Pattern) (h : Agree support p q) : d6977 p = d6977 q := by
  simp only [d6977, h 161 (by decide), agree6976 p q h, agree6975 p q h]
theorem nonnegative6977 (p : Pattern) : 0 ≤ d6977 p :=
  nonnegative_ite (p 161) (nonnegative6976 p) (nonnegative6975 p)
def d6978 (p : Pattern) : Int := if p 160 then d6977 p else d6972 p
theorem agree6978 (p q : Pattern) (h : Agree support p q) : d6978 p = d6978 q := by
  simp only [d6978, h 160 (by decide), agree6977 p q h, agree6972 p q h]
theorem nonnegative6978 (p : Pattern) : 0 ≤ d6978 p :=
  nonnegative_ite (p 160) (nonnegative6977 p) (nonnegative6972 p)
def d6979 (p : Pattern) : Int := if p 141 then d6978 p else d6954 p
theorem agree6979 (p q : Pattern) (h : Agree support p q) : d6979 p = d6979 q := by
  simp only [d6979, h 141 (by decide), agree6978 p q h, agree6954 p q h]
theorem nonnegative6979 (p : Pattern) : 0 ≤ d6979 p :=
  nonnegative_ite (p 141) (nonnegative6978 p) (nonnegative6954 p)
def d6980 (p : Pattern) : Int := if p 163 then d6811 p else d6808 p
theorem agree6980 (p q : Pattern) (h : Agree support p q) : d6980 p = d6980 q := by
  simp only [d6980, h 163 (by decide), agree6811 p q h, agree6808 p q h]
theorem nonnegative6980 (p : Pattern) : 0 ≤ d6980 p :=
  nonnegative_ite (p 163) (nonnegative6811 p) (nonnegative6808 p)
def d6981 (p : Pattern) : Int := if p 163 then d6648 p else d6818 p
theorem agree6981 (p q : Pattern) (h : Agree support p q) : d6981 p = d6981 q := by
  simp only [d6981, h 163 (by decide), agree6648 p q h, agree6818 p q h]
theorem nonnegative6981 (p : Pattern) : 0 ≤ d6981 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6818 p)
def d6982 (p : Pattern) : Int := if p 162 then d6981 p else d6980 p
theorem agree6982 (p q : Pattern) (h : Agree support p q) : d6982 p = d6982 q := by
  simp only [d6982, h 162 (by decide), agree6981 p q h, agree6980 p q h]
theorem nonnegative6982 (p : Pattern) : 0 ≤ d6982 p :=
  nonnegative_ite (p 162) (nonnegative6981 p) (nonnegative6980 p)
def d6983 (p : Pattern) : Int := if p 161 then d6829 p else d6982 p
theorem agree6983 (p q : Pattern) (h : Agree support p q) : d6983 p = d6983 q := by
  simp only [d6983, h 161 (by decide), agree6829 p q h, agree6982 p q h]
theorem nonnegative6983 (p : Pattern) : 0 ≤ d6983 p :=
  nonnegative_ite (p 161) (nonnegative6829 p) (nonnegative6982 p)
def d6984 (p : Pattern) : Int := if p 160 then d6833 p else d6983 p
theorem agree6984 (p q : Pattern) (h : Agree support p q) : d6984 p = d6984 q := by
  simp only [d6984, h 160 (by decide), agree6833 p q h, agree6983 p q h]
theorem nonnegative6984 (p : Pattern) : 0 ≤ d6984 p :=
  nonnegative_ite (p 160) (nonnegative6833 p) (nonnegative6983 p)
def d6985 (p : Pattern) : Int := if p 246 then d11 p else d3 p
theorem agree6985 (p q : Pattern) (h : Agree support p q) : d6985 p = d6985 q := by
  simp only [d6985, h 246 (by decide), agree11 p q h, agree3 p q h]
theorem nonnegative6985 (p : Pattern) : 0 ≤ d6985 p :=
  nonnegative_ite (p 246) (nonnegative11 p) (nonnegative3 p)
def d6986 (p : Pattern) : Int := if p 225 then d6985 p else d6750 p
theorem agree6986 (p q : Pattern) (h : Agree support p q) : d6986 p = d6986 q := by
  simp only [d6986, h 225 (by decide), agree6985 p q h, agree6750 p q h]
theorem nonnegative6986 (p : Pattern) : 0 ≤ d6986 p :=
  nonnegative_ite (p 225) (nonnegative6985 p) (nonnegative6750 p)
def d6987 (p : Pattern) : Int := if p 224 then d6986 p else d6749 p
theorem agree6987 (p q : Pattern) (h : Agree support p q) : d6987 p = d6987 q := by
  simp only [d6987, h 224 (by decide), agree6986 p q h, agree6749 p q h]
theorem nonnegative6987 (p : Pattern) : 0 ≤ d6987 p :=
  nonnegative_ite (p 224) (nonnegative6986 p) (nonnegative6749 p)
def d6988 (p : Pattern) : Int := if p 204 then d12 p else d6987 p
theorem agree6988 (p q : Pattern) (h : Agree support p q) : d6988 p = d6988 q := by
  simp only [d6988, h 204 (by decide), agree12 p q h, agree6987 p q h]
theorem nonnegative6988 (p : Pattern) : 0 ≤ d6988 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative6987 p)
def d6989 (p : Pattern) : Int := if p 182 then d6988 p else d6789 p
theorem agree6989 (p q : Pattern) (h : Agree support p q) : d6989 p = d6989 q := by
  simp only [d6989, h 182 (by decide), agree6988 p q h, agree6789 p q h]
theorem nonnegative6989 (p : Pattern) : 0 ≤ d6989 p :=
  nonnegative_ite (p 182) (nonnegative6988 p) (nonnegative6789 p)
def d6990 (p : Pattern) : Int := if p 163 then d6818 p else d6989 p
theorem agree6990 (p q : Pattern) (h : Agree support p q) : d6990 p = d6990 q := by
  simp only [d6990, h 163 (by decide), agree6818 p q h, agree6989 p q h]
theorem nonnegative6990 (p : Pattern) : 0 ≤ d6990 p :=
  nonnegative_ite (p 163) (nonnegative6818 p) (nonnegative6989 p)
def d6991 (p : Pattern) : Int := if p 162 then d6930 p else d6990 p
theorem agree6991 (p q : Pattern) (h : Agree support p q) : d6991 p = d6991 q := by
  simp only [d6991, h 162 (by decide), agree6930 p q h, agree6990 p q h]
theorem nonnegative6991 (p : Pattern) : 0 ≤ d6991 p :=
  nonnegative_ite (p 162) (nonnegative6930 p) (nonnegative6990 p)
def d6992 (p : Pattern) : Int := if p 161 then d6832 p else d6991 p
theorem agree6992 (p q : Pattern) (h : Agree support p q) : d6992 p = d6992 q := by
  simp only [d6992, h 161 (by decide), agree6832 p q h, agree6991 p q h]
theorem nonnegative6992 (p : Pattern) : 0 ≤ d6992 p :=
  nonnegative_ite (p 161) (nonnegative6832 p) (nonnegative6991 p)
def d6993 (p : Pattern) : Int := if p 162 then d12 p else d6684 p
theorem agree6993 (p q : Pattern) (h : Agree support p q) : d6993 p = d6993 q := by
  simp only [d6993, h 162 (by decide), agree12 p q h, agree6684 p q h]
theorem nonnegative6993 (p : Pattern) : 0 ≤ d6993 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative6684 p)
def d6994 (p : Pattern) : Int := if p 161 then d12 p else d6993 p
theorem agree6994 (p q : Pattern) (h : Agree support p q) : d6994 p = d6994 q := by
  simp only [d6994, h 161 (by decide), agree12 p q h, agree6993 p q h]
theorem nonnegative6994 (p : Pattern) : 0 ≤ d6994 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative6993 p)
def d6995 (p : Pattern) : Int := if p 160 then d6994 p else d6992 p
theorem agree6995 (p q : Pattern) (h : Agree support p q) : d6995 p = d6995 q := by
  simp only [d6995, h 160 (by decide), agree6994 p q h, agree6992 p q h]
theorem nonnegative6995 (p : Pattern) : 0 ≤ d6995 p :=
  nonnegative_ite (p 160) (nonnegative6994 p) (nonnegative6992 p)
def d6996 (p : Pattern) : Int := if p 141 then d6995 p else d6984 p
theorem agree6996 (p q : Pattern) (h : Agree support p q) : d6996 p = d6996 q := by
  simp only [d6996, h 141 (by decide), agree6995 p q h, agree6984 p q h]
theorem nonnegative6996 (p : Pattern) : 0 ≤ d6996 p :=
  nonnegative_ite (p 141) (nonnegative6995 p) (nonnegative6984 p)
def d6997 (p : Pattern) : Int := if p 138 then d6996 p else d6979 p
theorem agree6997 (p q : Pattern) (h : Agree support p q) : d6997 p = d6997 q := by
  simp only [d6997, h 138 (by decide), agree6996 p q h, agree6979 p q h]
theorem nonnegative6997 (p : Pattern) : 0 ≤ d6997 p :=
  nonnegative_ite (p 138) (nonnegative6996 p) (nonnegative6979 p)
def d6998 (p : Pattern) : Int := if p 163 then d6683 p else d6818 p
theorem agree6998 (p q : Pattern) (h : Agree support p q) : d6998 p = d6998 q := by
  simp only [d6998, h 163 (by decide), agree6683 p q h, agree6818 p q h]
theorem nonnegative6998 (p : Pattern) : 0 ≤ d6998 p :=
  nonnegative_ite (p 163) (nonnegative6683 p) (nonnegative6818 p)
def d6999 (p : Pattern) : Int := if p 162 then d6998 p else d6980 p
theorem agree6999 (p q : Pattern) (h : Agree support p q) : d6999 p = d6999 q := by
  simp only [d6999, h 162 (by decide), agree6998 p q h, agree6980 p q h]
theorem nonnegative6999 (p : Pattern) : 0 ≤ d6999 p :=
  nonnegative_ite (p 162) (nonnegative6998 p) (nonnegative6980 p)
def d7000 (p : Pattern) : Int := if p 163 then d6683 p else d6813 p
theorem agree7000 (p q : Pattern) (h : Agree support p q) : d7000 p = d7000 q := by
  simp only [d7000, h 163 (by decide), agree6683 p q h, agree6813 p q h]
theorem nonnegative7000 (p : Pattern) : 0 ≤ d7000 p :=
  nonnegative_ite (p 163) (nonnegative6683 p) (nonnegative6813 p)
def d7001 (p : Pattern) : Int := if p 162 then d12 p else d7000 p
theorem agree7001 (p q : Pattern) (h : Agree support p q) : d7001 p = d7001 q := by
  simp only [d7001, h 162 (by decide), agree12 p q h, agree7000 p q h]
theorem nonnegative7001 (p : Pattern) : 0 ≤ d7001 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7000 p)
def d7002 (p : Pattern) : Int := if p 161 then d7001 p else d6999 p
theorem agree7002 (p q : Pattern) (h : Agree support p q) : d7002 p = d7002 q := by
  simp only [d7002, h 161 (by decide), agree7001 p q h, agree6999 p q h]
theorem nonnegative7002 (p : Pattern) : 0 ≤ d7002 p :=
  nonnegative_ite (p 161) (nonnegative7001 p) (nonnegative6999 p)
def d7003 (p : Pattern) : Int := if p 163 then d6648 p else d6820 p
theorem agree7003 (p q : Pattern) (h : Agree support p q) : d7003 p = d7003 q := by
  simp only [d7003, h 163 (by decide), agree6648 p q h, agree6820 p q h]
theorem nonnegative7003 (p : Pattern) : 0 ≤ d7003 p :=
  nonnegative_ite (p 163) (nonnegative6648 p) (nonnegative6820 p)
def d7004 (p : Pattern) : Int := if p 162 then d12 p else d7003 p
theorem agree7004 (p q : Pattern) (h : Agree support p q) : d7004 p = d7004 q := by
  simp only [d7004, h 162 (by decide), agree12 p q h, agree7003 p q h]
theorem nonnegative7004 (p : Pattern) : 0 ≤ d7004 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7003 p)
def d7005 (p : Pattern) : Int := if p 161 then d12 p else d7004 p
theorem agree7005 (p q : Pattern) (h : Agree support p q) : d7005 p = d7005 q := by
  simp only [d7005, h 161 (by decide), agree12 p q h, agree7004 p q h]
theorem nonnegative7005 (p : Pattern) : 0 ≤ d7005 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7004 p)
def d7006 (p : Pattern) : Int := if p 160 then d7005 p else d7002 p
theorem agree7006 (p q : Pattern) (h : Agree support p q) : d7006 p = d7006 q := by
  simp only [d7006, h 160 (by decide), agree7005 p q h, agree7002 p q h]
theorem nonnegative7006 (p : Pattern) : 0 ≤ d7006 p :=
  nonnegative_ite (p 160) (nonnegative7005 p) (nonnegative7002 p)
def d7007 (p : Pattern) : Int := if p 141 then d6995 p else d7006 p
theorem agree7007 (p q : Pattern) (h : Agree support p q) : d7007 p = d7007 q := by
  simp only [d7007, h 141 (by decide), agree6995 p q h, agree7006 p q h]
theorem nonnegative7007 (p : Pattern) : 0 ≤ d7007 p :=
  nonnegative_ite (p 141) (nonnegative6995 p) (nonnegative7006 p)
def d7008 (p : Pattern) : Int := if p 138 then d12 p else d7007 p
theorem agree7008 (p q : Pattern) (h : Agree support p q) : d7008 p = d7008 q := by
  simp only [d7008, h 138 (by decide), agree12 p q h, agree7007 p q h]
theorem nonnegative7008 (p : Pattern) : 0 ≤ d7008 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7007 p)
def d7009 (p : Pattern) : Int := if p 116 then d7008 p else d6997 p
theorem agree7009 (p q : Pattern) (h : Agree support p q) : d7009 p = d7009 q := by
  simp only [d7009, h 116 (by decide), agree7008 p q h, agree6997 p q h]
theorem nonnegative7009 (p : Pattern) : 0 ≤ d7009 p :=
  nonnegative_ite (p 116) (nonnegative7008 p) (nonnegative6997 p)
def d7010 (p : Pattern) : Int := if p 115 then d7009 p else d6938 p
theorem agree7010 (p q : Pattern) (h : Agree support p q) : d7010 p = d7010 q := by
  simp only [d7010, h 115 (by decide), agree7009 p q h, agree6938 p q h]
theorem nonnegative7010 (p : Pattern) : 0 ≤ d7010 p :=
  nonnegative_ite (p 115) (nonnegative7009 p) (nonnegative6938 p)
def d7011 (p : Pattern) : Int := if p 71 then d7010 p else d6718 p
theorem agree7011 (p q : Pattern) (h : Agree support p q) : d7011 p = d7011 q := by
  simp only [d7011, h 71 (by decide), agree7010 p q h, agree6718 p q h]
theorem nonnegative7011 (p : Pattern) : 0 ≤ d7011 p :=
  nonnegative_ite (p 71) (nonnegative7010 p) (nonnegative6718 p)
def d7012 (p : Pattern) : Int := if p 49 then d7011 p else d6919 p
theorem agree7012 (p q : Pattern) (h : Agree support p q) : d7012 p = d7012 q := by
  simp only [d7012, h 49 (by decide), agree7011 p q h, agree6919 p q h]
theorem nonnegative7012 (p : Pattern) : 0 ≤ d7012 p :=
  nonnegative_ite (p 49) (nonnegative7011 p) (nonnegative6919 p)
def d7013 (p : Pattern) : Int := if p 48 then d7012 p else d6847 p
theorem agree7013 (p q : Pattern) (h : Agree support p q) : d7013 p = d7013 q := by
  simp only [d7013, h 48 (by decide), agree7012 p q h, agree6847 p q h]
theorem nonnegative7013 (p : Pattern) : 0 ≤ d7013 p :=
  nonnegative_ite (p 48) (nonnegative7012 p) (nonnegative6847 p)
def d7014 (p : Pattern) : Int := if p 182 then d12 p else d1772 p
theorem agree7014 (p q : Pattern) (h : Agree support p q) : d7014 p = d7014 q := by
  simp only [d7014, h 182 (by decide), agree12 p q h, agree1772 p q h]
theorem nonnegative7014 (p : Pattern) : 0 ≤ d7014 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1772 p)
def d7015 (p : Pattern) : Int := if p 182 then d12 p else d2012 p
theorem agree7015 (p q : Pattern) (h : Agree support p q) : d7015 p = d7015 q := by
  simp only [d7015, h 182 (by decide), agree12 p q h, agree2012 p q h]
theorem nonnegative7015 (p : Pattern) : 0 ≤ d7015 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2012 p)
def d7016 (p : Pattern) : Int := if p 163 then d7015 p else d7014 p
theorem agree7016 (p q : Pattern) (h : Agree support p q) : d7016 p = d7016 q := by
  simp only [d7016, h 163 (by decide), agree7015 p q h, agree7014 p q h]
theorem nonnegative7016 (p : Pattern) : 0 ≤ d7016 p :=
  nonnegative_ite (p 163) (nonnegative7015 p) (nonnegative7014 p)
def d7017 (p : Pattern) : Int := if p 162 then d7016 p else d7014 p
theorem agree7017 (p q : Pattern) (h : Agree support p q) : d7017 p = d7017 q := by
  simp only [d7017, h 162 (by decide), agree7016 p q h, agree7014 p q h]
theorem nonnegative7017 (p : Pattern) : 0 ≤ d7017 p :=
  nonnegative_ite (p 162) (nonnegative7016 p) (nonnegative7014 p)
def d7018 (p : Pattern) : Int := if p 182 then d12 p else d1803 p
theorem agree7018 (p q : Pattern) (h : Agree support p q) : d7018 p = d7018 q := by
  simp only [d7018, h 182 (by decide), agree12 p q h, agree1803 p q h]
theorem nonnegative7018 (p : Pattern) : 0 ≤ d7018 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1803 p)
def d7019 (p : Pattern) : Int := if p 163 then d12 p else d7018 p
theorem agree7019 (p q : Pattern) (h : Agree support p q) : d7019 p = d7019 q := by
  simp only [d7019, h 163 (by decide), agree12 p q h, agree7018 p q h]
theorem nonnegative7019 (p : Pattern) : 0 ≤ d7019 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7018 p)
def d7020 (p : Pattern) : Int := if p 162 then d7019 p else d7016 p
theorem agree7020 (p q : Pattern) (h : Agree support p q) : d7020 p = d7020 q := by
  simp only [d7020, h 162 (by decide), agree7019 p q h, agree7016 p q h]
theorem nonnegative7020 (p : Pattern) : 0 ≤ d7020 p :=
  nonnegative_ite (p 162) (nonnegative7019 p) (nonnegative7016 p)
def d7021 (p : Pattern) : Int := if p 161 then d7020 p else d7017 p
theorem agree7021 (p q : Pattern) (h : Agree support p q) : d7021 p = d7021 q := by
  simp only [d7021, h 161 (by decide), agree7020 p q h, agree7017 p q h]
theorem nonnegative7021 (p : Pattern) : 0 ≤ d7021 p :=
  nonnegative_ite (p 161) (nonnegative7020 p) (nonnegative7017 p)
def d7022 (p : Pattern) : Int := if p 182 then d12 p else d1788 p
theorem agree7022 (p q : Pattern) (h : Agree support p q) : d7022 p = d7022 q := by
  simp only [d7022, h 182 (by decide), agree12 p q h, agree1788 p q h]
theorem nonnegative7022 (p : Pattern) : 0 ≤ d7022 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1788 p)
def d7023 (p : Pattern) : Int := if p 182 then d12 p else d1797 p
theorem agree7023 (p q : Pattern) (h : Agree support p q) : d7023 p = d7023 q := by
  simp only [d7023, h 182 (by decide), agree12 p q h, agree1797 p q h]
theorem nonnegative7023 (p : Pattern) : 0 ≤ d7023 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1797 p)
def d7024 (p : Pattern) : Int := if p 163 then d7023 p else d7022 p
theorem agree7024 (p q : Pattern) (h : Agree support p q) : d7024 p = d7024 q := by
  simp only [d7024, h 163 (by decide), agree7023 p q h, agree7022 p q h]
theorem nonnegative7024 (p : Pattern) : 0 ≤ d7024 p :=
  nonnegative_ite (p 163) (nonnegative7023 p) (nonnegative7022 p)
def d7025 (p : Pattern) : Int := if p 162 then d7024 p else d7022 p
theorem agree7025 (p q : Pattern) (h : Agree support p q) : d7025 p = d7025 q := by
  simp only [d7025, h 162 (by decide), agree7024 p q h, agree7022 p q h]
theorem nonnegative7025 (p : Pattern) : 0 ≤ d7025 p :=
  nonnegative_ite (p 162) (nonnegative7024 p) (nonnegative7022 p)
def d7026 (p : Pattern) : Int := if p 162 then d7019 p else d7024 p
theorem agree7026 (p q : Pattern) (h : Agree support p q) : d7026 p = d7026 q := by
  simp only [d7026, h 162 (by decide), agree7019 p q h, agree7024 p q h]
theorem nonnegative7026 (p : Pattern) : 0 ≤ d7026 p :=
  nonnegative_ite (p 162) (nonnegative7019 p) (nonnegative7024 p)
def d7027 (p : Pattern) : Int := if p 161 then d7026 p else d7025 p
theorem agree7027 (p q : Pattern) (h : Agree support p q) : d7027 p = d7027 q := by
  simp only [d7027, h 161 (by decide), agree7026 p q h, agree7025 p q h]
theorem nonnegative7027 (p : Pattern) : 0 ≤ d7027 p :=
  nonnegative_ite (p 161) (nonnegative7026 p) (nonnegative7025 p)
def d7028 (p : Pattern) : Int := if p 160 then d7027 p else d7021 p
theorem agree7028 (p q : Pattern) (h : Agree support p q) : d7028 p = d7028 q := by
  simp only [d7028, h 160 (by decide), agree7027 p q h, agree7021 p q h]
theorem nonnegative7028 (p : Pattern) : 0 ≤ d7028 p :=
  nonnegative_ite (p 160) (nonnegative7027 p) (nonnegative7021 p)
def d7029 (p : Pattern) : Int := if p 182 then d12 p else d2030 p
theorem agree7029 (p q : Pattern) (h : Agree support p q) : d7029 p = d7029 q := by
  simp only [d7029, h 182 (by decide), agree12 p q h, agree2030 p q h]
theorem nonnegative7029 (p : Pattern) : 0 ≤ d7029 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2030 p)
def d7030 (p : Pattern) : Int := if p 163 then d7029 p else d7014 p
theorem agree7030 (p q : Pattern) (h : Agree support p q) : d7030 p = d7030 q := by
  simp only [d7030, h 163 (by decide), agree7029 p q h, agree7014 p q h]
theorem nonnegative7030 (p : Pattern) : 0 ≤ d7030 p :=
  nonnegative_ite (p 163) (nonnegative7029 p) (nonnegative7014 p)
def d7031 (p : Pattern) : Int := if p 163 then d7018 p else d7015 p
theorem agree7031 (p q : Pattern) (h : Agree support p q) : d7031 p = d7031 q := by
  simp only [d7031, h 163 (by decide), agree7018 p q h, agree7015 p q h]
theorem nonnegative7031 (p : Pattern) : 0 ≤ d7031 p :=
  nonnegative_ite (p 163) (nonnegative7018 p) (nonnegative7015 p)
def d7032 (p : Pattern) : Int := if p 162 then d7031 p else d7030 p
theorem agree7032 (p q : Pattern) (h : Agree support p q) : d7032 p = d7032 q := by
  simp only [d7032, h 162 (by decide), agree7031 p q h, agree7030 p q h]
theorem nonnegative7032 (p : Pattern) : 0 ≤ d7032 p :=
  nonnegative_ite (p 162) (nonnegative7031 p) (nonnegative7030 p)
def d7033 (p : Pattern) : Int := if p 182 then d12 p else d1752 p
theorem agree7033 (p q : Pattern) (h : Agree support p q) : d7033 p = d7033 q := by
  simp only [d7033, h 182 (by decide), agree12 p q h, agree1752 p q h]
theorem nonnegative7033 (p : Pattern) : 0 ≤ d7033 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1752 p)
def d7034 (p : Pattern) : Int := if p 163 then d7033 p else d7015 p
theorem agree7034 (p q : Pattern) (h : Agree support p q) : d7034 p = d7034 q := by
  simp only [d7034, h 163 (by decide), agree7033 p q h, agree7015 p q h]
theorem nonnegative7034 (p : Pattern) : 0 ≤ d7034 p :=
  nonnegative_ite (p 163) (nonnegative7033 p) (nonnegative7015 p)
def d7035 (p : Pattern) : Int := if p 182 then d12 p else d1729 p
theorem agree7035 (p q : Pattern) (h : Agree support p q) : d7035 p = d7035 q := by
  simp only [d7035, h 182 (by decide), agree12 p q h, agree1729 p q h]
theorem nonnegative7035 (p : Pattern) : 0 ≤ d7035 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1729 p)
def d7036 (p : Pattern) : Int := if p 163 then d12 p else d7035 p
theorem agree7036 (p q : Pattern) (h : Agree support p q) : d7036 p = d7036 q := by
  simp only [d7036, h 163 (by decide), agree12 p q h, agree7035 p q h]
theorem nonnegative7036 (p : Pattern) : 0 ≤ d7036 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7035 p)
def d7037 (p : Pattern) : Int := if p 162 then d7036 p else d7034 p
theorem agree7037 (p q : Pattern) (h : Agree support p q) : d7037 p = d7037 q := by
  simp only [d7037, h 162 (by decide), agree7036 p q h, agree7034 p q h]
theorem nonnegative7037 (p : Pattern) : 0 ≤ d7037 p :=
  nonnegative_ite (p 162) (nonnegative7036 p) (nonnegative7034 p)
def d7038 (p : Pattern) : Int := if p 161 then d7037 p else d7032 p
theorem agree7038 (p q : Pattern) (h : Agree support p q) : d7038 p = d7038 q := by
  simp only [d7038, h 161 (by decide), agree7037 p q h, agree7032 p q h]
theorem nonnegative7038 (p : Pattern) : 0 ≤ d7038 p :=
  nonnegative_ite (p 161) (nonnegative7037 p) (nonnegative7032 p)
def d7039 (p : Pattern) : Int := if p 182 then d12 p else d1717 p
theorem agree7039 (p q : Pattern) (h : Agree support p q) : d7039 p = d7039 q := by
  simp only [d7039, h 182 (by decide), agree12 p q h, agree1717 p q h]
theorem nonnegative7039 (p : Pattern) : 0 ≤ d7039 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1717 p)
def d7040 (p : Pattern) : Int := if p 163 then d7039 p else d7022 p
theorem agree7040 (p q : Pattern) (h : Agree support p q) : d7040 p = d7040 q := by
  simp only [d7040, h 163 (by decide), agree7039 p q h, agree7022 p q h]
theorem nonnegative7040 (p : Pattern) : 0 ≤ d7040 p :=
  nonnegative_ite (p 163) (nonnegative7039 p) (nonnegative7022 p)
def d7041 (p : Pattern) : Int := if p 163 then d7018 p else d7023 p
theorem agree7041 (p q : Pattern) (h : Agree support p q) : d7041 p = d7041 q := by
  simp only [d7041, h 163 (by decide), agree7018 p q h, agree7023 p q h]
theorem nonnegative7041 (p : Pattern) : 0 ≤ d7041 p :=
  nonnegative_ite (p 163) (nonnegative7018 p) (nonnegative7023 p)
def d7042 (p : Pattern) : Int := if p 162 then d7041 p else d7040 p
theorem agree7042 (p q : Pattern) (h : Agree support p q) : d7042 p = d7042 q := by
  simp only [d7042, h 162 (by decide), agree7041 p q h, agree7040 p q h]
theorem nonnegative7042 (p : Pattern) : 0 ≤ d7042 p :=
  nonnegative_ite (p 162) (nonnegative7041 p) (nonnegative7040 p)
def d7043 (p : Pattern) : Int := if p 163 then d7033 p else d7023 p
theorem agree7043 (p q : Pattern) (h : Agree support p q) : d7043 p = d7043 q := by
  simp only [d7043, h 163 (by decide), agree7033 p q h, agree7023 p q h]
theorem nonnegative7043 (p : Pattern) : 0 ≤ d7043 p :=
  nonnegative_ite (p 163) (nonnegative7033 p) (nonnegative7023 p)
def d7044 (p : Pattern) : Int := if p 162 then d7036 p else d7043 p
theorem agree7044 (p q : Pattern) (h : Agree support p q) : d7044 p = d7044 q := by
  simp only [d7044, h 162 (by decide), agree7036 p q h, agree7043 p q h]
theorem nonnegative7044 (p : Pattern) : 0 ≤ d7044 p :=
  nonnegative_ite (p 162) (nonnegative7036 p) (nonnegative7043 p)
def d7045 (p : Pattern) : Int := if p 161 then d7044 p else d7042 p
theorem agree7045 (p q : Pattern) (h : Agree support p q) : d7045 p = d7045 q := by
  simp only [d7045, h 161 (by decide), agree7044 p q h, agree7042 p q h]
theorem nonnegative7045 (p : Pattern) : 0 ≤ d7045 p :=
  nonnegative_ite (p 161) (nonnegative7044 p) (nonnegative7042 p)
def d7046 (p : Pattern) : Int := if p 160 then d7045 p else d7038 p
theorem agree7046 (p q : Pattern) (h : Agree support p q) : d7046 p = d7046 q := by
  simp only [d7046, h 160 (by decide), agree7045 p q h, agree7038 p q h]
theorem nonnegative7046 (p : Pattern) : 0 ≤ d7046 p :=
  nonnegative_ite (p 160) (nonnegative7045 p) (nonnegative7038 p)
def d7047 (p : Pattern) : Int := if p 141 then d7046 p else d7028 p
theorem agree7047 (p q : Pattern) (h : Agree support p q) : d7047 p = d7047 q := by
  simp only [d7047, h 141 (by decide), agree7046 p q h, agree7028 p q h]
theorem nonnegative7047 (p : Pattern) : 0 ≤ d7047 p :=
  nonnegative_ite (p 141) (nonnegative7046 p) (nonnegative7028 p)
def d7048 (p : Pattern) : Int := if p 182 then d12 p else d2048 p
theorem agree7048 (p q : Pattern) (h : Agree support p q) : d7048 p = d7048 q := by
  simp only [d7048, h 182 (by decide), agree12 p q h, agree2048 p q h]
theorem nonnegative7048 (p : Pattern) : 0 ≤ d7048 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2048 p)
def d7049 (p : Pattern) : Int := if p 182 then d12 p else d2054 p
theorem agree7049 (p q : Pattern) (h : Agree support p q) : d7049 p = d7049 q := by
  simp only [d7049, h 182 (by decide), agree12 p q h, agree2054 p q h]
theorem nonnegative7049 (p : Pattern) : 0 ≤ d7049 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2054 p)
def d7050 (p : Pattern) : Int := if p 163 then d7049 p else d7048 p
theorem agree7050 (p q : Pattern) (h : Agree support p q) : d7050 p = d7050 q := by
  simp only [d7050, h 163 (by decide), agree7049 p q h, agree7048 p q h]
theorem nonnegative7050 (p : Pattern) : 0 ≤ d7050 p :=
  nonnegative_ite (p 163) (nonnegative7049 p) (nonnegative7048 p)
def d7051 (p : Pattern) : Int := if p 162 then d7024 p else d7050 p
theorem agree7051 (p q : Pattern) (h : Agree support p q) : d7051 p = d7051 q := by
  simp only [d7051, h 162 (by decide), agree7024 p q h, agree7050 p q h]
theorem nonnegative7051 (p : Pattern) : 0 ≤ d7051 p :=
  nonnegative_ite (p 162) (nonnegative7024 p) (nonnegative7050 p)
def d7052 (p : Pattern) : Int := if p 161 then d7026 p else d7051 p
theorem agree7052 (p q : Pattern) (h : Agree support p q) : d7052 p = d7052 q := by
  simp only [d7052, h 161 (by decide), agree7026 p q h, agree7051 p q h]
theorem nonnegative7052 (p : Pattern) : 0 ≤ d7052 p :=
  nonnegative_ite (p 161) (nonnegative7026 p) (nonnegative7051 p)
def d7053 (p : Pattern) : Int := if p 182 then d12 p else d1724 p
theorem agree7053 (p q : Pattern) (h : Agree support p q) : d7053 p = d7053 q := by
  simp only [d7053, h 182 (by decide), agree12 p q h, agree1724 p q h]
theorem nonnegative7053 (p : Pattern) : 0 ≤ d7053 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative1724 p)
def d7054 (p : Pattern) : Int := if p 163 then d7053 p else d7039 p
theorem agree7054 (p q : Pattern) (h : Agree support p q) : d7054 p = d7054 q := by
  simp only [d7054, h 163 (by decide), agree7053 p q h, agree7039 p q h]
theorem nonnegative7054 (p : Pattern) : 0 ≤ d7054 p :=
  nonnegative_ite (p 163) (nonnegative7053 p) (nonnegative7039 p)
def d7055 (p : Pattern) : Int := if p 162 then d7036 p else d7054 p
theorem agree7055 (p q : Pattern) (h : Agree support p q) : d7055 p = d7055 q := by
  simp only [d7055, h 162 (by decide), agree7036 p q h, agree7054 p q h]
theorem nonnegative7055 (p : Pattern) : 0 ≤ d7055 p :=
  nonnegative_ite (p 162) (nonnegative7036 p) (nonnegative7054 p)
def d7056 (p : Pattern) : Int := if p 161 then d12 p else d7055 p
theorem agree7056 (p q : Pattern) (h : Agree support p q) : d7056 p = d7056 q := by
  simp only [d7056, h 161 (by decide), agree12 p q h, agree7055 p q h]
theorem nonnegative7056 (p : Pattern) : 0 ≤ d7056 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7055 p)
def d7057 (p : Pattern) : Int := if p 160 then d7056 p else d7052 p
theorem agree7057 (p q : Pattern) (h : Agree support p q) : d7057 p = d7057 q := by
  simp only [d7057, h 160 (by decide), agree7056 p q h, agree7052 p q h]
theorem nonnegative7057 (p : Pattern) : 0 ≤ d7057 p :=
  nonnegative_ite (p 160) (nonnegative7056 p) (nonnegative7052 p)
def d7058 (p : Pattern) : Int := if p 163 then d7039 p else d7049 p
theorem agree7058 (p q : Pattern) (h : Agree support p q) : d7058 p = d7058 q := by
  simp only [d7058, h 163 (by decide), agree7039 p q h, agree7049 p q h]
theorem nonnegative7058 (p : Pattern) : 0 ≤ d7058 p :=
  nonnegative_ite (p 163) (nonnegative7039 p) (nonnegative7049 p)
def d7059 (p : Pattern) : Int := if p 162 then d7041 p else d7058 p
theorem agree7059 (p q : Pattern) (h : Agree support p q) : d7059 p = d7059 q := by
  simp only [d7059, h 162 (by decide), agree7041 p q h, agree7058 p q h]
theorem nonnegative7059 (p : Pattern) : 0 ≤ d7059 p :=
  nonnegative_ite (p 162) (nonnegative7041 p) (nonnegative7058 p)
def d7060 (p : Pattern) : Int := if p 161 then d7044 p else d7059 p
theorem agree7060 (p q : Pattern) (h : Agree support p q) : d7060 p = d7060 q := by
  simp only [d7060, h 161 (by decide), agree7044 p q h, agree7059 p q h]
theorem nonnegative7060 (p : Pattern) : 0 ≤ d7060 p :=
  nonnegative_ite (p 161) (nonnegative7044 p) (nonnegative7059 p)
def d7061 (p : Pattern) : Int := if p 163 then d12 p else d7053 p
theorem agree7061 (p q : Pattern) (h : Agree support p q) : d7061 p = d7061 q := by
  simp only [d7061, h 163 (by decide), agree12 p q h, agree7053 p q h]
theorem nonnegative7061 (p : Pattern) : 0 ≤ d7061 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative7053 p)
def d7062 (p : Pattern) : Int := if p 162 then d12 p else d7061 p
theorem agree7062 (p q : Pattern) (h : Agree support p q) : d7062 p = d7062 q := by
  simp only [d7062, h 162 (by decide), agree12 p q h, agree7061 p q h]
theorem nonnegative7062 (p : Pattern) : 0 ≤ d7062 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7061 p)
def d7063 (p : Pattern) : Int := if p 161 then d12 p else d7062 p
theorem agree7063 (p q : Pattern) (h : Agree support p q) : d7063 p = d7063 q := by
  simp only [d7063, h 161 (by decide), agree12 p q h, agree7062 p q h]
theorem nonnegative7063 (p : Pattern) : 0 ≤ d7063 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7062 p)
def d7064 (p : Pattern) : Int := if p 160 then d7063 p else d7060 p
theorem agree7064 (p q : Pattern) (h : Agree support p q) : d7064 p = d7064 q := by
  simp only [d7064, h 160 (by decide), agree7063 p q h, agree7060 p q h]
theorem nonnegative7064 (p : Pattern) : 0 ≤ d7064 p :=
  nonnegative_ite (p 160) (nonnegative7063 p) (nonnegative7060 p)
def d7065 (p : Pattern) : Int := if p 141 then d7064 p else d7057 p
theorem agree7065 (p q : Pattern) (h : Agree support p q) : d7065 p = d7065 q := by
  simp only [d7065, h 141 (by decide), agree7064 p q h, agree7057 p q h]
theorem nonnegative7065 (p : Pattern) : 0 ≤ d7065 p :=
  nonnegative_ite (p 141) (nonnegative7064 p) (nonnegative7057 p)
def d7066 (p : Pattern) : Int := if p 138 then d7065 p else d7047 p
theorem agree7066 (p q : Pattern) (h : Agree support p q) : d7066 p = d7066 q := by
  simp only [d7066, h 138 (by decide), agree7065 p q h, agree7047 p q h]
theorem nonnegative7066 (p : Pattern) : 0 ≤ d7066 p :=
  nonnegative_ite (p 138) (nonnegative7065 p) (nonnegative7047 p)
def d7067 (p : Pattern) : Int := if p 163 then d7035 p else d7018 p
theorem agree7067 (p q : Pattern) (h : Agree support p q) : d7067 p = d7067 q := by
  simp only [d7067, h 163 (by decide), agree7035 p q h, agree7018 p q h]
theorem nonnegative7067 (p : Pattern) : 0 ≤ d7067 p :=
  nonnegative_ite (p 163) (nonnegative7035 p) (nonnegative7018 p)
def d7068 (p : Pattern) : Int := if p 162 then d7036 p else d7067 p
theorem agree7068 (p q : Pattern) (h : Agree support p q) : d7068 p = d7068 q := by
  simp only [d7068, h 162 (by decide), agree7036 p q h, agree7067 p q h]
theorem nonnegative7068 (p : Pattern) : 0 ≤ d7068 p :=
  nonnegative_ite (p 162) (nonnegative7036 p) (nonnegative7067 p)
def d7069 (p : Pattern) : Int := if p 162 then d12 p else d7036 p
theorem agree7069 (p q : Pattern) (h : Agree support p q) : d7069 p = d7069 q := by
  simp only [d7069, h 162 (by decide), agree12 p q h, agree7036 p q h]
theorem nonnegative7069 (p : Pattern) : 0 ≤ d7069 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7036 p)
def d7070 (p : Pattern) : Int := if p 161 then d7069 p else d7068 p
theorem agree7070 (p q : Pattern) (h : Agree support p q) : d7070 p = d7070 q := by
  simp only [d7070, h 161 (by decide), agree7069 p q h, agree7068 p q h]
theorem nonnegative7070 (p : Pattern) : 0 ≤ d7070 p :=
  nonnegative_ite (p 161) (nonnegative7069 p) (nonnegative7068 p)
def d7071 (p : Pattern) : Int := if p 161 then d12 p else d7069 p
theorem agree7071 (p q : Pattern) (h : Agree support p q) : d7071 p = d7071 q := by
  simp only [d7071, h 161 (by decide), agree12 p q h, agree7069 p q h]
theorem nonnegative7071 (p : Pattern) : 0 ≤ d7071 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative7069 p)
def d7072 (p : Pattern) : Int := if p 160 then d7071 p else d7070 p
theorem agree7072 (p q : Pattern) (h : Agree support p q) : d7072 p = d7072 q := by
  simp only [d7072, h 160 (by decide), agree7071 p q h, agree7070 p q h]
theorem nonnegative7072 (p : Pattern) : 0 ≤ d7072 p :=
  nonnegative_ite (p 160) (nonnegative7071 p) (nonnegative7070 p)
def d7073 (p : Pattern) : Int := if p 160 then d12 p else d7071 p
theorem agree7073 (p q : Pattern) (h : Agree support p q) : d7073 p = d7073 q := by
  simp only [d7073, h 160 (by decide), agree12 p q h, agree7071 p q h]
theorem nonnegative7073 (p : Pattern) : 0 ≤ d7073 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative7071 p)
def d7074 (p : Pattern) : Int := if p 141 then d7073 p else d7072 p
theorem agree7074 (p q : Pattern) (h : Agree support p q) : d7074 p = d7074 q := by
  simp only [d7074, h 141 (by decide), agree7073 p q h, agree7072 p q h]
theorem nonnegative7074 (p : Pattern) : 0 ≤ d7074 p :=
  nonnegative_ite (p 141) (nonnegative7073 p) (nonnegative7072 p)
def d7075 (p : Pattern) : Int := if p 138 then d7074 p else d7065 p
theorem agree7075 (p q : Pattern) (h : Agree support p q) : d7075 p = d7075 q := by
  simp only [d7075, h 138 (by decide), agree7074 p q h, agree7065 p q h]
theorem nonnegative7075 (p : Pattern) : 0 ≤ d7075 p :=
  nonnegative_ite (p 138) (nonnegative7074 p) (nonnegative7065 p)
def d7076 (p : Pattern) : Int := if p 116 then d7075 p else d7066 p
theorem agree7076 (p q : Pattern) (h : Agree support p q) : d7076 p = d7076 q := by
  simp only [d7076, h 116 (by decide), agree7075 p q h, agree7066 p q h]
theorem nonnegative7076 (p : Pattern) : 0 ≤ d7076 p :=
  nonnegative_ite (p 116) (nonnegative7075 p) (nonnegative7066 p)
def d7077 (p : Pattern) : Int := if p 138 then d12 p else d7065 p
theorem agree7077 (p q : Pattern) (h : Agree support p q) : d7077 p = d7077 q := by
  simp only [d7077, h 138 (by decide), agree12 p q h, agree7065 p q h]
theorem nonnegative7077 (p : Pattern) : 0 ≤ d7077 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative7065 p)
def d7078 (p : Pattern) : Int := if p 116 then d7077 p else d7066 p
theorem agree7078 (p q : Pattern) (h : Agree support p q) : d7078 p = d7078 q := by
  simp only [d7078, h 116 (by decide), agree7077 p q h, agree7066 p q h]
theorem nonnegative7078 (p : Pattern) : 0 ≤ d7078 p :=
  nonnegative_ite (p 116) (nonnegative7077 p) (nonnegative7066 p)
def d7079 (p : Pattern) : Int := if p 115 then d7078 p else d7076 p
theorem agree7079 (p q : Pattern) (h : Agree support p q) : d7079 p = d7079 q := by
  simp only [d7079, h 115 (by decide), agree7078 p q h, agree7076 p q h]
theorem nonnegative7079 (p : Pattern) : 0 ≤ d7079 p :=
  nonnegative_ite (p 115) (nonnegative7078 p) (nonnegative7076 p)
end NetHack.Sokoban22Refined85
