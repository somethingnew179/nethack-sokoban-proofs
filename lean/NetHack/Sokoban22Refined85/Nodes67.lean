/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes66
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d8040 (p : Pattern) : Int := if p 182 then d8039 p else d7841 p
theorem agree8040 (p q : Pattern) (h : Agree support p q) : d8040 p = d8040 q := by
  simp only [d8040, h 182 (by decide), agree8039 p q h, agree7841 p q h]
theorem nonnegative8040 (p : Pattern) : 0 ≤ d8040 p :=
  nonnegative_ite (p 182) (nonnegative8039 p) (nonnegative7841 p)
def d8041 (p : Pattern) : Int := if p 163 then d12 p else d8040 p
theorem agree8041 (p q : Pattern) (h : Agree support p q) : d8041 p = d8041 q := by
  simp only [d8041, h 163 (by decide), agree12 p q h, agree8040 p q h]
theorem nonnegative8041 (p : Pattern) : 0 ≤ d8041 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative8040 p)
def d8042 (p : Pattern) : Int := if p 162 then d12 p else d8041 p
theorem agree8042 (p q : Pattern) (h : Agree support p q) : d8042 p = d8042 q := by
  simp only [d8042, h 162 (by decide), agree12 p q h, agree8041 p q h]
theorem nonnegative8042 (p : Pattern) : 0 ≤ d8042 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative8041 p)
def d8043 (p : Pattern) : Int := if p 161 then d8042 p else d8038 p
theorem agree8043 (p q : Pattern) (h : Agree support p q) : d8043 p = d8043 q := by
  simp only [d8043, h 161 (by decide), agree8042 p q h, agree8038 p q h]
theorem nonnegative8043 (p : Pattern) : 0 ≤ d8043 p :=
  nonnegative_ite (p 161) (nonnegative8042 p) (nonnegative8038 p)
def d8044 (p : Pattern) : Int := if p 182 then d7835 p else d7841 p
theorem agree8044 (p q : Pattern) (h : Agree support p q) : d8044 p = d8044 q := by
  simp only [d8044, h 182 (by decide), agree7835 p q h, agree7841 p q h]
theorem nonnegative8044 (p : Pattern) : 0 ≤ d8044 p :=
  nonnegative_ite (p 182) (nonnegative7835 p) (nonnegative7841 p)
def d8045 (p : Pattern) : Int := if p 163 then d7842 p else d8044 p
theorem agree8045 (p q : Pattern) (h : Agree support p q) : d8045 p = d8045 q := by
  simp only [d8045, h 163 (by decide), agree7842 p q h, agree8044 p q h]
theorem nonnegative8045 (p : Pattern) : 0 ≤ d8045 p :=
  nonnegative_ite (p 163) (nonnegative7842 p) (nonnegative8044 p)
def d8046 (p : Pattern) : Int := if p 162 then d8023 p else d8045 p
theorem agree8046 (p q : Pattern) (h : Agree support p q) : d8046 p = d8046 q := by
  simp only [d8046, h 162 (by decide), agree8023 p q h, agree8045 p q h]
theorem nonnegative8046 (p : Pattern) : 0 ≤ d8046 p :=
  nonnegative_ite (p 162) (nonnegative8023 p) (nonnegative8045 p)
def d8047 (p : Pattern) : Int := if p 162 then d12 p else d7716 p
theorem agree8047 (p q : Pattern) (h : Agree support p q) : d8047 p = d8047 q := by
  simp only [d8047, h 162 (by decide), agree12 p q h, agree7716 p q h]
theorem nonnegative8047 (p : Pattern) : 0 ≤ d8047 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7716 p)
def d8048 (p : Pattern) : Int := if p 161 then d8047 p else d8046 p
theorem agree8048 (p q : Pattern) (h : Agree support p q) : d8048 p = d8048 q := by
  simp only [d8048, h 161 (by decide), agree8047 p q h, agree8046 p q h]
theorem nonnegative8048 (p : Pattern) : 0 ≤ d8048 p :=
  nonnegative_ite (p 161) (nonnegative8047 p) (nonnegative8046 p)
def d8049 (p : Pattern) : Int := if p 160 then d8048 p else d8043 p
theorem agree8049 (p q : Pattern) (h : Agree support p q) : d8049 p = d8049 q := by
  simp only [d8049, h 160 (by decide), agree8048 p q h, agree8043 p q h]
theorem nonnegative8049 (p : Pattern) : 0 ≤ d8049 p :=
  nonnegative_ite (p 160) (nonnegative8048 p) (nonnegative8043 p)
def d8050 (p : Pattern) : Int := if p 141 then d8049 p else d8026 p
theorem agree8050 (p q : Pattern) (h : Agree support p q) : d8050 p = d8050 q := by
  simp only [d8050, h 141 (by decide), agree8049 p q h, agree8026 p q h]
theorem nonnegative8050 (p : Pattern) : 0 ≤ d8050 p :=
  nonnegative_ite (p 141) (nonnegative8049 p) (nonnegative8026 p)
def d8051 (p : Pattern) : Int := if p 163 then d7883 p else d7880 p
theorem agree8051 (p q : Pattern) (h : Agree support p q) : d8051 p = d8051 q := by
  simp only [d8051, h 163 (by decide), agree7883 p q h, agree7880 p q h]
theorem nonnegative8051 (p : Pattern) : 0 ≤ d8051 p :=
  nonnegative_ite (p 163) (nonnegative7883 p) (nonnegative7880 p)
def d8052 (p : Pattern) : Int := if p 163 then d7736 p else d7890 p
theorem agree8052 (p q : Pattern) (h : Agree support p q) : d8052 p = d8052 q := by
  simp only [d8052, h 163 (by decide), agree7736 p q h, agree7890 p q h]
theorem nonnegative8052 (p : Pattern) : 0 ≤ d8052 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7890 p)
def d8053 (p : Pattern) : Int := if p 162 then d8052 p else d8051 p
theorem agree8053 (p q : Pattern) (h : Agree support p q) : d8053 p = d8053 q := by
  simp only [d8053, h 162 (by decide), agree8052 p q h, agree8051 p q h]
theorem nonnegative8053 (p : Pattern) : 0 ≤ d8053 p :=
  nonnegative_ite (p 162) (nonnegative8052 p) (nonnegative8051 p)
def d8054 (p : Pattern) : Int := if p 161 then d7901 p else d8053 p
theorem agree8054 (p q : Pattern) (h : Agree support p q) : d8054 p = d8054 q := by
  simp only [d8054, h 161 (by decide), agree7901 p q h, agree8053 p q h]
theorem nonnegative8054 (p : Pattern) : 0 ≤ d8054 p :=
  nonnegative_ite (p 161) (nonnegative7901 p) (nonnegative8053 p)
def d8055 (p : Pattern) : Int := if p 160 then d7905 p else d8054 p
theorem agree8055 (p q : Pattern) (h : Agree support p q) : d8055 p = d8055 q := by
  simp only [d8055, h 160 (by decide), agree7905 p q h, agree8054 p q h]
theorem nonnegative8055 (p : Pattern) : 0 ≤ d8055 p :=
  nonnegative_ite (p 160) (nonnegative7905 p) (nonnegative8054 p)
def d8056 (p : Pattern) : Int := if p 225 then d3257 p else d3377 p
theorem agree8056 (p q : Pattern) (h : Agree support p q) : d8056 p = d8056 q := by
  simp only [d8056, h 225 (by decide), agree3257 p q h, agree3377 p q h]
theorem nonnegative8056 (p : Pattern) : 0 ≤ d8056 p :=
  nonnegative_ite (p 225) (nonnegative3257 p) (nonnegative3377 p)
def d8057 (p : Pattern) : Int := if p 224 then d8056 p else d7829 p
theorem agree8057 (p q : Pattern) (h : Agree support p q) : d8057 p = d8057 q := by
  simp only [d8057, h 224 (by decide), agree8056 p q h, agree7829 p q h]
theorem nonnegative8057 (p : Pattern) : 0 ≤ d8057 p :=
  nonnegative_ite (p 224) (nonnegative8056 p) (nonnegative7829 p)
def d8058 (p : Pattern) : Int := if p 204 then d12 p else d8057 p
theorem agree8058 (p q : Pattern) (h : Agree support p q) : d8058 p = d8058 q := by
  simp only [d8058, h 204 (by decide), agree12 p q h, agree8057 p q h]
theorem nonnegative8058 (p : Pattern) : 0 ≤ d8058 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative8057 p)
def d8059 (p : Pattern) : Int := if p 182 then d8058 p else d7862 p
theorem agree8059 (p q : Pattern) (h : Agree support p q) : d8059 p = d8059 q := by
  simp only [d8059, h 182 (by decide), agree8058 p q h, agree7862 p q h]
theorem nonnegative8059 (p : Pattern) : 0 ≤ d8059 p :=
  nonnegative_ite (p 182) (nonnegative8058 p) (nonnegative7862 p)
def d8060 (p : Pattern) : Int := if p 163 then d7890 p else d8059 p
theorem agree8060 (p q : Pattern) (h : Agree support p q) : d8060 p = d8060 q := by
  simp only [d8060, h 163 (by decide), agree7890 p q h, agree8059 p q h]
theorem nonnegative8060 (p : Pattern) : 0 ≤ d8060 p :=
  nonnegative_ite (p 163) (nonnegative7890 p) (nonnegative8059 p)
def d8061 (p : Pattern) : Int := if p 162 then d8002 p else d8060 p
theorem agree8061 (p q : Pattern) (h : Agree support p q) : d8061 p = d8061 q := by
  simp only [d8061, h 162 (by decide), agree8002 p q h, agree8060 p q h]
theorem nonnegative8061 (p : Pattern) : 0 ≤ d8061 p :=
  nonnegative_ite (p 162) (nonnegative8002 p) (nonnegative8060 p)
def d8062 (p : Pattern) : Int := if p 161 then d7904 p else d8061 p
theorem agree8062 (p q : Pattern) (h : Agree support p q) : d8062 p = d8062 q := by
  simp only [d8062, h 161 (by decide), agree7904 p q h, agree8061 p q h]
theorem nonnegative8062 (p : Pattern) : 0 ≤ d8062 p :=
  nonnegative_ite (p 161) (nonnegative7904 p) (nonnegative8061 p)
def d8063 (p : Pattern) : Int := if p 162 then d12 p else d7771 p
theorem agree8063 (p q : Pattern) (h : Agree support p q) : d8063 p = d8063 q := by
  simp only [d8063, h 162 (by decide), agree12 p q h, agree7771 p q h]
theorem nonnegative8063 (p : Pattern) : 0 ≤ d8063 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative7771 p)
def d8064 (p : Pattern) : Int := if p 161 then d12 p else d8063 p
theorem agree8064 (p q : Pattern) (h : Agree support p q) : d8064 p = d8064 q := by
  simp only [d8064, h 161 (by decide), agree12 p q h, agree8063 p q h]
theorem nonnegative8064 (p : Pattern) : 0 ≤ d8064 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative8063 p)
def d8065 (p : Pattern) : Int := if p 160 then d8064 p else d8062 p
theorem agree8065 (p q : Pattern) (h : Agree support p q) : d8065 p = d8065 q := by
  simp only [d8065, h 160 (by decide), agree8064 p q h, agree8062 p q h]
theorem nonnegative8065 (p : Pattern) : 0 ≤ d8065 p :=
  nonnegative_ite (p 160) (nonnegative8064 p) (nonnegative8062 p)
def d8066 (p : Pattern) : Int := if p 141 then d8065 p else d8055 p
theorem agree8066 (p q : Pattern) (h : Agree support p q) : d8066 p = d8066 q := by
  simp only [d8066, h 141 (by decide), agree8065 p q h, agree8055 p q h]
theorem nonnegative8066 (p : Pattern) : 0 ≤ d8066 p :=
  nonnegative_ite (p 141) (nonnegative8065 p) (nonnegative8055 p)
def d8067 (p : Pattern) : Int := if p 138 then d8066 p else d8050 p
theorem agree8067 (p q : Pattern) (h : Agree support p q) : d8067 p = d8067 q := by
  simp only [d8067, h 138 (by decide), agree8066 p q h, agree8050 p q h]
theorem nonnegative8067 (p : Pattern) : 0 ≤ d8067 p :=
  nonnegative_ite (p 138) (nonnegative8066 p) (nonnegative8050 p)
def d8068 (p : Pattern) : Int := if p 163 then d7770 p else d7890 p
theorem agree8068 (p q : Pattern) (h : Agree support p q) : d8068 p = d8068 q := by
  simp only [d8068, h 163 (by decide), agree7770 p q h, agree7890 p q h]
theorem nonnegative8068 (p : Pattern) : 0 ≤ d8068 p :=
  nonnegative_ite (p 163) (nonnegative7770 p) (nonnegative7890 p)
def d8069 (p : Pattern) : Int := if p 162 then d8068 p else d8051 p
theorem agree8069 (p q : Pattern) (h : Agree support p q) : d8069 p = d8069 q := by
  simp only [d8069, h 162 (by decide), agree8068 p q h, agree8051 p q h]
theorem nonnegative8069 (p : Pattern) : 0 ≤ d8069 p :=
  nonnegative_ite (p 162) (nonnegative8068 p) (nonnegative8051 p)
def d8070 (p : Pattern) : Int := if p 163 then d7770 p else d7885 p
theorem agree8070 (p q : Pattern) (h : Agree support p q) : d8070 p = d8070 q := by
  simp only [d8070, h 163 (by decide), agree7770 p q h, agree7885 p q h]
theorem nonnegative8070 (p : Pattern) : 0 ≤ d8070 p :=
  nonnegative_ite (p 163) (nonnegative7770 p) (nonnegative7885 p)
def d8071 (p : Pattern) : Int := if p 162 then d12 p else d8070 p
theorem agree8071 (p q : Pattern) (h : Agree support p q) : d8071 p = d8071 q := by
  simp only [d8071, h 162 (by decide), agree12 p q h, agree8070 p q h]
theorem nonnegative8071 (p : Pattern) : 0 ≤ d8071 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative8070 p)
def d8072 (p : Pattern) : Int := if p 161 then d8071 p else d8069 p
theorem agree8072 (p q : Pattern) (h : Agree support p q) : d8072 p = d8072 q := by
  simp only [d8072, h 161 (by decide), agree8071 p q h, agree8069 p q h]
theorem nonnegative8072 (p : Pattern) : 0 ≤ d8072 p :=
  nonnegative_ite (p 161) (nonnegative8071 p) (nonnegative8069 p)
def d8073 (p : Pattern) : Int := if p 163 then d7736 p else d7892 p
theorem agree8073 (p q : Pattern) (h : Agree support p q) : d8073 p = d8073 q := by
  simp only [d8073, h 163 (by decide), agree7736 p q h, agree7892 p q h]
theorem nonnegative8073 (p : Pattern) : 0 ≤ d8073 p :=
  nonnegative_ite (p 163) (nonnegative7736 p) (nonnegative7892 p)
def d8074 (p : Pattern) : Int := if p 162 then d12 p else d8073 p
theorem agree8074 (p q : Pattern) (h : Agree support p q) : d8074 p = d8074 q := by
  simp only [d8074, h 162 (by decide), agree12 p q h, agree8073 p q h]
theorem nonnegative8074 (p : Pattern) : 0 ≤ d8074 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative8073 p)
def d8075 (p : Pattern) : Int := if p 161 then d12 p else d8074 p
theorem agree8075 (p q : Pattern) (h : Agree support p q) : d8075 p = d8075 q := by
  simp only [d8075, h 161 (by decide), agree12 p q h, agree8074 p q h]
theorem nonnegative8075 (p : Pattern) : 0 ≤ d8075 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative8074 p)
def d8076 (p : Pattern) : Int := if p 160 then d8075 p else d8072 p
theorem agree8076 (p q : Pattern) (h : Agree support p q) : d8076 p = d8076 q := by
  simp only [d8076, h 160 (by decide), agree8075 p q h, agree8072 p q h]
theorem nonnegative8076 (p : Pattern) : 0 ≤ d8076 p :=
  nonnegative_ite (p 160) (nonnegative8075 p) (nonnegative8072 p)
def d8077 (p : Pattern) : Int := if p 141 then d8065 p else d8076 p
theorem agree8077 (p q : Pattern) (h : Agree support p q) : d8077 p = d8077 q := by
  simp only [d8077, h 141 (by decide), agree8065 p q h, agree8076 p q h]
theorem nonnegative8077 (p : Pattern) : 0 ≤ d8077 p :=
  nonnegative_ite (p 141) (nonnegative8065 p) (nonnegative8076 p)
def d8078 (p : Pattern) : Int := if p 138 then d12 p else d8077 p
theorem agree8078 (p q : Pattern) (h : Agree support p q) : d8078 p = d8078 q := by
  simp only [d8078, h 138 (by decide), agree12 p q h, agree8077 p q h]
theorem nonnegative8078 (p : Pattern) : 0 ≤ d8078 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative8077 p)
def d8079 (p : Pattern) : Int := if p 116 then d8078 p else d8067 p
theorem agree8079 (p q : Pattern) (h : Agree support p q) : d8079 p = d8079 q := by
  simp only [d8079, h 116 (by decide), agree8078 p q h, agree8067 p q h]
theorem nonnegative8079 (p : Pattern) : 0 ≤ d8079 p :=
  nonnegative_ite (p 116) (nonnegative8078 p) (nonnegative8067 p)
def d8080 (p : Pattern) : Int := if p 115 then d8079 p else d8010 p
theorem agree8080 (p q : Pattern) (h : Agree support p q) : d8080 p = d8080 q := by
  simp only [d8080, h 115 (by decide), agree8079 p q h, agree8010 p q h]
theorem nonnegative8080 (p : Pattern) : 0 ≤ d8080 p :=
  nonnegative_ite (p 115) (nonnegative8079 p) (nonnegative8010 p)
def d8081 (p : Pattern) : Int := if p 71 then d8080 p else d7805 p
theorem agree8081 (p q : Pattern) (h : Agree support p q) : d8081 p = d8081 q := by
  simp only [d8081, h 71 (by decide), agree8080 p q h, agree7805 p q h]
theorem nonnegative8081 (p : Pattern) : 0 ≤ d8081 p :=
  nonnegative_ite (p 71) (nonnegative8080 p) (nonnegative7805 p)
def d8082 (p : Pattern) : Int := if p 49 then d8081 p else d7991 p
theorem agree8082 (p q : Pattern) (h : Agree support p q) : d8082 p = d8082 q := by
  simp only [d8082, h 49 (by decide), agree8081 p q h, agree7991 p q h]
theorem nonnegative8082 (p : Pattern) : 0 ≤ d8082 p :=
  nonnegative_ite (p 49) (nonnegative8081 p) (nonnegative7991 p)
def d8083 (p : Pattern) : Int := if p 48 then d8082 p else d7919 p
theorem agree8083 (p q : Pattern) (h : Agree support p q) : d8083 p = d8083 q := by
  simp only [d8083, h 48 (by decide), agree8082 p q h, agree7919 p q h]
theorem nonnegative8083 (p : Pattern) : 0 ≤ d8083 p :=
  nonnegative_ite (p 48) (nonnegative8082 p) (nonnegative7919 p)
def d8084 (p : Pattern) : Int := if p 246 then d5843 p else d1 p
theorem agree8084 (p q : Pattern) (h : Agree support p q) : d8084 p = d8084 q := by
  simp only [d8084, h 246 (by decide), agree5843 p q h, agree1 p q h]
theorem nonnegative8084 (p : Pattern) : 0 ≤ d8084 p :=
  nonnegative_ite (p 246) (nonnegative5843 p) (nonnegative1 p)
def d8085 (p : Pattern) : Int := if p 225 then d8084 p else d1 p
theorem agree8085 (p q : Pattern) (h : Agree support p q) : d8085 p = d8085 q := by
  simp only [d8085, h 225 (by decide), agree8084 p q h, agree1 p q h]
theorem nonnegative8085 (p : Pattern) : 0 ≤ d8085 p :=
  nonnegative_ite (p 225) (nonnegative8084 p) (nonnegative1 p)
def d8086 (p : Pattern) : Int := if p 224 then d8085 p else d1 p
theorem agree8086 (p q : Pattern) (h : Agree support p q) : d8086 p = d8086 q := by
  simp only [d8086, h 224 (by decide), agree8085 p q h, agree1 p q h]
theorem nonnegative8086 (p : Pattern) : 0 ≤ d8086 p :=
  nonnegative_ite (p 224) (nonnegative8085 p) (nonnegative1 p)
def d8087 (p : Pattern) : Int := if p 204 then d8086 p else d1 p
theorem agree8087 (p q : Pattern) (h : Agree support p q) : d8087 p = d8087 q := by
  simp only [d8087, h 204 (by decide), agree8086 p q h, agree1 p q h]
theorem nonnegative8087 (p : Pattern) : 0 ≤ d8087 p :=
  nonnegative_ite (p 204) (nonnegative8086 p) (nonnegative1 p)
def d8088 (p : Pattern) : Int := if p 182 then d8087 p else d1 p
theorem agree8088 (p q : Pattern) (h : Agree support p q) : d8088 p = d8088 q := by
  simp only [d8088, h 182 (by decide), agree8087 p q h, agree1 p q h]
theorem nonnegative8088 (p : Pattern) : 0 ≤ d8088 p :=
  nonnegative_ite (p 182) (nonnegative8087 p) (nonnegative1 p)
def d8089 (p : Pattern) : Int := if p 225 then d5847 p else d8084 p
theorem agree8089 (p q : Pattern) (h : Agree support p q) : d8089 p = d8089 q := by
  simp only [d8089, h 225 (by decide), agree5847 p q h, agree8084 p q h]
theorem nonnegative8089 (p : Pattern) : 0 ≤ d8089 p :=
  nonnegative_ite (p 225) (nonnegative5847 p) (nonnegative8084 p)
def d8090 (p : Pattern) : Int := if p 224 then d8089 p else d8085 p
theorem agree8090 (p q : Pattern) (h : Agree support p q) : d8090 p = d8090 q := by
  simp only [d8090, h 224 (by decide), agree8089 p q h, agree8085 p q h]
theorem nonnegative8090 (p : Pattern) : 0 ≤ d8090 p :=
  nonnegative_ite (p 224) (nonnegative8089 p) (nonnegative8085 p)
def d8091 (p : Pattern) : Int := if p 204 then d8090 p else d8086 p
theorem agree8091 (p q : Pattern) (h : Agree support p q) : d8091 p = d8091 q := by
  simp only [d8091, h 204 (by decide), agree8090 p q h, agree8086 p q h]
theorem nonnegative8091 (p : Pattern) : 0 ≤ d8091 p :=
  nonnegative_ite (p 204) (nonnegative8090 p) (nonnegative8086 p)
def d8092 (p : Pattern) : Int := if p 182 then d8091 p else d8087 p
theorem agree8092 (p q : Pattern) (h : Agree support p q) : d8092 p = d8092 q := by
  simp only [d8092, h 182 (by decide), agree8091 p q h, agree8087 p q h]
theorem nonnegative8092 (p : Pattern) : 0 ≤ d8092 p :=
  nonnegative_ite (p 182) (nonnegative8091 p) (nonnegative8087 p)
def d8093 (p : Pattern) : Int := if p 163 then d8092 p else d8088 p
theorem agree8093 (p q : Pattern) (h : Agree support p q) : d8093 p = d8093 q := by
  simp only [d8093, h 163 (by decide), agree8092 p q h, agree8088 p q h]
theorem nonnegative8093 (p : Pattern) : 0 ≤ d8093 p :=
  nonnegative_ite (p 163) (nonnegative8092 p) (nonnegative8088 p)
def d8094 (p : Pattern) : Int := if p 224 then d5854 p else d8089 p
theorem agree8094 (p q : Pattern) (h : Agree support p q) : d8094 p = d8094 q := by
  simp only [d8094, h 224 (by decide), agree5854 p q h, agree8089 p q h]
theorem nonnegative8094 (p : Pattern) : 0 ≤ d8094 p :=
  nonnegative_ite (p 224) (nonnegative5854 p) (nonnegative8089 p)
def d8095 (p : Pattern) : Int := if p 204 then d8094 p else d8090 p
theorem agree8095 (p q : Pattern) (h : Agree support p q) : d8095 p = d8095 q := by
  simp only [d8095, h 204 (by decide), agree8094 p q h, agree8090 p q h]
theorem nonnegative8095 (p : Pattern) : 0 ≤ d8095 p :=
  nonnegative_ite (p 204) (nonnegative8094 p) (nonnegative8090 p)
def d8096 (p : Pattern) : Int := if p 182 then d8095 p else d8091 p
theorem agree8096 (p q : Pattern) (h : Agree support p q) : d8096 p = d8096 q := by
  simp only [d8096, h 182 (by decide), agree8095 p q h, agree8091 p q h]
theorem nonnegative8096 (p : Pattern) : 0 ≤ d8096 p :=
  nonnegative_ite (p 182) (nonnegative8095 p) (nonnegative8091 p)
def d8097 (p : Pattern) : Int := if p 163 then d8096 p else d8092 p
theorem agree8097 (p q : Pattern) (h : Agree support p q) : d8097 p = d8097 q := by
  simp only [d8097, h 163 (by decide), agree8096 p q h, agree8092 p q h]
theorem nonnegative8097 (p : Pattern) : 0 ≤ d8097 p :=
  nonnegative_ite (p 163) (nonnegative8096 p) (nonnegative8092 p)
def d8098 (p : Pattern) : Int := if p 162 then d8097 p else d8093 p
theorem agree8098 (p q : Pattern) (h : Agree support p q) : d8098 p = d8098 q := by
  simp only [d8098, h 162 (by decide), agree8097 p q h, agree8093 p q h]
theorem nonnegative8098 (p : Pattern) : 0 ≤ d8098 p :=
  nonnegative_ite (p 162) (nonnegative8097 p) (nonnegative8093 p)
def d8099 (p : Pattern) : Int := if p 224 then d0 p else d5854 p
theorem agree8099 (p q : Pattern) (h : Agree support p q) : d8099 p = d8099 q := by
  simp only [d8099, h 224 (by decide), agree0 p q h, agree5854 p q h]
theorem nonnegative8099 (p : Pattern) : 0 ≤ d8099 p :=
  nonnegative_ite (p 224) (nonnegative0 p) (nonnegative5854 p)
def d8100 (p : Pattern) : Int := if p 204 then d8099 p else d8094 p
theorem agree8100 (p q : Pattern) (h : Agree support p q) : d8100 p = d8100 q := by
  simp only [d8100, h 204 (by decide), agree8099 p q h, agree8094 p q h]
theorem nonnegative8100 (p : Pattern) : 0 ≤ d8100 p :=
  nonnegative_ite (p 204) (nonnegative8099 p) (nonnegative8094 p)
def d8101 (p : Pattern) : Int := if p 182 then d8100 p else d8095 p
theorem agree8101 (p q : Pattern) (h : Agree support p q) : d8101 p = d8101 q := by
  simp only [d8101, h 182 (by decide), agree8100 p q h, agree8095 p q h]
theorem nonnegative8101 (p : Pattern) : 0 ≤ d8101 p :=
  nonnegative_ite (p 182) (nonnegative8100 p) (nonnegative8095 p)
def d8102 (p : Pattern) : Int := if p 163 then d8101 p else d8096 p
theorem agree8102 (p q : Pattern) (h : Agree support p q) : d8102 p = d8102 q := by
  simp only [d8102, h 163 (by decide), agree8101 p q h, agree8096 p q h]
theorem nonnegative8102 (p : Pattern) : 0 ≤ d8102 p :=
  nonnegative_ite (p 163) (nonnegative8101 p) (nonnegative8096 p)
def d8103 (p : Pattern) : Int := if p 162 then d8102 p else d8097 p
theorem agree8103 (p q : Pattern) (h : Agree support p q) : d8103 p = d8103 q := by
  simp only [d8103, h 162 (by decide), agree8102 p q h, agree8097 p q h]
theorem nonnegative8103 (p : Pattern) : 0 ≤ d8103 p :=
  nonnegative_ite (p 162) (nonnegative8102 p) (nonnegative8097 p)
def d8104 (p : Pattern) : Int := if p 161 then d8103 p else d8098 p
theorem agree8104 (p q : Pattern) (h : Agree support p q) : d8104 p = d8104 q := by
  simp only [d8104, h 161 (by decide), agree8103 p q h, agree8098 p q h]
theorem nonnegative8104 (p : Pattern) : 0 ≤ d8104 p :=
  nonnegative_ite (p 161) (nonnegative8103 p) (nonnegative8098 p)
def d8105 (p : Pattern) : Int := if p 204 then d0 p else d8099 p
theorem agree8105 (p q : Pattern) (h : Agree support p q) : d8105 p = d8105 q := by
  simp only [d8105, h 204 (by decide), agree0 p q h, agree8099 p q h]
theorem nonnegative8105 (p : Pattern) : 0 ≤ d8105 p :=
  nonnegative_ite (p 204) (nonnegative0 p) (nonnegative8099 p)
def d8106 (p : Pattern) : Int := if p 182 then d8105 p else d8100 p
theorem agree8106 (p q : Pattern) (h : Agree support p q) : d8106 p = d8106 q := by
  simp only [d8106, h 182 (by decide), agree8105 p q h, agree8100 p q h]
theorem nonnegative8106 (p : Pattern) : 0 ≤ d8106 p :=
  nonnegative_ite (p 182) (nonnegative8105 p) (nonnegative8100 p)
def d8107 (p : Pattern) : Int := if p 163 then d8106 p else d8101 p
theorem agree8107 (p q : Pattern) (h : Agree support p q) : d8107 p = d8107 q := by
  simp only [d8107, h 163 (by decide), agree8106 p q h, agree8101 p q h]
theorem nonnegative8107 (p : Pattern) : 0 ≤ d8107 p :=
  nonnegative_ite (p 163) (nonnegative8106 p) (nonnegative8101 p)
def d8108 (p : Pattern) : Int := if p 162 then d8107 p else d8102 p
theorem agree8108 (p q : Pattern) (h : Agree support p q) : d8108 p = d8108 q := by
  simp only [d8108, h 162 (by decide), agree8107 p q h, agree8102 p q h]
theorem nonnegative8108 (p : Pattern) : 0 ≤ d8108 p :=
  nonnegative_ite (p 162) (nonnegative8107 p) (nonnegative8102 p)
def d8109 (p : Pattern) : Int := if p 161 then d8108 p else d8103 p
theorem agree8109 (p q : Pattern) (h : Agree support p q) : d8109 p = d8109 q := by
  simp only [d8109, h 161 (by decide), agree8108 p q h, agree8103 p q h]
theorem nonnegative8109 (p : Pattern) : 0 ≤ d8109 p :=
  nonnegative_ite (p 161) (nonnegative8108 p) (nonnegative8103 p)
def d8110 (p : Pattern) : Int := if p 160 then d8109 p else d8104 p
theorem agree8110 (p q : Pattern) (h : Agree support p q) : d8110 p = d8110 q := by
  simp only [d8110, h 160 (by decide), agree8109 p q h, agree8104 p q h]
theorem nonnegative8110 (p : Pattern) : 0 ≤ d8110 p :=
  nonnegative_ite (p 160) (nonnegative8109 p) (nonnegative8104 p)
def d8111 (p : Pattern) : Int := if p 182 then d0 p else d8105 p
theorem agree8111 (p q : Pattern) (h : Agree support p q) : d8111 p = d8111 q := by
  simp only [d8111, h 182 (by decide), agree0 p q h, agree8105 p q h]
theorem nonnegative8111 (p : Pattern) : 0 ≤ d8111 p :=
  nonnegative_ite (p 182) (nonnegative0 p) (nonnegative8105 p)
def d8112 (p : Pattern) : Int := if p 163 then d8111 p else d8106 p
theorem agree8112 (p q : Pattern) (h : Agree support p q) : d8112 p = d8112 q := by
  simp only [d8112, h 163 (by decide), agree8111 p q h, agree8106 p q h]
theorem nonnegative8112 (p : Pattern) : 0 ≤ d8112 p :=
  nonnegative_ite (p 163) (nonnegative8111 p) (nonnegative8106 p)
def d8113 (p : Pattern) : Int := if p 162 then d8112 p else d8107 p
theorem agree8113 (p q : Pattern) (h : Agree support p q) : d8113 p = d8113 q := by
  simp only [d8113, h 162 (by decide), agree8112 p q h, agree8107 p q h]
theorem nonnegative8113 (p : Pattern) : 0 ≤ d8113 p :=
  nonnegative_ite (p 162) (nonnegative8112 p) (nonnegative8107 p)
def d8114 (p : Pattern) : Int := if p 161 then d8113 p else d8108 p
theorem agree8114 (p q : Pattern) (h : Agree support p q) : d8114 p = d8114 q := by
  simp only [d8114, h 161 (by decide), agree8113 p q h, agree8108 p q h]
theorem nonnegative8114 (p : Pattern) : 0 ≤ d8114 p :=
  nonnegative_ite (p 161) (nonnegative8113 p) (nonnegative8108 p)
def d8115 (p : Pattern) : Int := if p 160 then d8114 p else d8109 p
theorem agree8115 (p q : Pattern) (h : Agree support p q) : d8115 p = d8115 q := by
  simp only [d8115, h 160 (by decide), agree8114 p q h, agree8109 p q h]
theorem nonnegative8115 (p : Pattern) : 0 ≤ d8115 p :=
  nonnegative_ite (p 160) (nonnegative8114 p) (nonnegative8109 p)
def d8116 (p : Pattern) : Int := if p 141 then d8115 p else d8110 p
theorem agree8116 (p q : Pattern) (h : Agree support p q) : d8116 p = d8116 q := by
  simp only [d8116, h 141 (by decide), agree8115 p q h, agree8110 p q h]
theorem nonnegative8116 (p : Pattern) : 0 ≤ d8116 p :=
  nonnegative_ite (p 141) (nonnegative8115 p) (nonnegative8110 p)
def d8117 (p : Pattern) : Int := if p 163 then d0 p else d8111 p
theorem agree8117 (p q : Pattern) (h : Agree support p q) : d8117 p = d8117 q := by
  simp only [d8117, h 163 (by decide), agree0 p q h, agree8111 p q h]
theorem nonnegative8117 (p : Pattern) : 0 ≤ d8117 p :=
  nonnegative_ite (p 163) (nonnegative0 p) (nonnegative8111 p)
def d8118 (p : Pattern) : Int := if p 162 then d8117 p else d8112 p
theorem agree8118 (p q : Pattern) (h : Agree support p q) : d8118 p = d8118 q := by
  simp only [d8118, h 162 (by decide), agree8117 p q h, agree8112 p q h]
theorem nonnegative8118 (p : Pattern) : 0 ≤ d8118 p :=
  nonnegative_ite (p 162) (nonnegative8117 p) (nonnegative8112 p)
def d8119 (p : Pattern) : Int := if p 161 then d8118 p else d8113 p
theorem agree8119 (p q : Pattern) (h : Agree support p q) : d8119 p = d8119 q := by
  simp only [d8119, h 161 (by decide), agree8118 p q h, agree8113 p q h]
theorem nonnegative8119 (p : Pattern) : 0 ≤ d8119 p :=
  nonnegative_ite (p 161) (nonnegative8118 p) (nonnegative8113 p)
def d8120 (p : Pattern) : Int := if p 160 then d8119 p else d8114 p
theorem agree8120 (p q : Pattern) (h : Agree support p q) : d8120 p = d8120 q := by
  simp only [d8120, h 160 (by decide), agree8119 p q h, agree8114 p q h]
theorem nonnegative8120 (p : Pattern) : 0 ≤ d8120 p :=
  nonnegative_ite (p 160) (nonnegative8119 p) (nonnegative8114 p)
def d8121 (p : Pattern) : Int := if p 141 then d8120 p else d8115 p
theorem agree8121 (p q : Pattern) (h : Agree support p q) : d8121 p = d8121 q := by
  simp only [d8121, h 141 (by decide), agree8120 p q h, agree8115 p q h]
theorem nonnegative8121 (p : Pattern) : 0 ≤ d8121 p :=
  nonnegative_ite (p 141) (nonnegative8120 p) (nonnegative8115 p)
def d8122 (p : Pattern) : Int := if p 138 then d8121 p else d8116 p
theorem agree8122 (p q : Pattern) (h : Agree support p q) : d8122 p = d8122 q := by
  simp only [d8122, h 138 (by decide), agree8121 p q h, agree8116 p q h]
theorem nonnegative8122 (p : Pattern) : 0 ≤ d8122 p :=
  nonnegative_ite (p 138) (nonnegative8121 p) (nonnegative8116 p)
def d8123 (p : Pattern) : Int := if p 162 then d0 p else d8117 p
theorem agree8123 (p q : Pattern) (h : Agree support p q) : d8123 p = d8123 q := by
  simp only [d8123, h 162 (by decide), agree0 p q h, agree8117 p q h]
theorem nonnegative8123 (p : Pattern) : 0 ≤ d8123 p :=
  nonnegative_ite (p 162) (nonnegative0 p) (nonnegative8117 p)
def d8124 (p : Pattern) : Int := if p 161 then d8123 p else d8118 p
theorem agree8124 (p q : Pattern) (h : Agree support p q) : d8124 p = d8124 q := by
  simp only [d8124, h 161 (by decide), agree8123 p q h, agree8118 p q h]
theorem nonnegative8124 (p : Pattern) : 0 ≤ d8124 p :=
  nonnegative_ite (p 161) (nonnegative8123 p) (nonnegative8118 p)
def d8125 (p : Pattern) : Int := if p 160 then d8124 p else d8119 p
theorem agree8125 (p q : Pattern) (h : Agree support p q) : d8125 p = d8125 q := by
  simp only [d8125, h 160 (by decide), agree8124 p q h, agree8119 p q h]
theorem nonnegative8125 (p : Pattern) : 0 ≤ d8125 p :=
  nonnegative_ite (p 160) (nonnegative8124 p) (nonnegative8119 p)
def d8126 (p : Pattern) : Int := if p 141 then d8125 p else d8120 p
theorem agree8126 (p q : Pattern) (h : Agree support p q) : d8126 p = d8126 q := by
  simp only [d8126, h 141 (by decide), agree8125 p q h, agree8120 p q h]
theorem nonnegative8126 (p : Pattern) : 0 ≤ d8126 p :=
  nonnegative_ite (p 141) (nonnegative8125 p) (nonnegative8120 p)
def d8127 (p : Pattern) : Int := if p 138 then d8126 p else d8121 p
theorem agree8127 (p q : Pattern) (h : Agree support p q) : d8127 p = d8127 q := by
  simp only [d8127, h 138 (by decide), agree8126 p q h, agree8121 p q h]
theorem nonnegative8127 (p : Pattern) : 0 ≤ d8127 p :=
  nonnegative_ite (p 138) (nonnegative8126 p) (nonnegative8121 p)
def d8128 (p : Pattern) : Int := if p 116 then d8127 p else d8122 p
theorem agree8128 (p q : Pattern) (h : Agree support p q) : d8128 p = d8128 q := by
  simp only [d8128, h 116 (by decide), agree8127 p q h, agree8122 p q h]
theorem nonnegative8128 (p : Pattern) : 0 ≤ d8128 p :=
  nonnegative_ite (p 116) (nonnegative8127 p) (nonnegative8122 p)
def d8129 (p : Pattern) : Int := if p 161 then d0 p else d8123 p
theorem agree8129 (p q : Pattern) (h : Agree support p q) : d8129 p = d8129 q := by
  simp only [d8129, h 161 (by decide), agree0 p q h, agree8123 p q h]
theorem nonnegative8129 (p : Pattern) : 0 ≤ d8129 p :=
  nonnegative_ite (p 161) (nonnegative0 p) (nonnegative8123 p)
def d8130 (p : Pattern) : Int := if p 160 then d8129 p else d8124 p
theorem agree8130 (p q : Pattern) (h : Agree support p q) : d8130 p = d8130 q := by
  simp only [d8130, h 160 (by decide), agree8129 p q h, agree8124 p q h]
theorem nonnegative8130 (p : Pattern) : 0 ≤ d8130 p :=
  nonnegative_ite (p 160) (nonnegative8129 p) (nonnegative8124 p)
def d8131 (p : Pattern) : Int := if p 141 then d8130 p else d8125 p
theorem agree8131 (p q : Pattern) (h : Agree support p q) : d8131 p = d8131 q := by
  simp only [d8131, h 141 (by decide), agree8130 p q h, agree8125 p q h]
theorem nonnegative8131 (p : Pattern) : 0 ≤ d8131 p :=
  nonnegative_ite (p 141) (nonnegative8130 p) (nonnegative8125 p)
def d8132 (p : Pattern) : Int := if p 138 then d8131 p else d8126 p
theorem agree8132 (p q : Pattern) (h : Agree support p q) : d8132 p = d8132 q := by
  simp only [d8132, h 138 (by decide), agree8131 p q h, agree8126 p q h]
theorem nonnegative8132 (p : Pattern) : 0 ≤ d8132 p :=
  nonnegative_ite (p 138) (nonnegative8131 p) (nonnegative8126 p)
def d8133 (p : Pattern) : Int := if p 116 then d8132 p else d8127 p
theorem agree8133 (p q : Pattern) (h : Agree support p q) : d8133 p = d8133 q := by
  simp only [d8133, h 116 (by decide), agree8132 p q h, agree8127 p q h]
theorem nonnegative8133 (p : Pattern) : 0 ≤ d8133 p :=
  nonnegative_ite (p 116) (nonnegative8132 p) (nonnegative8127 p)
def d8134 (p : Pattern) : Int := if p 115 then d8133 p else d8128 p
theorem agree8134 (p q : Pattern) (h : Agree support p q) : d8134 p = d8134 q := by
  simp only [d8134, h 115 (by decide), agree8133 p q h, agree8128 p q h]
theorem nonnegative8134 (p : Pattern) : 0 ≤ d8134 p :=
  nonnegative_ite (p 115) (nonnegative8133 p) (nonnegative8128 p)
def d8135 (p : Pattern) : Int := if p 160 then d0 p else d8129 p
theorem agree8135 (p q : Pattern) (h : Agree support p q) : d8135 p = d8135 q := by
  simp only [d8135, h 160 (by decide), agree0 p q h, agree8129 p q h]
theorem nonnegative8135 (p : Pattern) : 0 ≤ d8135 p :=
  nonnegative_ite (p 160) (nonnegative0 p) (nonnegative8129 p)
def d8136 (p : Pattern) : Int := if p 141 then d8135 p else d8130 p
theorem agree8136 (p q : Pattern) (h : Agree support p q) : d8136 p = d8136 q := by
  simp only [d8136, h 141 (by decide), agree8135 p q h, agree8130 p q h]
theorem nonnegative8136 (p : Pattern) : 0 ≤ d8136 p :=
  nonnegative_ite (p 141) (nonnegative8135 p) (nonnegative8130 p)
def d8137 (p : Pattern) : Int := if p 138 then d8136 p else d8131 p
theorem agree8137 (p q : Pattern) (h : Agree support p q) : d8137 p = d8137 q := by
  simp only [d8137, h 138 (by decide), agree8136 p q h, agree8131 p q h]
theorem nonnegative8137 (p : Pattern) : 0 ≤ d8137 p :=
  nonnegative_ite (p 138) (nonnegative8136 p) (nonnegative8131 p)
def d8138 (p : Pattern) : Int := if p 116 then d8137 p else d8132 p
theorem agree8138 (p q : Pattern) (h : Agree support p q) : d8138 p = d8138 q := by
  simp only [d8138, h 116 (by decide), agree8137 p q h, agree8132 p q h]
theorem nonnegative8138 (p : Pattern) : 0 ≤ d8138 p :=
  nonnegative_ite (p 116) (nonnegative8137 p) (nonnegative8132 p)
def d8139 (p : Pattern) : Int := if p 115 then d8138 p else d8133 p
theorem agree8139 (p q : Pattern) (h : Agree support p q) : d8139 p = d8139 q := by
  simp only [d8139, h 115 (by decide), agree8138 p q h, agree8133 p q h]
theorem nonnegative8139 (p : Pattern) : 0 ≤ d8139 p :=
  nonnegative_ite (p 115) (nonnegative8138 p) (nonnegative8133 p)
def d8140 (p : Pattern) : Int := if p 71 then d8139 p else d8134 p
theorem agree8140 (p q : Pattern) (h : Agree support p q) : d8140 p = d8140 q := by
  simp only [d8140, h 71 (by decide), agree8139 p q h, agree8134 p q h]
theorem nonnegative8140 (p : Pattern) : 0 ≤ d8140 p :=
  nonnegative_ite (p 71) (nonnegative8139 p) (nonnegative8134 p)
def d8141 (p : Pattern) : Int := if p 141 then d0 p else d8135 p
theorem agree8141 (p q : Pattern) (h : Agree support p q) : d8141 p = d8141 q := by
  simp only [d8141, h 141 (by decide), agree0 p q h, agree8135 p q h]
theorem nonnegative8141 (p : Pattern) : 0 ≤ d8141 p :=
  nonnegative_ite (p 141) (nonnegative0 p) (nonnegative8135 p)
def d8142 (p : Pattern) : Int := if p 138 then d8141 p else d8136 p
theorem agree8142 (p q : Pattern) (h : Agree support p q) : d8142 p = d8142 q := by
  simp only [d8142, h 138 (by decide), agree8141 p q h, agree8136 p q h]
theorem nonnegative8142 (p : Pattern) : 0 ≤ d8142 p :=
  nonnegative_ite (p 138) (nonnegative8141 p) (nonnegative8136 p)
def d8143 (p : Pattern) : Int := if p 116 then d8142 p else d8137 p
theorem agree8143 (p q : Pattern) (h : Agree support p q) : d8143 p = d8143 q := by
  simp only [d8143, h 116 (by decide), agree8142 p q h, agree8137 p q h]
theorem nonnegative8143 (p : Pattern) : 0 ≤ d8143 p :=
  nonnegative_ite (p 116) (nonnegative8142 p) (nonnegative8137 p)
def d8144 (p : Pattern) : Int := if p 115 then d8143 p else d8138 p
theorem agree8144 (p q : Pattern) (h : Agree support p q) : d8144 p = d8144 q := by
  simp only [d8144, h 115 (by decide), agree8143 p q h, agree8138 p q h]
theorem nonnegative8144 (p : Pattern) : 0 ≤ d8144 p :=
  nonnegative_ite (p 115) (nonnegative8143 p) (nonnegative8138 p)
def d8145 (p : Pattern) : Int := if p 71 then d8144 p else d8139 p
theorem agree8145 (p q : Pattern) (h : Agree support p q) : d8145 p = d8145 q := by
  simp only [d8145, h 71 (by decide), agree8144 p q h, agree8139 p q h]
theorem nonnegative8145 (p : Pattern) : 0 ≤ d8145 p :=
  nonnegative_ite (p 71) (nonnegative8144 p) (nonnegative8139 p)
def d8146 (p : Pattern) : Int := if p 49 then d8145 p else d8140 p
theorem agree8146 (p q : Pattern) (h : Agree support p q) : d8146 p = d8146 q := by
  simp only [d8146, h 49 (by decide), agree8145 p q h, agree8140 p q h]
theorem nonnegative8146 (p : Pattern) : 0 ≤ d8146 p :=
  nonnegative_ite (p 49) (nonnegative8145 p) (nonnegative8140 p)
def d8147 (p : Pattern) : Int := if p 138 then d0 p else d8141 p
theorem agree8147 (p q : Pattern) (h : Agree support p q) : d8147 p = d8147 q := by
  simp only [d8147, h 138 (by decide), agree0 p q h, agree8141 p q h]
theorem nonnegative8147 (p : Pattern) : 0 ≤ d8147 p :=
  nonnegative_ite (p 138) (nonnegative0 p) (nonnegative8141 p)
def d8148 (p : Pattern) : Int := if p 116 then d8147 p else d8142 p
theorem agree8148 (p q : Pattern) (h : Agree support p q) : d8148 p = d8148 q := by
  simp only [d8148, h 116 (by decide), agree8147 p q h, agree8142 p q h]
theorem nonnegative8148 (p : Pattern) : 0 ≤ d8148 p :=
  nonnegative_ite (p 116) (nonnegative8147 p) (nonnegative8142 p)
def d8149 (p : Pattern) : Int := if p 115 then d8148 p else d8143 p
theorem agree8149 (p q : Pattern) (h : Agree support p q) : d8149 p = d8149 q := by
  simp only [d8149, h 115 (by decide), agree8148 p q h, agree8143 p q h]
theorem nonnegative8149 (p : Pattern) : 0 ≤ d8149 p :=
  nonnegative_ite (p 115) (nonnegative8148 p) (nonnegative8143 p)
def d8150 (p : Pattern) : Int := if p 71 then d8149 p else d8144 p
theorem agree8150 (p q : Pattern) (h : Agree support p q) : d8150 p = d8150 q := by
  simp only [d8150, h 71 (by decide), agree8149 p q h, agree8144 p q h]
theorem nonnegative8150 (p : Pattern) : 0 ≤ d8150 p :=
  nonnegative_ite (p 71) (nonnegative8149 p) (nonnegative8144 p)
def d8151 (p : Pattern) : Int := if p 49 then d8150 p else d8145 p
theorem agree8151 (p q : Pattern) (h : Agree support p q) : d8151 p = d8151 q := by
  simp only [d8151, h 49 (by decide), agree8150 p q h, agree8145 p q h]
theorem nonnegative8151 (p : Pattern) : 0 ≤ d8151 p :=
  nonnegative_ite (p 49) (nonnegative8150 p) (nonnegative8145 p)
def d8152 (p : Pattern) : Int := if p 48 then d8151 p else d8146 p
theorem agree8152 (p q : Pattern) (h : Agree support p q) : d8152 p = d8152 q := by
  simp only [d8152, h 48 (by decide), agree8151 p q h, agree8146 p q h]
theorem nonnegative8152 (p : Pattern) : 0 ≤ d8152 p :=
  nonnegative_ite (p 48) (nonnegative8151 p) (nonnegative8146 p)
end NetHack.Sokoban22Refined85
