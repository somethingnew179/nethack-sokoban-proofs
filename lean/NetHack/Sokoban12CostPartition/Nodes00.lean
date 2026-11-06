/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d0 (_p : Pattern) : Int := 0
theorem agree0 (p q : Pattern) (_h : Agree support p q) : d0 p = d0 q := rfl
theorem nonnegative0 (p : Pattern) : 0 ≤ d0 p := by change (0 : Int) ≤ 0; decide
def d1 (_p : Pattern) : Int := 1
theorem agree1 (p q : Pattern) (_h : Agree support p q) : d1 p = d1 q := rfl
theorem nonnegative1 (p : Pattern) : 0 ≤ d1 p := by change (0 : Int) ≤ 1; decide
def d2 (_p : Pattern) : Int := 2
theorem agree2 (p q : Pattern) (_h : Agree support p q) : d2 p = d2 q := rfl
theorem nonnegative2 (p : Pattern) : 0 ≤ d2 p := by change (0 : Int) ≤ 2; decide
def d3 (_p : Pattern) : Int := 3
theorem agree3 (p q : Pattern) (_h : Agree support p q) : d3 p = d3 q := rfl
theorem nonnegative3 (p : Pattern) : 0 ≤ d3 p := by change (0 : Int) ≤ 3; decide
def d4 (_p : Pattern) : Int := 4
theorem agree4 (p q : Pattern) (_h : Agree support p q) : d4 p = d4 q := rfl
theorem nonnegative4 (p : Pattern) : 0 ≤ d4 p := by change (0 : Int) ≤ 4; decide
def d5 (_p : Pattern) : Int := 5
theorem agree5 (p q : Pattern) (_h : Agree support p q) : d5 p = d5 q := rfl
theorem nonnegative5 (p : Pattern) : 0 ≤ d5 p := by change (0 : Int) ≤ 5; decide
def d6 (p : Pattern) : Int := if p 193 then d2 p else d0 p
theorem agree6 (p q : Pattern) (h : Agree support p q) : d6 p = d6 q := by
  simp only [d6, h 193 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative6 (p : Pattern) : 0 ≤ d6 p :=
  nonnegative_ite (p 193) (nonnegative2 p) (nonnegative0 p)
def d7 (p : Pattern) : Int := if p 192 then d6 p else d0 p
theorem agree7 (p q : Pattern) (h : Agree support p q) : d7 p = d7 q := by
  simp only [d7, h 192 (by decide), agree6 p q h, agree0 p q h]
theorem nonnegative7 (p : Pattern) : 0 ≤ d7 p :=
  nonnegative_ite (p 192) (nonnegative6 p) (nonnegative0 p)
def d8 (p : Pattern) : Int := if p 271 then d1 p else d0 p
theorem agree8 (p q : Pattern) (h : Agree support p q) : d8 p = d8 q := by
  simp only [d8, h 271 (by decide), agree1 p q h, agree0 p q h]
theorem nonnegative8 (p : Pattern) : 0 ≤ d8 p :=
  nonnegative_ite (p 271) (nonnegative1 p) (nonnegative0 p)
def d9 (p : Pattern) : Int := if p 271 then d3 p else d2 p
theorem agree9 (p q : Pattern) (h : Agree support p q) : d9 p = d9 q := by
  simp only [d9, h 271 (by decide), agree3 p q h, agree2 p q h]
theorem nonnegative9 (p : Pattern) : 0 ≤ d9 p :=
  nonnegative_ite (p 271) (nonnegative3 p) (nonnegative2 p)
def d10 (p : Pattern) : Int := if p 193 then d9 p else d8 p
theorem agree10 (p q : Pattern) (h : Agree support p q) : d10 p = d10 q := by
  simp only [d10, h 193 (by decide), agree9 p q h, agree8 p q h]
theorem nonnegative10 (p : Pattern) : 0 ≤ d10 p :=
  nonnegative_ite (p 193) (nonnegative9 p) (nonnegative8 p)
def d11 (p : Pattern) : Int := if p 192 then d10 p else d8 p
theorem agree11 (p q : Pattern) (h : Agree support p q) : d11 p = d11 q := by
  simp only [d11, h 192 (by decide), agree10 p q h, agree8 p q h]
theorem nonnegative11 (p : Pattern) : 0 ≤ d11 p :=
  nonnegative_ite (p 192) (nonnegative10 p) (nonnegative8 p)
def d12 (p : Pattern) : Int := if p 168 then d11 p else d7 p
theorem agree12 (p q : Pattern) (h : Agree support p q) : d12 p = d12 q := by
  simp only [d12, h 168 (by decide), agree11 p q h, agree7 p q h]
theorem nonnegative12 (p : Pattern) : 0 ≤ d12 p :=
  nonnegative_ite (p 168) (nonnegative11 p) (nonnegative7 p)
def d13 (p : Pattern) : Int := if p 141 then d12 p else d7 p
theorem agree13 (p q : Pattern) (h : Agree support p q) : d13 p = d13 q := by
  simp only [d13, h 141 (by decide), agree12 p q h, agree7 p q h]
theorem nonnegative13 (p : Pattern) : 0 ≤ d13 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative7 p)
def d14 (p : Pattern) : Int := if p 193 then d9 p else d0 p
theorem agree14 (p q : Pattern) (h : Agree support p q) : d14 p = d14 q := by
  simp only [d14, h 193 (by decide), agree9 p q h, agree0 p q h]
theorem nonnegative14 (p : Pattern) : 0 ≤ d14 p :=
  nonnegative_ite (p 193) (nonnegative9 p) (nonnegative0 p)
def d15 (p : Pattern) : Int := if p 192 then d3 p else d14 p
theorem agree15 (p q : Pattern) (h : Agree support p q) : d15 p = d15 q := by
  simp only [d15, h 192 (by decide), agree3 p q h, agree14 p q h]
theorem nonnegative15 (p : Pattern) : 0 ≤ d15 p :=
  nonnegative_ite (p 192) (nonnegative3 p) (nonnegative14 p)
def d16 (p : Pattern) : Int := if p 271 then d3 p else d0 p
theorem agree16 (p q : Pattern) (h : Agree support p q) : d16 p = d16 q := by
  simp only [d16, h 271 (by decide), agree3 p q h, agree0 p q h]
theorem nonnegative16 (p : Pattern) : 0 ≤ d16 p :=
  nonnegative_ite (p 271) (nonnegative3 p) (nonnegative0 p)
def d17 (p : Pattern) : Int := if p 193 then d3 p else d16 p
theorem agree17 (p q : Pattern) (h : Agree support p q) : d17 p = d17 q := by
  simp only [d17, h 193 (by decide), agree3 p q h, agree16 p q h]
theorem nonnegative17 (p : Pattern) : 0 ≤ d17 p :=
  nonnegative_ite (p 193) (nonnegative3 p) (nonnegative16 p)
def d18 (p : Pattern) : Int := if p 192 then d3 p else d17 p
theorem agree18 (p q : Pattern) (h : Agree support p q) : d18 p = d18 q := by
  simp only [d18, h 192 (by decide), agree3 p q h, agree17 p q h]
theorem nonnegative18 (p : Pattern) : 0 ≤ d18 p :=
  nonnegative_ite (p 192) (nonnegative3 p) (nonnegative17 p)
def d19 (p : Pattern) : Int := if p 168 then d18 p else d15 p
theorem agree19 (p q : Pattern) (h : Agree support p q) : d19 p = d19 q := by
  simp only [d19, h 168 (by decide), agree18 p q h, agree15 p q h]
theorem nonnegative19 (p : Pattern) : 0 ≤ d19 p :=
  nonnegative_ite (p 168) (nonnegative18 p) (nonnegative15 p)
def d20 (p : Pattern) : Int := if p 141 then d19 p else d7 p
theorem agree20 (p q : Pattern) (h : Agree support p q) : d20 p = d20 q := by
  simp only [d20, h 141 (by decide), agree19 p q h, agree7 p q h]
theorem nonnegative20 (p : Pattern) : 0 ≤ d20 p :=
  nonnegative_ite (p 141) (nonnegative19 p) (nonnegative7 p)
def d21 (p : Pattern) : Int := if p 168 then d15 p else d7 p
theorem agree21 (p q : Pattern) (h : Agree support p q) : d21 p = d21 q := by
  simp only [d21, h 168 (by decide), agree15 p q h, agree7 p q h]
theorem nonnegative21 (p : Pattern) : 0 ≤ d21 p :=
  nonnegative_ite (p 168) (nonnegative15 p) (nonnegative7 p)
def d22 (p : Pattern) : Int := if p 168 then d18 p else d7 p
theorem agree22 (p q : Pattern) (h : Agree support p q) : d22 p = d22 q := by
  simp only [d22, h 168 (by decide), agree18 p q h, agree7 p q h]
theorem nonnegative22 (p : Pattern) : 0 ≤ d22 p :=
  nonnegative_ite (p 168) (nonnegative18 p) (nonnegative7 p)
def d23 (p : Pattern) : Int := if p 141 then d22 p else d21 p
theorem agree23 (p q : Pattern) (h : Agree support p q) : d23 p = d23 q := by
  simp only [d23, h 141 (by decide), agree22 p q h, agree21 p q h]
theorem nonnegative23 (p : Pattern) : 0 ≤ d23 p :=
  nonnegative_ite (p 141) (nonnegative22 p) (nonnegative21 p)
def d24 (p : Pattern) : Int := if p 192 then d3 p else d0 p
theorem agree24 (p q : Pattern) (h : Agree support p q) : d24 p = d24 q := by
  simp only [d24, h 192 (by decide), agree3 p q h, agree0 p q h]
theorem nonnegative24 (p : Pattern) : 0 ≤ d24 p :=
  nonnegative_ite (p 192) (nonnegative3 p) (nonnegative0 p)
def d25 (p : Pattern) : Int := if p 192 then d3 p else d8 p
theorem agree25 (p q : Pattern) (h : Agree support p q) : d25 p = d25 q := by
  simp only [d25, h 192 (by decide), agree3 p q h, agree8 p q h]
theorem nonnegative25 (p : Pattern) : 0 ≤ d25 p :=
  nonnegative_ite (p 192) (nonnegative3 p) (nonnegative8 p)
def d26 (p : Pattern) : Int := if p 168 then d25 p else d24 p
theorem agree26 (p q : Pattern) (h : Agree support p q) : d26 p = d26 q := by
  simp only [d26, h 168 (by decide), agree25 p q h, agree24 p q h]
theorem nonnegative26 (p : Pattern) : 0 ≤ d26 p :=
  nonnegative_ite (p 168) (nonnegative25 p) (nonnegative24 p)
def d27 (p : Pattern) : Int := if p 141 then d26 p else d24 p
theorem agree27 (p q : Pattern) (h : Agree support p q) : d27 p = d27 q := by
  simp only [d27, h 141 (by decide), agree26 p q h, agree24 p q h]
theorem nonnegative27 (p : Pattern) : 0 ≤ d27 p :=
  nonnegative_ite (p 141) (nonnegative26 p) (nonnegative24 p)
def d28 (p : Pattern) : Int := if p 193 then d3 p else d0 p
theorem agree28 (p q : Pattern) (h : Agree support p q) : d28 p = d28 q := by
  simp only [d28, h 193 (by decide), agree3 p q h, agree0 p q h]
theorem nonnegative28 (p : Pattern) : 0 ≤ d28 p :=
  nonnegative_ite (p 193) (nonnegative3 p) (nonnegative0 p)
def d29 (p : Pattern) : Int := if p 192 then d28 p else d6 p
theorem agree29 (p q : Pattern) (h : Agree support p q) : d29 p = d29 q := by
  simp only [d29, h 192 (by decide), agree28 p q h, agree6 p q h]
theorem nonnegative29 (p : Pattern) : 0 ≤ d29 p :=
  nonnegative_ite (p 192) (nonnegative28 p) (nonnegative6 p)
def d30 (p : Pattern) : Int := if p 192 then d28 p else d14 p
theorem agree30 (p q : Pattern) (h : Agree support p q) : d30 p = d30 q := by
  simp only [d30, h 192 (by decide), agree28 p q h, agree14 p q h]
theorem nonnegative30 (p : Pattern) : 0 ≤ d30 p :=
  nonnegative_ite (p 192) (nonnegative28 p) (nonnegative14 p)
def d31 (p : Pattern) : Int := if p 168 then d30 p else d29 p
theorem agree31 (p q : Pattern) (h : Agree support p q) : d31 p = d31 q := by
  simp only [d31, h 168 (by decide), agree30 p q h, agree29 p q h]
theorem nonnegative31 (p : Pattern) : 0 ≤ d31 p :=
  nonnegative_ite (p 168) (nonnegative30 p) (nonnegative29 p)
def d32 (p : Pattern) : Int := if p 193 then d3 p else d8 p
theorem agree32 (p q : Pattern) (h : Agree support p q) : d32 p = d32 q := by
  simp only [d32, h 193 (by decide), agree3 p q h, agree8 p q h]
theorem nonnegative32 (p : Pattern) : 0 ≤ d32 p :=
  nonnegative_ite (p 193) (nonnegative3 p) (nonnegative8 p)
def d33 (p : Pattern) : Int := if p 168 then d32 p else d30 p
theorem agree33 (p q : Pattern) (h : Agree support p q) : d33 p = d33 q := by
  simp only [d33, h 168 (by decide), agree32 p q h, agree30 p q h]
theorem nonnegative33 (p : Pattern) : 0 ≤ d33 p :=
  nonnegative_ite (p 168) (nonnegative32 p) (nonnegative30 p)
def d34 (p : Pattern) : Int := if p 141 then d33 p else d31 p
theorem agree34 (p q : Pattern) (h : Agree support p q) : d34 p = d34 q := by
  simp only [d34, h 141 (by decide), agree33 p q h, agree31 p q h]
theorem nonnegative34 (p : Pattern) : 0 ≤ d34 p :=
  nonnegative_ite (p 141) (nonnegative33 p) (nonnegative31 p)
def d35 (p : Pattern) : Int := if p 271 then d2 p else d0 p
theorem agree35 (p q : Pattern) (h : Agree support p q) : d35 p = d35 q := by
  simp only [d35, h 271 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative35 (p : Pattern) : 0 ≤ d35 p :=
  nonnegative_ite (p 271) (nonnegative2 p) (nonnegative0 p)
def d36 (p : Pattern) : Int := if p 193 then d35 p else d0 p
theorem agree36 (p q : Pattern) (h : Agree support p q) : d36 p = d36 q := by
  simp only [d36, h 193 (by decide), agree35 p q h, agree0 p q h]
theorem nonnegative36 (p : Pattern) : 0 ≤ d36 p :=
  nonnegative_ite (p 193) (nonnegative35 p) (nonnegative0 p)
def d37 (p : Pattern) : Int := if p 193 then d9 p else d16 p
theorem agree37 (p q : Pattern) (h : Agree support p q) : d37 p = d37 q := by
  simp only [d37, h 193 (by decide), agree9 p q h, agree16 p q h]
theorem nonnegative37 (p : Pattern) : 0 ≤ d37 p :=
  nonnegative_ite (p 193) (nonnegative9 p) (nonnegative16 p)
def d38 (p : Pattern) : Int := if p 192 then d37 p else d36 p
theorem agree38 (p q : Pattern) (h : Agree support p q) : d38 p = d38 q := by
  simp only [d38, h 192 (by decide), agree37 p q h, agree36 p q h]
theorem nonnegative38 (p : Pattern) : 0 ≤ d38 p :=
  nonnegative_ite (p 192) (nonnegative37 p) (nonnegative36 p)
def d39 (p : Pattern) : Int := if p 193 then d16 p else d0 p
theorem agree39 (p q : Pattern) (h : Agree support p q) : d39 p = d39 q := by
  simp only [d39, h 193 (by decide), agree16 p q h, agree0 p q h]
theorem nonnegative39 (p : Pattern) : 0 ≤ d39 p :=
  nonnegative_ite (p 193) (nonnegative16 p) (nonnegative0 p)
def d40 (p : Pattern) : Int := if p 192 then d37 p else d39 p
theorem agree40 (p q : Pattern) (h : Agree support p q) : d40 p = d40 q := by
  simp only [d40, h 192 (by decide), agree37 p q h, agree39 p q h]
theorem nonnegative40 (p : Pattern) : 0 ≤ d40 p :=
  nonnegative_ite (p 192) (nonnegative37 p) (nonnegative39 p)
def d41 (p : Pattern) : Int := if p 168 then d40 p else d38 p
theorem agree41 (p q : Pattern) (h : Agree support p q) : d41 p = d41 q := by
  simp only [d41, h 168 (by decide), agree40 p q h, agree38 p q h]
theorem nonnegative41 (p : Pattern) : 0 ≤ d41 p :=
  nonnegative_ite (p 168) (nonnegative40 p) (nonnegative38 p)
def d42 (p : Pattern) : Int := if p 192 then d37 p else d16 p
theorem agree42 (p q : Pattern) (h : Agree support p q) : d42 p = d42 q := by
  simp only [d42, h 192 (by decide), agree37 p q h, agree16 p q h]
theorem nonnegative42 (p : Pattern) : 0 ≤ d42 p :=
  nonnegative_ite (p 192) (nonnegative37 p) (nonnegative16 p)
def d43 (p : Pattern) : Int := if p 168 then d42 p else d40 p
theorem agree43 (p q : Pattern) (h : Agree support p q) : d43 p = d43 q := by
  simp only [d43, h 168 (by decide), agree42 p q h, agree40 p q h]
theorem nonnegative43 (p : Pattern) : 0 ≤ d43 p :=
  nonnegative_ite (p 168) (nonnegative42 p) (nonnegative40 p)
def d44 (p : Pattern) : Int := if p 141 then d43 p else d41 p
theorem agree44 (p q : Pattern) (h : Agree support p q) : d44 p = d44 q := by
  simp only [d44, h 141 (by decide), agree43 p q h, agree41 p q h]
theorem nonnegative44 (p : Pattern) : 0 ≤ d44 p :=
  nonnegative_ite (p 141) (nonnegative43 p) (nonnegative41 p)
def d45 (p : Pattern) : Int := if p 186 then d2 p else d0 p
theorem agree45 (p q : Pattern) (h : Agree support p q) : d45 p = d45 q := by
  simp only [d45, h 186 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative45 (p : Pattern) : 0 ≤ d45 p :=
  nonnegative_ite (p 186) (nonnegative2 p) (nonnegative0 p)
def d46 (p : Pattern) : Int := if p 160 then d45 p else d0 p
theorem agree46 (p q : Pattern) (h : Agree support p q) : d46 p = d46 q := by
  simp only [d46, h 160 (by decide), agree45 p q h, agree0 p q h]
theorem nonnegative46 (p : Pattern) : 0 ≤ d46 p :=
  nonnegative_ite (p 160) (nonnegative45 p) (nonnegative0 p)
def d47 (p : Pattern) : Int := if p 134 then d2 p else d46 p
theorem agree47 (p q : Pattern) (h : Agree support p q) : d47 p = d47 q := by
  simp only [d47, h 134 (by decide), agree2 p q h, agree46 p q h]
theorem nonnegative47 (p : Pattern) : 0 ≤ d47 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative46 p)
def d48 (p : Pattern) : Int := if p 158 then d2 p else d46 p
theorem agree48 (p q : Pattern) (h : Agree support p q) : d48 p = d48 q := by
  simp only [d48, h 158 (by decide), agree2 p q h, agree46 p q h]
theorem nonnegative48 (p : Pattern) : 0 ≤ d48 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative46 p)
def d49 (p : Pattern) : Int := if p 134 then d2 p else d48 p
theorem agree49 (p q : Pattern) (h : Agree support p q) : d49 p = d49 q := by
  simp only [d49, h 134 (by decide), agree2 p q h, agree48 p q h]
theorem nonnegative49 (p : Pattern) : 0 ≤ d49 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative48 p)
def d50 (p : Pattern) : Int := if p 133 then d49 p else d47 p
theorem agree50 (p q : Pattern) (h : Agree support p q) : d50 p = d50 q := by
  simp only [d50, h 133 (by decide), agree49 p q h, agree47 p q h]
theorem nonnegative50 (p : Pattern) : 0 ≤ d50 p :=
  nonnegative_ite (p 133) (nonnegative49 p) (nonnegative47 p)
def d51 (p : Pattern) : Int := if p 133 then d2 p else d49 p
theorem agree51 (p q : Pattern) (h : Agree support p q) : d51 p = d51 q := by
  simp only [d51, h 133 (by decide), agree2 p q h, agree49 p q h]
theorem nonnegative51 (p : Pattern) : 0 ≤ d51 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative49 p)
def d52 (p : Pattern) : Int := if p 132 then d51 p else d50 p
theorem agree52 (p q : Pattern) (h : Agree support p q) : d52 p = d52 q := by
  simp only [d52, h 132 (by decide), agree51 p q h, agree50 p q h]
theorem nonnegative52 (p : Pattern) : 0 ≤ d52 p :=
  nonnegative_ite (p 132) (nonnegative51 p) (nonnegative50 p)
def d53 (p : Pattern) : Int := if p 108 then d2 p else d52 p
theorem agree53 (p q : Pattern) (h : Agree support p q) : d53 p = d53 q := by
  simp only [d53, h 108 (by decide), agree2 p q h, agree52 p q h]
theorem nonnegative53 (p : Pattern) : 0 ≤ d53 p :=
  nonnegative_ite (p 108) (nonnegative2 p) (nonnegative52 p)
def d54 (p : Pattern) : Int := if p 193 then d4 p else d2 p
theorem agree54 (p q : Pattern) (h : Agree support p q) : d54 p = d54 q := by
  simp only [d54, h 193 (by decide), agree4 p q h, agree2 p q h]
theorem nonnegative54 (p : Pattern) : 0 ≤ d54 p :=
  nonnegative_ite (p 193) (nonnegative4 p) (nonnegative2 p)
def d55 (p : Pattern) : Int := if p 192 then d54 p else d2 p
theorem agree55 (p q : Pattern) (h : Agree support p q) : d55 p = d55 q := by
  simp only [d55, h 192 (by decide), agree54 p q h, agree2 p q h]
theorem nonnegative55 (p : Pattern) : 0 ≤ d55 p :=
  nonnegative_ite (p 192) (nonnegative54 p) (nonnegative2 p)
def d56 (p : Pattern) : Int := if p 186 then d55 p else d7 p
theorem agree56 (p q : Pattern) (h : Agree support p q) : d56 p = d56 q := by
  simp only [d56, h 186 (by decide), agree55 p q h, agree7 p q h]
theorem nonnegative56 (p : Pattern) : 0 ≤ d56 p :=
  nonnegative_ite (p 186) (nonnegative55 p) (nonnegative7 p)
def d57 (p : Pattern) : Int := if p 160 then d56 p else d7 p
theorem agree57 (p q : Pattern) (h : Agree support p q) : d57 p = d57 q := by
  simp only [d57, h 160 (by decide), agree56 p q h, agree7 p q h]
theorem nonnegative57 (p : Pattern) : 0 ≤ d57 p :=
  nonnegative_ite (p 160) (nonnegative56 p) (nonnegative7 p)
def d58 (p : Pattern) : Int := if p 271 then d5 p else d4 p
theorem agree58 (p q : Pattern) (h : Agree support p q) : d58 p = d58 q := by
  simp only [d58, h 271 (by decide), agree5 p q h, agree4 p q h]
theorem nonnegative58 (p : Pattern) : 0 ≤ d58 p :=
  nonnegative_ite (p 271) (nonnegative5 p) (nonnegative4 p)
def d59 (p : Pattern) : Int := if p 193 then d58 p else d9 p
theorem agree59 (p q : Pattern) (h : Agree support p q) : d59 p = d59 q := by
  simp only [d59, h 193 (by decide), agree58 p q h, agree9 p q h]
theorem nonnegative59 (p : Pattern) : 0 ≤ d59 p :=
  nonnegative_ite (p 193) (nonnegative58 p) (nonnegative9 p)
def d60 (p : Pattern) : Int := if p 192 then d59 p else d9 p
theorem agree60 (p q : Pattern) (h : Agree support p q) : d60 p = d60 q := by
  simp only [d60, h 192 (by decide), agree59 p q h, agree9 p q h]
theorem nonnegative60 (p : Pattern) : 0 ≤ d60 p :=
  nonnegative_ite (p 192) (nonnegative59 p) (nonnegative9 p)
def d61 (p : Pattern) : Int := if p 186 then d60 p else d11 p
theorem agree61 (p q : Pattern) (h : Agree support p q) : d61 p = d61 q := by
  simp only [d61, h 186 (by decide), agree60 p q h, agree11 p q h]
theorem nonnegative61 (p : Pattern) : 0 ≤ d61 p :=
  nonnegative_ite (p 186) (nonnegative60 p) (nonnegative11 p)
def d62 (p : Pattern) : Int := if p 168 then d61 p else d56 p
theorem agree62 (p q : Pattern) (h : Agree support p q) : d62 p = d62 q := by
  simp only [d62, h 168 (by decide), agree61 p q h, agree56 p q h]
theorem nonnegative62 (p : Pattern) : 0 ≤ d62 p :=
  nonnegative_ite (p 168) (nonnegative61 p) (nonnegative56 p)
def d63 (p : Pattern) : Int := if p 160 then d62 p else d12 p
theorem agree63 (p q : Pattern) (h : Agree support p q) : d63 p = d63 q := by
  simp only [d63, h 160 (by decide), agree62 p q h, agree12 p q h]
theorem nonnegative63 (p : Pattern) : 0 ≤ d63 p :=
  nonnegative_ite (p 160) (nonnegative62 p) (nonnegative12 p)
def d64 (p : Pattern) : Int := if p 141 then d63 p else d57 p
theorem agree64 (p q : Pattern) (h : Agree support p q) : d64 p = d64 q := by
  simp only [d64, h 141 (by decide), agree63 p q h, agree57 p q h]
theorem nonnegative64 (p : Pattern) : 0 ≤ d64 p :=
  nonnegative_ite (p 141) (nonnegative63 p) (nonnegative57 p)
def d65 (p : Pattern) : Int := if p 168 then d60 p else d55 p
theorem agree65 (p q : Pattern) (h : Agree support p q) : d65 p = d65 q := by
  simp only [d65, h 168 (by decide), agree60 p q h, agree55 p q h]
theorem nonnegative65 (p : Pattern) : 0 ≤ d65 p :=
  nonnegative_ite (p 168) (nonnegative60 p) (nonnegative55 p)
def d66 (p : Pattern) : Int := if p 141 then d65 p else d55 p
theorem agree66 (p q : Pattern) (h : Agree support p q) : d66 p = d66 q := by
  simp only [d66, h 141 (by decide), agree65 p q h, agree55 p q h]
theorem nonnegative66 (p : Pattern) : 0 ≤ d66 p :=
  nonnegative_ite (p 141) (nonnegative65 p) (nonnegative55 p)
def d67 (p : Pattern) : Int := if p 134 then d66 p else d64 p
theorem agree67 (p q : Pattern) (h : Agree support p q) : d67 p = d67 q := by
  simp only [d67, h 134 (by decide), agree66 p q h, agree64 p q h]
theorem nonnegative67 (p : Pattern) : 0 ≤ d67 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative64 p)
def d68 (p : Pattern) : Int := if p 158 then d55 p else d57 p
theorem agree68 (p q : Pattern) (h : Agree support p q) : d68 p = d68 q := by
  simp only [d68, h 158 (by decide), agree55 p q h, agree57 p q h]
theorem nonnegative68 (p : Pattern) : 0 ≤ d68 p :=
  nonnegative_ite (p 158) (nonnegative55 p) (nonnegative57 p)
def d69 (p : Pattern) : Int := if p 158 then d65 p else d63 p
theorem agree69 (p q : Pattern) (h : Agree support p q) : d69 p = d69 q := by
  simp only [d69, h 158 (by decide), agree65 p q h, agree63 p q h]
theorem nonnegative69 (p : Pattern) : 0 ≤ d69 p :=
  nonnegative_ite (p 158) (nonnegative65 p) (nonnegative63 p)
def d70 (p : Pattern) : Int := if p 141 then d69 p else d68 p
theorem agree70 (p q : Pattern) (h : Agree support p q) : d70 p = d70 q := by
  simp only [d70, h 141 (by decide), agree69 p q h, agree68 p q h]
theorem nonnegative70 (p : Pattern) : 0 ≤ d70 p :=
  nonnegative_ite (p 141) (nonnegative69 p) (nonnegative68 p)
def d71 (p : Pattern) : Int := if p 134 then d66 p else d70 p
theorem agree71 (p q : Pattern) (h : Agree support p q) : d71 p = d71 q := by
  simp only [d71, h 134 (by decide), agree66 p q h, agree70 p q h]
theorem nonnegative71 (p : Pattern) : 0 ≤ d71 p :=
  nonnegative_ite (p 134) (nonnegative66 p) (nonnegative70 p)
def d72 (p : Pattern) : Int := if p 133 then d71 p else d67 p
theorem agree72 (p q : Pattern) (h : Agree support p q) : d72 p = d72 q := by
  simp only [d72, h 133 (by decide), agree71 p q h, agree67 p q h]
theorem nonnegative72 (p : Pattern) : 0 ≤ d72 p :=
  nonnegative_ite (p 133) (nonnegative71 p) (nonnegative67 p)
def d73 (p : Pattern) : Int := if p 133 then d66 p else d71 p
theorem agree73 (p q : Pattern) (h : Agree support p q) : d73 p = d73 q := by
  simp only [d73, h 133 (by decide), agree66 p q h, agree71 p q h]
theorem nonnegative73 (p : Pattern) : 0 ≤ d73 p :=
  nonnegative_ite (p 133) (nonnegative66 p) (nonnegative71 p)
def d74 (p : Pattern) : Int := if p 132 then d73 p else d72 p
theorem agree74 (p q : Pattern) (h : Agree support p q) : d74 p = d74 q := by
  simp only [d74, h 132 (by decide), agree73 p q h, agree72 p q h]
theorem nonnegative74 (p : Pattern) : 0 ≤ d74 p :=
  nonnegative_ite (p 132) (nonnegative73 p) (nonnegative72 p)
def d75 (p : Pattern) : Int := if p 108 then d66 p else d74 p
theorem agree75 (p q : Pattern) (h : Agree support p q) : d75 p = d75 q := by
  simp only [d75, h 108 (by decide), agree66 p q h, agree74 p q h]
theorem nonnegative75 (p : Pattern) : 0 ≤ d75 p :=
  nonnegative_ite (p 108) (nonnegative66 p) (nonnegative74 p)
def d76 (p : Pattern) : Int := if p 160 then d2 p else d0 p
theorem agree76 (p q : Pattern) (h : Agree support p q) : d76 p = d76 q := by
  simp only [d76, h 160 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative76 (p : Pattern) : 0 ≤ d76 p :=
  nonnegative_ite (p 160) (nonnegative2 p) (nonnegative0 p)
def d77 (p : Pattern) : Int := if p 159 then d2 p else d76 p
theorem agree77 (p q : Pattern) (h : Agree support p q) : d77 p = d77 q := by
  simp only [d77, h 159 (by decide), agree2 p q h, agree76 p q h]
theorem nonnegative77 (p : Pattern) : 0 ≤ d77 p :=
  nonnegative_ite (p 159) (nonnegative2 p) (nonnegative76 p)
def d78 (p : Pattern) : Int := if p 158 then d77 p else d76 p
theorem agree78 (p q : Pattern) (h : Agree support p q) : d78 p = d78 q := by
  simp only [d78, h 158 (by decide), agree77 p q h, agree76 p q h]
theorem nonnegative78 (p : Pattern) : 0 ≤ d78 p :=
  nonnegative_ite (p 158) (nonnegative77 p) (nonnegative76 p)
def d79 (p : Pattern) : Int := if p 134 then d78 p else d46 p
theorem agree79 (p q : Pattern) (h : Agree support p q) : d79 p = d79 q := by
  simp only [d79, h 134 (by decide), agree78 p q h, agree46 p q h]
theorem nonnegative79 (p : Pattern) : 0 ≤ d79 p :=
  nonnegative_ite (p 134) (nonnegative78 p) (nonnegative46 p)
def d80 (p : Pattern) : Int := if p 159 then d2 p else d46 p
theorem agree80 (p q : Pattern) (h : Agree support p q) : d80 p = d80 q := by
  simp only [d80, h 159 (by decide), agree2 p q h, agree46 p q h]
theorem nonnegative80 (p : Pattern) : 0 ≤ d80 p :=
  nonnegative_ite (p 159) (nonnegative2 p) (nonnegative46 p)
def d81 (p : Pattern) : Int := if p 158 then d80 p else d46 p
theorem agree81 (p q : Pattern) (h : Agree support p q) : d81 p = d81 q := by
  simp only [d81, h 158 (by decide), agree80 p q h, agree46 p q h]
theorem nonnegative81 (p : Pattern) : 0 ≤ d81 p :=
  nonnegative_ite (p 158) (nonnegative80 p) (nonnegative46 p)
def d82 (p : Pattern) : Int := if p 187 then d2 p else d0 p
theorem agree82 (p q : Pattern) (h : Agree support p q) : d82 p = d82 q := by
  simp only [d82, h 187 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative82 (p : Pattern) : 0 ≤ d82 p :=
  nonnegative_ite (p 187) (nonnegative2 p) (nonnegative0 p)
def d83 (p : Pattern) : Int := if p 186 then d82 p else d0 p
theorem agree83 (p q : Pattern) (h : Agree support p q) : d83 p = d83 q := by
  simp only [d83, h 186 (by decide), agree82 p q h, agree0 p q h]
theorem nonnegative83 (p : Pattern) : 0 ≤ d83 p :=
  nonnegative_ite (p 186) (nonnegative82 p) (nonnegative0 p)
def d84 (p : Pattern) : Int := if p 160 then d2 p else d83 p
theorem agree84 (p q : Pattern) (h : Agree support p q) : d84 p = d84 q := by
  simp only [d84, h 160 (by decide), agree2 p q h, agree83 p q h]
theorem nonnegative84 (p : Pattern) : 0 ≤ d84 p :=
  nonnegative_ite (p 160) (nonnegative2 p) (nonnegative83 p)
def d85 (p : Pattern) : Int := if p 159 then d84 p else d76 p
theorem agree85 (p q : Pattern) (h : Agree support p q) : d85 p = d85 q := by
  simp only [d85, h 159 (by decide), agree84 p q h, agree76 p q h]
theorem nonnegative85 (p : Pattern) : 0 ≤ d85 p :=
  nonnegative_ite (p 159) (nonnegative84 p) (nonnegative76 p)
def d86 (p : Pattern) : Int := if p 159 then d2 p else d84 p
theorem agree86 (p q : Pattern) (h : Agree support p q) : d86 p = d86 q := by
  simp only [d86, h 159 (by decide), agree2 p q h, agree84 p q h]
theorem nonnegative86 (p : Pattern) : 0 ≤ d86 p :=
  nonnegative_ite (p 159) (nonnegative2 p) (nonnegative84 p)
def d87 (p : Pattern) : Int := if p 158 then d86 p else d85 p
theorem agree87 (p q : Pattern) (h : Agree support p q) : d87 p = d87 q := by
  simp only [d87, h 158 (by decide), agree86 p q h, agree85 p q h]
theorem nonnegative87 (p : Pattern) : 0 ≤ d87 p :=
  nonnegative_ite (p 158) (nonnegative86 p) (nonnegative85 p)
def d88 (p : Pattern) : Int := if p 134 then d87 p else d81 p
theorem agree88 (p q : Pattern) (h : Agree support p q) : d88 p = d88 q := by
  simp only [d88, h 134 (by decide), agree87 p q h, agree81 p q h]
theorem nonnegative88 (p : Pattern) : 0 ≤ d88 p :=
  nonnegative_ite (p 134) (nonnegative87 p) (nonnegative81 p)
def d89 (p : Pattern) : Int := if p 133 then d88 p else d79 p
theorem agree89 (p q : Pattern) (h : Agree support p q) : d89 p = d89 q := by
  simp only [d89, h 133 (by decide), agree88 p q h, agree79 p q h]
theorem nonnegative89 (p : Pattern) : 0 ≤ d89 p :=
  nonnegative_ite (p 133) (nonnegative88 p) (nonnegative79 p)
def d90 (p : Pattern) : Int := if p 133 then d2 p else d88 p
theorem agree90 (p q : Pattern) (h : Agree support p q) : d90 p = d90 q := by
  simp only [d90, h 133 (by decide), agree2 p q h, agree88 p q h]
theorem nonnegative90 (p : Pattern) : 0 ≤ d90 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative88 p)
def d91 (p : Pattern) : Int := if p 132 then d90 p else d89 p
theorem agree91 (p q : Pattern) (h : Agree support p q) : d91 p = d91 q := by
  simp only [d91, h 132 (by decide), agree90 p q h, agree89 p q h]
theorem nonnegative91 (p : Pattern) : 0 ≤ d91 p :=
  nonnegative_ite (p 132) (nonnegative90 p) (nonnegative89 p)
def d92 (p : Pattern) : Int := if p 186 then d2 p else d82 p
theorem agree92 (p q : Pattern) (h : Agree support p q) : d92 p = d92 q := by
  simp only [d92, h 186 (by decide), agree2 p q h, agree82 p q h]
theorem nonnegative92 (p : Pattern) : 0 ≤ d92 p :=
  nonnegative_ite (p 186) (nonnegative2 p) (nonnegative82 p)
def d93 (p : Pattern) : Int := if p 160 then d92 p else d0 p
theorem agree93 (p q : Pattern) (h : Agree support p q) : d93 p = d93 q := by
  simp only [d93, h 160 (by decide), agree92 p q h, agree0 p q h]
theorem nonnegative93 (p : Pattern) : 0 ≤ d93 p :=
  nonnegative_ite (p 160) (nonnegative92 p) (nonnegative0 p)
def d94 (p : Pattern) : Int := if p 160 then d92 p else d83 p
theorem agree94 (p q : Pattern) (h : Agree support p q) : d94 p = d94 q := by
  simp only [d94, h 160 (by decide), agree92 p q h, agree83 p q h]
theorem nonnegative94 (p : Pattern) : 0 ≤ d94 p :=
  nonnegative_ite (p 160) (nonnegative92 p) (nonnegative83 p)
def d95 (p : Pattern) : Int := if p 159 then d94 p else d93 p
theorem agree95 (p q : Pattern) (h : Agree support p q) : d95 p = d95 q := by
  simp only [d95, h 159 (by decide), agree94 p q h, agree93 p q h]
theorem nonnegative95 (p : Pattern) : 0 ≤ d95 p :=
  nonnegative_ite (p 159) (nonnegative94 p) (nonnegative93 p)
def d96 (p : Pattern) : Int := if p 159 then d2 p else d94 p
theorem agree96 (p q : Pattern) (h : Agree support p q) : d96 p = d96 q := by
  simp only [d96, h 159 (by decide), agree2 p q h, agree94 p q h]
theorem nonnegative96 (p : Pattern) : 0 ≤ d96 p :=
  nonnegative_ite (p 159) (nonnegative2 p) (nonnegative94 p)
def d97 (p : Pattern) : Int := if p 158 then d96 p else d95 p
theorem agree97 (p q : Pattern) (h : Agree support p q) : d97 p = d97 q := by
  simp only [d97, h 158 (by decide), agree96 p q h, agree95 p q h]
theorem nonnegative97 (p : Pattern) : 0 ≤ d97 p :=
  nonnegative_ite (p 158) (nonnegative96 p) (nonnegative95 p)
def d98 (p : Pattern) : Int := if p 134 then d2 p else d97 p
theorem agree98 (p q : Pattern) (h : Agree support p q) : d98 p = d98 q := by
  simp only [d98, h 134 (by decide), agree2 p q h, agree97 p q h]
theorem nonnegative98 (p : Pattern) : 0 ≤ d98 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative97 p)
def d99 (p : Pattern) : Int := if p 133 then d98 p else d47 p
theorem agree99 (p q : Pattern) (h : Agree support p q) : d99 p = d99 q := by
  simp only [d99, h 133 (by decide), agree98 p q h, agree47 p q h]
theorem nonnegative99 (p : Pattern) : 0 ≤ d99 p :=
  nonnegative_ite (p 133) (nonnegative98 p) (nonnegative47 p)
def d100 (p : Pattern) : Int := if p 159 then d94 p else d46 p
theorem agree100 (p q : Pattern) (h : Agree support p q) : d100 p = d100 q := by
  simp only [d100, h 159 (by decide), agree94 p q h, agree46 p q h]
theorem nonnegative100 (p : Pattern) : 0 ≤ d100 p :=
  nonnegative_ite (p 159) (nonnegative94 p) (nonnegative46 p)
def d101 (p : Pattern) : Int := if p 158 then d96 p else d100 p
theorem agree101 (p q : Pattern) (h : Agree support p q) : d101 p = d101 q := by
  simp only [d101, h 158 (by decide), agree96 p q h, agree100 p q h]
theorem nonnegative101 (p : Pattern) : 0 ≤ d101 p :=
  nonnegative_ite (p 158) (nonnegative96 p) (nonnegative100 p)
def d102 (p : Pattern) : Int := if p 134 then d2 p else d101 p
theorem agree102 (p q : Pattern) (h : Agree support p q) : d102 p = d102 q := by
  simp only [d102, h 134 (by decide), agree2 p q h, agree101 p q h]
theorem nonnegative102 (p : Pattern) : 0 ≤ d102 p :=
  nonnegative_ite (p 134) (nonnegative2 p) (nonnegative101 p)
def d103 (p : Pattern) : Int := if p 133 then d2 p else d102 p
theorem agree103 (p q : Pattern) (h : Agree support p q) : d103 p = d103 q := by
  simp only [d103, h 133 (by decide), agree2 p q h, agree102 p q h]
theorem nonnegative103 (p : Pattern) : 0 ≤ d103 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative102 p)
def d104 (p : Pattern) : Int := if p 132 then d103 p else d99 p
theorem agree104 (p q : Pattern) (h : Agree support p q) : d104 p = d104 q := by
  simp only [d104, h 132 (by decide), agree103 p q h, agree99 p q h]
theorem nonnegative104 (p : Pattern) : 0 ≤ d104 p :=
  nonnegative_ite (p 132) (nonnegative103 p) (nonnegative99 p)
def d105 (p : Pattern) : Int := if p 108 then d104 p else d91 p
theorem agree105 (p q : Pattern) (h : Agree support p q) : d105 p = d105 q := by
  simp only [d105, h 108 (by decide), agree104 p q h, agree91 p q h]
theorem nonnegative105 (p : Pattern) : 0 ≤ d105 p :=
  nonnegative_ite (p 108) (nonnegative104 p) (nonnegative91 p)
def d106 (p : Pattern) : Int := if p 160 then d55 p else d7 p
theorem agree106 (p q : Pattern) (h : Agree support p q) : d106 p = d106 q := by
  simp only [d106, h 160 (by decide), agree55 p q h, agree7 p q h]
theorem nonnegative106 (p : Pattern) : 0 ≤ d106 p :=
  nonnegative_ite (p 160) (nonnegative55 p) (nonnegative7 p)
def d107 (p : Pattern) : Int := if p 159 then d55 p else d106 p
theorem agree107 (p q : Pattern) (h : Agree support p q) : d107 p = d107 q := by
  simp only [d107, h 159 (by decide), agree55 p q h, agree106 p q h]
theorem nonnegative107 (p : Pattern) : 0 ≤ d107 p :=
  nonnegative_ite (p 159) (nonnegative55 p) (nonnegative106 p)
def d108 (p : Pattern) : Int := if p 158 then d107 p else d106 p
theorem agree108 (p q : Pattern) (h : Agree support p q) : d108 p = d108 q := by
  simp only [d108, h 158 (by decide), agree107 p q h, agree106 p q h]
theorem nonnegative108 (p : Pattern) : 0 ≤ d108 p :=
  nonnegative_ite (p 158) (nonnegative107 p) (nonnegative106 p)
def d109 (p : Pattern) : Int := if p 160 then d65 p else d12 p
theorem agree109 (p q : Pattern) (h : Agree support p q) : d109 p = d109 q := by
  simp only [d109, h 160 (by decide), agree65 p q h, agree12 p q h]
theorem nonnegative109 (p : Pattern) : 0 ≤ d109 p :=
  nonnegative_ite (p 160) (nonnegative65 p) (nonnegative12 p)
def d110 (p : Pattern) : Int := if p 159 then d65 p else d109 p
theorem agree110 (p q : Pattern) (h : Agree support p q) : d110 p = d110 q := by
  simp only [d110, h 159 (by decide), agree65 p q h, agree109 p q h]
theorem nonnegative110 (p : Pattern) : 0 ≤ d110 p :=
  nonnegative_ite (p 159) (nonnegative65 p) (nonnegative109 p)
def d111 (p : Pattern) : Int := if p 158 then d110 p else d109 p
theorem agree111 (p q : Pattern) (h : Agree support p q) : d111 p = d111 q := by
  simp only [d111, h 158 (by decide), agree110 p q h, agree109 p q h]
theorem nonnegative111 (p : Pattern) : 0 ≤ d111 p :=
  nonnegative_ite (p 158) (nonnegative110 p) (nonnegative109 p)
def d112 (p : Pattern) : Int := if p 141 then d111 p else d108 p
theorem agree112 (p q : Pattern) (h : Agree support p q) : d112 p = d112 q := by
  simp only [d112, h 141 (by decide), agree111 p q h, agree108 p q h]
theorem nonnegative112 (p : Pattern) : 0 ≤ d112 p :=
  nonnegative_ite (p 141) (nonnegative111 p) (nonnegative108 p)
def d113 (p : Pattern) : Int := if p 134 then d112 p else d64 p
theorem agree113 (p q : Pattern) (h : Agree support p q) : d113 p = d113 q := by
  simp only [d113, h 134 (by decide), agree112 p q h, agree64 p q h]
theorem nonnegative113 (p : Pattern) : 0 ≤ d113 p :=
  nonnegative_ite (p 134) (nonnegative112 p) (nonnegative64 p)
def d114 (p : Pattern) : Int := if p 159 then d55 p else d57 p
theorem agree114 (p q : Pattern) (h : Agree support p q) : d114 p = d114 q := by
  simp only [d114, h 159 (by decide), agree55 p q h, agree57 p q h]
theorem nonnegative114 (p : Pattern) : 0 ≤ d114 p :=
  nonnegative_ite (p 159) (nonnegative55 p) (nonnegative57 p)
def d115 (p : Pattern) : Int := if p 158 then d114 p else d57 p
theorem agree115 (p q : Pattern) (h : Agree support p q) : d115 p = d115 q := by
  simp only [d115, h 158 (by decide), agree114 p q h, agree57 p q h]
theorem nonnegative115 (p : Pattern) : 0 ≤ d115 p :=
  nonnegative_ite (p 158) (nonnegative114 p) (nonnegative57 p)
def d116 (p : Pattern) : Int := if p 159 then d65 p else d63 p
theorem agree116 (p q : Pattern) (h : Agree support p q) : d116 p = d116 q := by
  simp only [d116, h 159 (by decide), agree65 p q h, agree63 p q h]
theorem nonnegative116 (p : Pattern) : 0 ≤ d116 p :=
  nonnegative_ite (p 159) (nonnegative65 p) (nonnegative63 p)
def d117 (p : Pattern) : Int := if p 158 then d116 p else d63 p
theorem agree117 (p q : Pattern) (h : Agree support p q) : d117 p = d117 q := by
  simp only [d117, h 158 (by decide), agree116 p q h, agree63 p q h]
theorem nonnegative117 (p : Pattern) : 0 ≤ d117 p :=
  nonnegative_ite (p 158) (nonnegative116 p) (nonnegative63 p)
def d118 (p : Pattern) : Int := if p 141 then d117 p else d115 p
theorem agree118 (p q : Pattern) (h : Agree support p q) : d118 p = d118 q := by
  simp only [d118, h 141 (by decide), agree117 p q h, agree115 p q h]
theorem nonnegative118 (p : Pattern) : 0 ≤ d118 p :=
  nonnegative_ite (p 141) (nonnegative117 p) (nonnegative115 p)
def d119 (p : Pattern) : Int := if p 187 then d55 p else d7 p
theorem agree119 (p q : Pattern) (h : Agree support p q) : d119 p = d119 q := by
  simp only [d119, h 187 (by decide), agree55 p q h, agree7 p q h]
theorem nonnegative119 (p : Pattern) : 0 ≤ d119 p :=
  nonnegative_ite (p 187) (nonnegative55 p) (nonnegative7 p)
end NetHack.Sokoban12CostPartition
