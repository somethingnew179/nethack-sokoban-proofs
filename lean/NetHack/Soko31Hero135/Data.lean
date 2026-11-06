/- Four exact occupancy rows proposed from initial residual0/1 layers.
All Model directions at every positive hero are checked; no search premise. -/
import NetHack.Soko31Hero133.Verified
import NetHack.Sokoban.HeroPhasePotential.Residual
import NetHack.Sokoban.ListNormalizer
import NetHack.Sokoban.ClosedComponents
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
def cert := NetHack.Soko31Hero133.certificate NetHack.Soko31Hero133.all_walk_rows
  NetHack.Soko31Hero133.all_push_rows NetHack.Soko31Hero133.all_advance_rows
def base : State → Int := HeroPhasePotential.value cert
theorem base_eq (s : State) : base s = NetHack.Soko31Hero133.candidateValue s := rfl
def norm : Normalizer soko3_1.board := ListNormalizer.normalizer soko3_1.board
  ClosedComponents.soko3_1Support soko3_1.initial.holes
  (ClosedSupport.check_sound _ _ ClosedComponents.soko3_1_closed_checked)
  ClosedComponents.soko3_1_support_unique (by decide +kernel)
def code (cells : List Cell) : Nat := cells.foldl (fun bits cell => bits + (1 <<< cell)) 0
def key (s : State) : Nat := code s.boulders
def entry0 : Entry := ⟨[61, 62, 64, 65, 93, 177, 205, 206, 209, 211, 213, 235, 241, 263, 264, 265, 267, 270, 298, 300],soko3_1.initial.holes,finiteScore 348 0 79753679885744237880995659343491760128⟩
def entry1 : Entry := ⟨[36, 61, 62, 64, 93, 177, 205, 206, 209, 211, 213, 235, 241, 263, 264, 265, 267, 270, 298, 300],soko3_1.initial.holes,finiteScore 348 79753679885744237917889147387831648256 0⟩
def entry2 : Entry := ⟨[61, 62, 64, 93, 94, 177, 205, 206, 209, 211, 213, 235, 241, 263, 264, 265, 267, 270, 298, 300],soko3_1.initial.holes,finiteScore 348 79753679865937197289323063092524875776 0⟩
def entry3 : Entry := ⟨[61, 62, 64, 65, 92, 177, 205, 206, 209, 211, 213, 235, 241, 263, 264, 265, 267, 270, 298, 300],soko3_1.initial.holes,finiteScore 348 79753679895647758195278701542684753920 0⟩
def table : Table := (.node 2546294972656137112203312653421659773341416875141916697198978349434380918142510964370571264 entry0 (.node 2546294972656137112203312653421659773341416875141916697198978349434380881249022885670944768 entry1 (.node 2546294972656137112203312653421659773341416875141916697198978344482620761000989864774074368 entry3 .empty .empty) .empty) (.node 2546294972656137112203312653421659773341416875141916697198978369241421509815107215337455616 entry2 .empty .empty))
end NetHack.Soko31Hero135
