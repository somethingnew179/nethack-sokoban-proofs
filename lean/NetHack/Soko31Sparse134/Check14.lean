import NetHack.Soko31Sparse134.Check14Part00
import NetHack.Soko31Sparse134.Check14Part01
import NetHack.Soko31Sparse134.Check14Part02
import NetHack.Soko31Sparse134.Check14Part03
import NetHack.Soko31Sparse134.Check14Part04
import NetHack.Soko31Sparse134.Check14Part05
import NetHack.Soko31Sparse134.Check14Part06
import NetHack.Soko31Sparse134.Check14Part07
import NetHack.Soko31Sparse134.Check14Part08
namespace NetHack.Soko31Sparse134
theorem checked14 : check 14 = true := by
  have partition : phases.heroes 14 = heroes14part00 ++ heroes14part01 ++ heroes14part02 ++ heroes14part03 ++ heroes14part04 ++ heroes14part05 ++ heroes14part06 ++ heroes14part07 ++ heroes14part08 := by decide +kernel
  rw [check_as_rows,partition]
  simp only [List.all_append,checked14part00,checked14part01,checked14part02,checked14part03,checked14part04,checked14part05,checked14part06,checked14part07,checked14part08,Bool.and_self]
end NetHack.Soko31Sparse134
