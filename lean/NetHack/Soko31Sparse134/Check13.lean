import NetHack.Soko31Sparse134.Check13Part00
import NetHack.Soko31Sparse134.Check13Part01
import NetHack.Soko31Sparse134.Check13Part02
import NetHack.Soko31Sparse134.Check13Part03
import NetHack.Soko31Sparse134.Check13Part04
import NetHack.Soko31Sparse134.Check13Part05
import NetHack.Soko31Sparse134.Check13Part06
import NetHack.Soko31Sparse134.Check13Part07
namespace NetHack.Soko31Sparse134
theorem checked13 : check 13 = true := by
  have partition : phases.heroes 13 = heroes13part00 ++ heroes13part01 ++ heroes13part02 ++ heroes13part03 ++ heroes13part04 ++ heroes13part05 ++ heroes13part06 ++ heroes13part07 := by decide +kernel
  rw [check_as_rows,partition]
  simp only [List.all_append,checked13part00,checked13part01,checked13part02,checked13part03,checked13part04,checked13part05,checked13part06,checked13part07,Bool.and_self]
end NetHack.Soko31Sparse134
