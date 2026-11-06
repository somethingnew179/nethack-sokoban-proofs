import NetHack.Soko31Sparse134.Base
namespace NetHack.Soko31Sparse134
def classifyRow (phase hero : Nat) : Bool := (List.range 8).all fun mask =>
  NetHack.Sokoban.allDirs.all fun direction => walkCheck phase hero mask direction && pushCheck phase hero mask direction
theorem check_as_rows (phase : Nat) : check phase = (phases.heroes phase).all (classifyRow phase) := rfl
end NetHack.Soko31Sparse134
