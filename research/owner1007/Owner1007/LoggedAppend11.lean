import Owner1007.TokenAccounting
namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

theorem Logged.append {board initial firstDirs middle firstPushes firstMoves firstOutcomes
 secondDirs final secondPushes secondMoves secondOutcomes}
 (first : Logged board initial firstDirs middle firstPushes firstMoves firstOutcomes)
 (second : Logged board middle secondDirs final secondPushes secondMoves secondOutcomes) :
 Logged board initial (firstDirs++secondDirs) final (firstPushes+secondPushes) (firstMoves+secondMoves) (firstOutcomes++secondOutcomes) := by
 induction first with
 | nil => simpa only [List.nil_append,Nat.zero_add] using second
 | @cons state dir t rest middle pushes moves outcome outcomes head effect tail ih =>
   have joined := Logged.cons head effect (ih second)
   simpa only [List.cons_append,Nat.add_assoc] using joined
#print axioms Logged.append
end Owner1007.TokenAccounting
