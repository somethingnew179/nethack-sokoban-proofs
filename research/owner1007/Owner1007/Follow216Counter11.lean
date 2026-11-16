import NetHack.Sokoban.Maps
namespace Owner1007.Follow216Counter11
open NetHack.Sokoban
/-- Local four-lock diagnostic only; this is not a canonical-start witness. -/
def before : State:={player:=189,boulders:=[186,188,213,216],holes:=soko1_1.initial.holes}
def middle : State:={before with player:=215}
def after : Transition:={state:={player:=216,boulders:=[217,186,188,213],holes:=soko1_1.initial.holes},pushed:=true,filled:=none,pushSource:=some 216,landing:=some 217}
/-- After the proposed189West shift, walkingSouth opens the forbiddenEast support. -/
theorem walk_south : step soko1_1.board before .south=some {state:=middle,pushed:=false,filled:=none}:=by decide +kernel
theorem push_east : step soko1_1.board middle .east=some after:=by decide +kernel
#print axioms walk_south
#print axioms push_east
end Owner1007.Follow216Counter11
