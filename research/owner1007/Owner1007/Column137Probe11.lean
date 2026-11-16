import Owner1007.ActorPrices11
namespace Owner1007.Column137Probe11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def exits : List (Cell×Cell×Cell) := [(190,164,138),(216,190,164),(191,190,189),(189,190,191),(242,216,190),(215,216,217)]
/-- Negative diagnostic: the unguarded single-column proposal fails. -/
theorem prices_false : (List.range 16).all (fun p=>exits.all (fun (hero,source,dest)=>decide (2≤ActorPrices11.price p hero source dest)))=false := by decide +kernel
#print axioms prices_false
theorem north_free : (List.range 16).all (fun p=>decide
 (ActorPrices11.price p 190 164 138=0 ∧ ActorPrices11.price p 216 190 164=0 ∧
 ActorPrices11.price p 217 216 215=0))=true := by decide +kernel
#print axioms north_free
end Owner1007.Column137Probe11
