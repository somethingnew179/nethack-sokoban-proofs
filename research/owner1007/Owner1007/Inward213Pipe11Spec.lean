import Owner1007.Inward213Pipe11Geometry
import Owner1007.ShiftedPipe11
namespace Owner1007.Inward213Pipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def spec : ShiftedPipe11.Certificate 10 where
 locks:=locks
 region:=region
 u:=u
 paid:=paid
 terminal:=fun i=>decide ((phase i).val=4)
 unique:=unique
 nonempty:=nonempty
 size:=by intro i;rfl
 closed:=closed
 u_mem:=by intro i;simp [locks]
 u_options:=by decide +kernel
 only_u:=by
  intro i c alternatives member
  rcases alternatives with rfl|rfl
  ·have row : ∀i,(186:Cell)∈locks i→186=u i:=by decide +kernel
   exact row i member
  ·have row : ∀i,(187:Cell)∈locks i→187=u i:=by decide +kernel
   exact row i member
 u_paid:=by
  intro i dir
  by_cases branch : i.val<5 <;> simp [paid,u,branch]
 right_mem:=by intro i;simp [locks]
 right_paid:=by intro dir;simp [paid]
 frozen_shift:=by decide +kernel
 head:=by
  intro state dir t source i hero member inside checked metadata pays
  have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
  have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source (PairPost11.source_adjacent checked metadata)
  simp only [headCheck,behind] at row
  have shape:=of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata inside) pays
  rcases shape with terminal|west
  ·exact Or.inl (by simpa only [decide_eq_true_eq] using terminal)
  ·exact Or.inr west
#print axioms spec
end Owner1007.Inward213Pipe11
