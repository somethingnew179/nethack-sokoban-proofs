import Owner1007.Left212TwoHistory11
import Owner1007.Left212TwoRank11
namespace Owner1007.Left212BeforeRest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem word {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (cheap212 : energy soko1_1.initial final [212] (outcomes++last)<4) :
 ∃dest,dest∈([211,212,213,214,239]:List Cell) ∧endGroup [212] outcomes=[dest] ∧
   Left212TwoWord11.rank dest≤energy soko1_1.initial state [212] outcomes := by
 have north:=Left212TwoHistory11.prefix_no_north prefixLog suffix completed cheap rest noRest
 have down:=SmallRestNoTopDown11.prefix_zero prefixLog suffix completed cheap rest noRest
 have quietDown:=QuietFromCount11.from_count prefixLog Gate265Transport11.upperOrigins down
 have smallDown:=TransportQuiet11.Quiet.project quietDown (by decide) (by decide) (by decide) [212] (by decide) (by decide)
 have down212:=FirstRest18711.quiet_count_zero smallDown
 have earlyQuiet:=QuietFromCount11.from_two_counts prefixLog [212] north down212
 have exactQuiet : UpperQuiet11.Quiet Left212TwoWord11.early soko1_1.initial [212] dirs state pushes moves outcomes:=earlyQuiet
 have prefixBound:=prefix_energy_le prefixLog suffix [212] (by decide) (by decide)
 have cheapPrefix : energy soko1_1.initial state [212] outcomes<4:=by omega
 obtain ⟨dest,member,tag,rankBound⟩:=Left212TwoWord11.guard_rank exactQuiet
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide) cheapPrefix
 have colors:=SmallRestTopColor11.prefix_colored prefixLog suffix completed cheap rest noRest
 have included:=end_subset_selected prefixLog (by decide) [212] Gate265Transport11.upperOrigins
   (by decide) (by decide) (by decide) (by decide)
 have insideUpper : dest∈Gate265Transport11.upper:=colors (included (by rw [tag];simp))
 change dest∈([212,213,239,265,211,214,264,266]:List Cell) at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact ⟨212,by decide,tag,rankBound⟩
 ·exact ⟨213,by decide,tag,rankBound⟩
 ·exact ⟨239,by decide,tag,rankBound⟩
 ·exact False.elim ((show (265:Cell)∉Gate265Transport11.upper by decide) insideUpper)
 ·exact ⟨211,by decide,tag,rankBound⟩
 ·exact ⟨214,by decide,tag,rankBound⟩
 ·exact False.elim ((show (264:Cell)∉Gate265Transport11.upper by decide) insideUpper)
 ·exact False.elim ((show (266:Cell)∉Gate265Transport11.upper by decide) insideUpper)
#print axioms word
end Owner1007.Left212BeforeRest11
