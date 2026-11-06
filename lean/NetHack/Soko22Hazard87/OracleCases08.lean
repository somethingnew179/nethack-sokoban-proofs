import NetHack.Soko22Hazard87.OracleCases07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases800 : List OracleBranch := [((.walk 171), d1), ((.push 171 (.stay 149)), d0)]
theorem oracleMember821 : ((.walk 171), d1) ∈ rowCases800 := by
  exact List.mem_cons_self
theorem oracleMember822 : ((.push 171 (.stay 149)), d0) ∈ rowCases800 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases801 : List OracleBranch := [((.walk 215), d1)]
theorem oracleMember823 : ((.walk 215), d1) ∈ rowCases801 := by
  exact List.mem_cons_self
noncomputable def rowCases802 : List OracleBranch := [((.walk 194), d1)]
theorem oracleMember824 : ((.walk 194), d1) ∈ rowCases802 := by
  exact List.mem_cons_self
noncomputable def rowCases803 : List OracleBranch := [((.walk 192), d1), ((.push 192 (.stay 191)), d0)]
theorem oracleMember825 : ((.walk 192), d1) ∈ rowCases803 := by
  exact List.mem_cons_self
theorem oracleMember826 : ((.push 192 (.stay 191)), d0) ∈ rowCases803 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases804 : List OracleBranch := [((.walk 172), d1)]
theorem oracleMember827 : ((.walk 172), d1) ∈ rowCases804 := by
  exact List.mem_cons_self
noncomputable def rowCases805 : List OracleBranch := [((.walk 170), d1)]
theorem oracleMember828 : ((.walk 170), d1) ∈ rowCases805 := by
  exact List.mem_cons_self
noncomputable def rowCases806 : List OracleBranch := [((.walk 216), d1)]
theorem oracleMember829 : ((.walk 216), d1) ∈ rowCases806 := by
  exact List.mem_cons_self
noncomputable def rowCases807 : List OracleBranch := [((.walk 214), d1)]
theorem oracleMember830 : ((.walk 214), d1) ∈ rowCases807 := by
  exact List.mem_cons_self
noncomputable def rowCases808 : List OracleBranch := [((.walk 172), d1), ((.push 172 (.stay 150)), d0)]
theorem oracleMember831 : ((.walk 172), d1) ∈ rowCases808 := by
  exact List.mem_cons_self
theorem oracleMember832 : ((.push 172 (.stay 150)), d0) ∈ rowCases808 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases809 : List OracleBranch := [((.walk 216), d1)]
theorem oracleMember833 : ((.walk 216), d1) ∈ rowCases809 := by
  exact List.mem_cons_self
noncomputable def rowCases810 : List OracleBranch := []
noncomputable def rowCases811 : List OracleBranch := [((.walk 193), d1), ((.push 193 (.stay 192)), d0)]
theorem oracleMember834 : ((.walk 193), d1) ∈ rowCases811 := by
  exact List.mem_cons_self
theorem oracleMember835 : ((.push 193 (.stay 192)), d0) ∈ rowCases811 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases812 : List OracleBranch := []
noncomputable def rowCases813 : List OracleBranch := [((.walk 171), d1)]
theorem oracleMember836 : ((.walk 171), d1) ∈ rowCases813 := by
  exact List.mem_cons_self
noncomputable def rowCases814 : List OracleBranch := []
noncomputable def rowCases815 : List OracleBranch := [((.walk 215), d1)]
theorem oracleMember837 : ((.walk 215), d1) ∈ rowCases815 := by
  exact List.mem_cons_self
noncomputable def rowCases816 : List OracleBranch := [((.walk 177), d194333), ((.push 177 (.stay 155)), d132769)]
theorem oracleMember838 : ((.walk 177), d194333) ∈ rowCases816 := by
  exact List.mem_cons_self
theorem oracleMember839 : ((.push 177 (.stay 155)), d132769) ∈ rowCases816 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases817 : List OracleBranch := []
noncomputable def rowCases818 : List OracleBranch := [((.walk 200), d194336), ((.push 200 (.stay 201)), d227687)]
theorem oracleMember840 : ((.walk 200), d194336) ∈ rowCases818 := by
  exact List.mem_cons_self
theorem oracleMember841 : ((.push 200 (.stay 201)), d227687) ∈ rowCases818 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases819 : List OracleBranch := []
noncomputable def rowCases820 : List OracleBranch := []
noncomputable def rowCases821 : List OracleBranch := []
noncomputable def rowCases822 : List OracleBranch := []
noncomputable def rowCases823 : List OracleBranch := []
noncomputable def rowCases824 : List OracleBranch := []
noncomputable def rowCases825 : List OracleBranch := []
noncomputable def rowCases826 : List OracleBranch := [((.walk 201), d231166), ((.push 201 (.stay 202)), d231382)]
theorem oracleMember842 : ((.walk 201), d231166) ∈ rowCases826 := by
  exact List.mem_cons_self
theorem oracleMember843 : ((.push 201 (.stay 202)), d231382) ∈ rowCases826 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases827 : List OracleBranch := [((.walk 199), d194336)]
theorem oracleMember844 : ((.walk 199), d194336) ∈ rowCases827 := by
  exact List.mem_cons_self
noncomputable def rowCases828 : List OracleBranch := []
noncomputable def rowCases829 : List OracleBranch := [((.walk 177), d194337)]
theorem oracleMember845 : ((.walk 177), d194337) ∈ rowCases829 := by
  exact List.mem_cons_self
noncomputable def rowCases830 : List OracleBranch := [((.walk 223), d236583)]
theorem oracleMember846 : ((.walk 223), d236583) ∈ rowCases830 := by
  exact List.mem_cons_self
noncomputable def rowCases831 : List OracleBranch := []
noncomputable def rowCases832 : List OracleBranch := []
noncomputable def rowCases833 : List OracleBranch := [((.walk 223), d236582), ((.push 223 (.stay 245)), d239127)]
theorem oracleMember847 : ((.walk 223), d236582) ∈ rowCases833 := by
  exact List.mem_cons_self
theorem oracleMember848 : ((.push 223 (.stay 245)), d239127) ∈ rowCases833 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases834 : List OracleBranch := [((.walk 202), d208034)]
theorem oracleMember849 : ((.walk 202), d208034) ∈ rowCases834 := by
  exact List.mem_cons_self
noncomputable def rowCases835 : List OracleBranch := [((.walk 200), d231166), ((.push 200 (.stay 199)), d227687)]
theorem oracleMember850 : ((.walk 200), d231166) ∈ rowCases835 := by
  exact List.mem_cons_self
theorem oracleMember851 : ((.push 200 (.stay 199)), d227687) ∈ rowCases835 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases836 : List OracleBranch := [((.walk 180), d208035)]
theorem oracleMember852 : ((.walk 180), d208035) ∈ rowCases836 := by
  exact List.mem_cons_self
noncomputable def rowCases837 : List OracleBranch := []
noncomputable def rowCases838 : List OracleBranch := [((.walk 224), d241832)]
theorem oracleMember853 : ((.walk 224), d241832) ∈ rowCases838 := by
  exact List.mem_cons_self
noncomputable def rowCases839 : List OracleBranch := []
noncomputable def rowCases840 : List OracleBranch := [((.walk 180), d198467), ((.push 180 (.stay 158)), d152855)]
theorem oracleMember854 : ((.walk 180), d198467) ∈ rowCases840 := by
  exact List.mem_cons_self
theorem oracleMember855 : ((.push 180 (.stay 158)), d152855) ∈ rowCases840 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases841 : List OracleBranch := [((.walk 224), d251389), ((.push 224 (.stay 246)), d253272)]
theorem oracleMember856 : ((.walk 224), d251389) ∈ rowCases841 := by
  exact List.mem_cons_self
theorem oracleMember857 : ((.push 224 (.stay 246)), d253272) ∈ rowCases841 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases842 : List OracleBranch := []
noncomputable def rowCases843 : List OracleBranch := [((.walk 201), d208034), ((.push 201 (.stay 200)), d231382)]
theorem oracleMember858 : ((.walk 201), d208034) ∈ rowCases843 := by
  exact List.mem_cons_self
theorem oracleMember859 : ((.push 201 (.stay 200)), d231382) ∈ rowCases843 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases844 : List OracleBranch := [((.walk 181), d212559)]
theorem oracleMember860 : ((.walk 181), d212559) ∈ rowCases844 := by
  exact List.mem_cons_self
noncomputable def rowCases845 : List OracleBranch := []
noncomputable def rowCases846 : List OracleBranch := [((.walk 225), d261986)]
theorem oracleMember861 : ((.walk 225), d261986) ∈ rowCases846 := by
  exact List.mem_cons_self
noncomputable def rowCases847 : List OracleBranch := [((.walk 223), d266246)]
theorem oracleMember862 : ((.walk 223), d266246) ∈ rowCases847 := by
  exact List.mem_cons_self
noncomputable def rowCases848 : List OracleBranch := [((.walk 182), d211415), ((.push 182 (.stay 160)), d171300)]
theorem oracleMember863 : ((.walk 182), d211415) ∈ rowCases848 := by
  exact List.mem_cons_self
theorem oracleMember864 : ((.push 182 (.stay 160)), d171300) ∈ rowCases848 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases849 : List OracleBranch := [((.walk 226), d267844), ((.push 226 (.stay 248)), d271212)]
theorem oracleMember865 : ((.walk 226), d267844) ∈ rowCases849 := by
  exact List.mem_cons_self
theorem oracleMember866 : ((.push 226 (.stay 248)), d271212) ∈ rowCases849 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases850 : List OracleBranch := []
noncomputable def rowCases851 : List OracleBranch := []
noncomputable def rowCases852 : List OracleBranch := []
noncomputable def rowCases853 : List OracleBranch := [((.walk 181), d211416)]
theorem oracleMember867 : ((.walk 181), d211416) ∈ rowCases853 := by
  exact List.mem_cons_self
noncomputable def rowCases854 : List OracleBranch := []
noncomputable def rowCases855 : List OracleBranch := [((.walk 225), d277740)]
theorem oracleMember868 : ((.walk 225), d277740) ∈ rowCases855 := by
  exact List.mem_cons_self
noncomputable def rowCases856 : List OracleBranch := [((.walk 188), d1), ((.push 188 (.stay 166)), d0)]
theorem oracleMember869 : ((.walk 188), d1) ∈ rowCases856 := by
  exact List.mem_cons_self
theorem oracleMember870 : ((.push 188 (.stay 166)), d0) ∈ rowCases856 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases857 : List OracleBranch := []
noncomputable def rowCases858 : List OracleBranch := [((.walk 211), d1), ((.push 211 (.stay 212)), d0)]
theorem oracleMember871 : ((.walk 211), d1) ∈ rowCases858 := by
  exact List.mem_cons_self
theorem oracleMember872 : ((.push 211 (.stay 212)), d0) ∈ rowCases858 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases859 : List OracleBranch := []
noncomputable def rowCases860 : List OracleBranch := [((.walk 189), d1)]
theorem oracleMember873 : ((.walk 189), d1) ∈ rowCases860 := by
  exact List.mem_cons_self
noncomputable def rowCases861 : List OracleBranch := []
noncomputable def rowCases862 : List OracleBranch := []
noncomputable def rowCases863 : List OracleBranch := []
noncomputable def rowCases864 : List OracleBranch := [((.walk 189), d1), ((.push 189 (.stay 167)), d0)]
theorem oracleMember874 : ((.walk 189), d1) ∈ rowCases864 := by
  exact List.mem_cons_self
theorem oracleMember875 : ((.push 189 (.stay 167)), d0) ∈ rowCases864 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases865 : List OracleBranch := []
noncomputable def rowCases866 : List OracleBranch := [((.walk 212), d1), ((.push 212 (.stay 213)), d0)]
theorem oracleMember876 : ((.walk 212), d1) ∈ rowCases866 := by
  exact List.mem_cons_self
theorem oracleMember877 : ((.push 212 (.stay 213)), d0) ∈ rowCases866 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases867 : List OracleBranch := [((.walk 210), d1)]
theorem oracleMember878 : ((.walk 210), d1) ∈ rowCases867 := by
  exact List.mem_cons_self
noncomputable def rowCases868 : List OracleBranch := [((.walk 190), d1)]
theorem oracleMember879 : ((.walk 190), d1) ∈ rowCases868 := by
  exact List.mem_cons_self
noncomputable def rowCases869 : List OracleBranch := [((.walk 188), d1)]
theorem oracleMember880 : ((.walk 188), d1) ∈ rowCases869 := by
  exact List.mem_cons_self
noncomputable def rowCases870 : List OracleBranch := []
noncomputable def rowCases871 : List OracleBranch := []
noncomputable def rowCases872 : List OracleBranch := [((.walk 190), d1), ((.push 190 (.stay 168)), d0)]
theorem oracleMember881 : ((.walk 190), d1) ∈ rowCases872 := by
  exact List.mem_cons_self
theorem oracleMember882 : ((.push 190 (.stay 168)), d0) ∈ rowCases872 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases873 : List OracleBranch := []
noncomputable def rowCases874 : List OracleBranch := [((.walk 213), d1), ((.push 213 (.stay 214)), d0)]
theorem oracleMember883 : ((.walk 213), d1) ∈ rowCases874 := by
  exact List.mem_cons_self
theorem oracleMember884 : ((.push 213 (.stay 214)), d0) ∈ rowCases874 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases875 : List OracleBranch := [((.walk 211), d1), ((.push 211 (.stay 210)), d0)]
theorem oracleMember885 : ((.walk 211), d1) ∈ rowCases875 := by
  exact List.mem_cons_self
theorem oracleMember886 : ((.push 211 (.stay 210)), d0) ∈ rowCases875 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases876 : List OracleBranch := [((.walk 191), d1)]
theorem oracleMember887 : ((.walk 191), d1) ∈ rowCases876 := by
  exact List.mem_cons_self
noncomputable def rowCases877 : List OracleBranch := [((.walk 189), d1)]
theorem oracleMember888 : ((.walk 189), d1) ∈ rowCases877 := by
  exact List.mem_cons_self
noncomputable def rowCases878 : List OracleBranch := []
noncomputable def rowCases879 : List OracleBranch := []
noncomputable def rowCases880 : List OracleBranch := [((.walk 191), d1), ((.push 191 (.stay 169)), d0)]
theorem oracleMember889 : ((.walk 191), d1) ∈ rowCases880 := by
  exact List.mem_cons_self
theorem oracleMember890 : ((.push 191 (.stay 169)), d0) ∈ rowCases880 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases881 : List OracleBranch := []
noncomputable def rowCases882 : List OracleBranch := [((.walk 214), d1), ((.push 214 (.stay 215)), d0)]
theorem oracleMember891 : ((.walk 214), d1) ∈ rowCases882 := by
  exact List.mem_cons_self
theorem oracleMember892 : ((.push 214 (.stay 215)), d0) ∈ rowCases882 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases883 : List OracleBranch := [((.walk 212), d1), ((.push 212 (.stay 211)), d0)]
theorem oracleMember893 : ((.walk 212), d1) ∈ rowCases883 := by
  exact List.mem_cons_self
theorem oracleMember894 : ((.push 212 (.stay 211)), d0) ∈ rowCases883 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases884 : List OracleBranch := [((.walk 192), d1)]
theorem oracleMember895 : ((.walk 192), d1) ∈ rowCases884 := by
  exact List.mem_cons_self
noncomputable def rowCases885 : List OracleBranch := [((.walk 190), d1)]
theorem oracleMember896 : ((.walk 190), d1) ∈ rowCases885 := by
  exact List.mem_cons_self
noncomputable def rowCases886 : List OracleBranch := []
noncomputable def rowCases887 : List OracleBranch := []
noncomputable def rowCases888 : List OracleBranch := [((.walk 192), d1), ((.push 192 (.stay 170)), d0)]
theorem oracleMember897 : ((.walk 192), d1) ∈ rowCases888 := by
  exact List.mem_cons_self
theorem oracleMember898 : ((.push 192 (.stay 170)), d0) ∈ rowCases888 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases889 : List OracleBranch := []
noncomputable def rowCases890 : List OracleBranch := [((.walk 215), d1), ((.push 215 (.stay 216)), d0)]
theorem oracleMember899 : ((.walk 215), d1) ∈ rowCases890 := by
  exact List.mem_cons_self
theorem oracleMember900 : ((.push 215 (.stay 216)), d0) ∈ rowCases890 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases891 : List OracleBranch := [((.walk 213), d1), ((.push 213 (.stay 212)), d0)]
theorem oracleMember901 : ((.walk 213), d1) ∈ rowCases891 := by
  exact List.mem_cons_self
theorem oracleMember902 : ((.push 213 (.stay 212)), d0) ∈ rowCases891 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases892 : List OracleBranch := [((.walk 193), d1)]
theorem oracleMember903 : ((.walk 193), d1) ∈ rowCases892 := by
  exact List.mem_cons_self
noncomputable def rowCases893 : List OracleBranch := [((.walk 191), d1)]
theorem oracleMember904 : ((.walk 191), d1) ∈ rowCases893 := by
  exact List.mem_cons_self
noncomputable def rowCases894 : List OracleBranch := []
noncomputable def rowCases895 : List OracleBranch := []
noncomputable def rowCases896 : List OracleBranch := [((.walk 193), d1), ((.push 193 (.stay 171)), d0)]
theorem oracleMember905 : ((.walk 193), d1) ∈ rowCases896 := by
  exact List.mem_cons_self
theorem oracleMember906 : ((.push 193 (.stay 171)), d0) ∈ rowCases896 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases897 : List OracleBranch := []
noncomputable def rowCases898 : List OracleBranch := [((.walk 216), d1)]
theorem oracleMember907 : ((.walk 216), d1) ∈ rowCases898 := by
  exact List.mem_cons_self
noncomputable def rowCases899 : List OracleBranch := [((.walk 214), d1), ((.push 214 (.stay 213)), d0)]
theorem oracleMember908 : ((.walk 214), d1) ∈ rowCases899 := by
  exact List.mem_cons_self
theorem oracleMember909 : ((.push 214 (.stay 213)), d0) ∈ rowCases899 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
end NetHack.Soko22Hazard87
