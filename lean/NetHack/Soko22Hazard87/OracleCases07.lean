import NetHack.Soko22Hazard87.OracleCases06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases700 : List OracleBranch := []
noncomputable def rowCases701 : List OracleBranch := [((.walk 149), d1)]
theorem oracleMember725 : ((.walk 149), d1) ∈ rowCases701 := by
  exact List.mem_cons_self
noncomputable def rowCases702 : List OracleBranch := []
noncomputable def rowCases703 : List OracleBranch := [((.walk 193), d1)]
theorem oracleMember726 : ((.walk 193), d1) ∈ rowCases703 := by
  exact List.mem_cons_self
noncomputable def rowCases704 : List OracleBranch := [((.walk 155), d132764), ((.push 155 (.stay 133)), d102598)]
theorem oracleMember727 : ((.walk 155), d132764) ∈ rowCases704 := by
  exact List.mem_cons_self
theorem oracleMember728 : ((.push 155 (.stay 133)), d102598) ∈ rowCases704 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases705 : List OracleBranch := [((.walk 199), d194333)]
theorem oracleMember729 : ((.walk 199), d194333) ∈ rowCases705 := by
  exact List.mem_cons_self
noncomputable def rowCases706 : List OracleBranch := []
noncomputable def rowCases707 : List OracleBranch := []
noncomputable def rowCases708 : List OracleBranch := [((.walk 156), d139752)]
theorem oracleMember730 : ((.walk 156), d139752) ∈ rowCases708 := by
  exact List.mem_cons_self
noncomputable def rowCases709 : List OracleBranch := []
noncomputable def rowCases710 : List OracleBranch := [((.walk 200), d194337)]
theorem oracleMember731 : ((.walk 200), d194337) ∈ rowCases710 := by
  exact List.mem_cons_self
noncomputable def rowCases711 : List OracleBranch := []
noncomputable def rowCases712 : List OracleBranch := [((.walk 158), d146836), ((.push 158 (.stay 136)), d116753)]
theorem oracleMember732 : ((.walk 158), d146836) ∈ rowCases712 := by
  exact List.mem_cons_self
theorem oracleMember733 : ((.push 158 (.stay 136)), d116753) ∈ rowCases712 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases713 : List OracleBranch := [((.walk 202), d198467), ((.push 202 (.stay 224)), d202307)]
theorem oracleMember734 : ((.walk 202), d198467) ∈ rowCases713 := by
  exact List.mem_cons_self
theorem oracleMember735 : ((.push 202 (.stay 224)), d202307) ∈ rowCases713 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases714 : List OracleBranch := [((.walk 181), d207963), ((.push 181 (.stay 182)), d207966)]
theorem oracleMember736 : ((.walk 181), d207963) ∈ rowCases714 := by
  exact List.mem_cons_self
theorem oracleMember737 : ((.push 181 (.stay 182)), d207966) ∈ rowCases714 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases715 : List OracleBranch := []
noncomputable def rowCases716 : List OracleBranch := [((.walk 159), d169397)]
theorem oracleMember738 : ((.walk 159), d169397) ∈ rowCases716 := by
  exact List.mem_cons_self
noncomputable def rowCases717 : List OracleBranch := [((.walk 157), d146837)]
theorem oracleMember739 : ((.walk 157), d146837) ∈ rowCases717 := by
  exact List.mem_cons_self
noncomputable def rowCases718 : List OracleBranch := []
noncomputable def rowCases719 : List OracleBranch := [((.walk 201), d208035)]
theorem oracleMember740 : ((.walk 201), d208035) ∈ rowCases719 := by
  exact List.mem_cons_self
noncomputable def rowCases720 : List OracleBranch := [((.walk 159), d163444)]
theorem oracleMember741 : ((.walk 159), d163444) ∈ rowCases720 := by
  exact List.mem_cons_self
noncomputable def rowCases721 : List OracleBranch := []
noncomputable def rowCases722 : List OracleBranch := [((.walk 182), d211412)]
theorem oracleMember742 : ((.walk 182), d211412) ∈ rowCases722 := by
  exact List.mem_cons_self
noncomputable def rowCases723 : List OracleBranch := [((.walk 180), d207963)]
theorem oracleMember743 : ((.walk 180), d207963) ∈ rowCases723 := by
  exact List.mem_cons_self
noncomputable def rowCases724 : List OracleBranch := [((.walk 160), d180907)]
theorem oracleMember744 : ((.walk 160), d180907) ∈ rowCases724 := by
  exact List.mem_cons_self
noncomputable def rowCases725 : List OracleBranch := [((.walk 158), d162095)]
theorem oracleMember745 : ((.walk 158), d162095) ∈ rowCases725 := by
  exact List.mem_cons_self
noncomputable def rowCases726 : List OracleBranch := [((.walk 204), d211416)]
theorem oracleMember746 : ((.walk 204), d211416) ∈ rowCases726 := by
  exact List.mem_cons_self
noncomputable def rowCases727 : List OracleBranch := [((.walk 202), d212559)]
theorem oracleMember747 : ((.walk 202), d212559) ∈ rowCases727 := by
  exact List.mem_cons_self
noncomputable def rowCases728 : List OracleBranch := [((.walk 160), d169389), ((.push 160 (.stay 138)), d128487)]
theorem oracleMember748 : ((.walk 160), d169389) ∈ rowCases728 := by
  exact List.mem_cons_self
theorem oracleMember749 : ((.push 160 (.stay 138)), d128487) ∈ rowCases728 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases729 : List OracleBranch := [((.walk 204), d211415), ((.push 204 (.stay 226)), d216471)]
theorem oracleMember750 : ((.walk 204), d211415) ∈ rowCases729 := by
  exact List.mem_cons_self
theorem oracleMember751 : ((.push 204 (.stay 226)), d216471) ∈ rowCases729 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases730 : List OracleBranch := []
noncomputable def rowCases731 : List OracleBranch := [((.walk 181), d211412), ((.push 181 (.stay 180)), d207966)]
theorem oracleMember752 : ((.walk 181), d211412) ∈ rowCases731 := by
  exact List.mem_cons_self
theorem oracleMember753 : ((.push 181 (.stay 180)), d207966) ∈ rowCases731 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases732 : List OracleBranch := [((.walk 161), d187678)]
theorem oracleMember754 : ((.walk 161), d187678) ∈ rowCases732 := by
  exact List.mem_cons_self
noncomputable def rowCases733 : List OracleBranch := [((.walk 159), d169391)]
theorem oracleMember755 : ((.walk 159), d169391) ∈ rowCases733 := by
  exact List.mem_cons_self
noncomputable def rowCases734 : List OracleBranch := []
noncomputable def rowCases735 : List OracleBranch := []
noncomputable def rowCases736 : List OracleBranch := [((.walk 162), d187679)]
theorem oracleMember756 : ((.walk 162), d187679) ∈ rowCases736 := by
  exact List.mem_cons_self
noncomputable def rowCases737 : List OracleBranch := []
noncomputable def rowCases738 : List OracleBranch := [((.walk 185), d225586), ((.push 185 (.stay 186)), d225589)]
theorem oracleMember757 : ((.walk 185), d225586) ∈ rowCases738 := by
  exact List.mem_cons_self
theorem oracleMember758 : ((.push 185 (.stay 186)), d225589) ∈ rowCases738 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases739 : List OracleBranch := []
noncomputable def rowCases740 : List OracleBranch := [((.walk 163), d192716)]
theorem oracleMember759 : ((.walk 163), d192716) ∈ rowCases740 := by
  exact List.mem_cons_self
noncomputable def rowCases741 : List OracleBranch := [((.walk 161), d187676)]
theorem oracleMember760 : ((.walk 161), d187676) ∈ rowCases741 := by
  exact List.mem_cons_self
noncomputable def rowCases742 : List OracleBranch := []
noncomputable def rowCases743 : List OracleBranch := []
noncomputable def rowCases744 : List OracleBranch := [((.walk 163), d190593), ((.push 163 (.stay 141)), d130390)]
theorem oracleMember761 : ((.walk 163), d190593) ∈ rowCases744 := by
  exact List.mem_cons_self
theorem oracleMember762 : ((.push 163 (.stay 141)), d130390) ∈ rowCases744 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases745 : List OracleBranch := []
noncomputable def rowCases746 : List OracleBranch := [((.walk 186), d227682)]
theorem oracleMember763 : ((.walk 186), d227682) ∈ rowCases746 := by
  exact List.mem_cons_self
noncomputable def rowCases747 : List OracleBranch := [((.walk 184), d225586)]
theorem oracleMember764 : ((.walk 184), d225586) ∈ rowCases747 := by
  exact List.mem_cons_self
noncomputable def rowCases748 : List OracleBranch := [((.walk 164), d194332)]
theorem oracleMember765 : ((.walk 164), d194332) ∈ rowCases748 := by
  exact List.mem_cons_self
noncomputable def rowCases749 : List OracleBranch := [((.walk 162), d188524)]
theorem oracleMember766 : ((.walk 162), d188524) ∈ rowCases749 := by
  exact List.mem_cons_self
noncomputable def rowCases750 : List OracleBranch := []
noncomputable def rowCases751 : List OracleBranch := []
noncomputable def rowCases752 : List OracleBranch := [((.walk 164), d192717)]
theorem oracleMember767 : ((.walk 164), d192717) ∈ rowCases752 := by
  exact List.mem_cons_self
noncomputable def rowCases753 : List OracleBranch := []
noncomputable def rowCases754 : List OracleBranch := []
noncomputable def rowCases755 : List OracleBranch := [((.walk 185), d227682), ((.push 185 (.stay 184)), d225589)]
theorem oracleMember768 : ((.walk 185), d227682) ∈ rowCases755 := by
  exact List.mem_cons_self
theorem oracleMember769 : ((.push 185 (.stay 184)), d225589) ∈ rowCases755 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases756 : List OracleBranch := []
noncomputable def rowCases757 : List OracleBranch := [((.walk 163), d192712)]
theorem oracleMember770 : ((.walk 163), d192712) ∈ rowCases757 := by
  exact List.mem_cons_self
noncomputable def rowCases758 : List OracleBranch := []
noncomputable def rowCases759 : List OracleBranch := []
noncomputable def rowCases760 : List OracleBranch := [((.walk 166), d1), ((.push 166 (.stay 144)), d0)]
theorem oracleMember771 : ((.walk 166), d1) ∈ rowCases760 := by
  exact List.mem_cons_self
theorem oracleMember772 : ((.push 166 (.stay 144)), d0) ∈ rowCases760 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases761 : List OracleBranch := [((.walk 210), d1)]
theorem oracleMember773 : ((.walk 210), d1) ∈ rowCases761 := by
  exact List.mem_cons_self
noncomputable def rowCases762 : List OracleBranch := [((.walk 189), d1), ((.push 189 (.stay 190)), d0)]
theorem oracleMember774 : ((.walk 189), d1) ∈ rowCases762 := by
  exact List.mem_cons_self
theorem oracleMember775 : ((.push 189 (.stay 190)), d0) ∈ rowCases762 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases763 : List OracleBranch := []
noncomputable def rowCases764 : List OracleBranch := [((.walk 167), d1)]
theorem oracleMember776 : ((.walk 167), d1) ∈ rowCases764 := by
  exact List.mem_cons_self
noncomputable def rowCases765 : List OracleBranch := []
noncomputable def rowCases766 : List OracleBranch := [((.walk 211), d1)]
theorem oracleMember777 : ((.walk 211), d1) ∈ rowCases766 := by
  exact List.mem_cons_self
noncomputable def rowCases767 : List OracleBranch := []
noncomputable def rowCases768 : List OracleBranch := [((.walk 167), d1), ((.push 167 (.stay 145)), d0)]
theorem oracleMember778 : ((.walk 167), d1) ∈ rowCases768 := by
  exact List.mem_cons_self
theorem oracleMember779 : ((.push 167 (.stay 145)), d0) ∈ rowCases768 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases769 : List OracleBranch := [((.walk 211), d1)]
theorem oracleMember780 : ((.walk 211), d1) ∈ rowCases769 := by
  exact List.mem_cons_self
noncomputable def rowCases770 : List OracleBranch := [((.walk 190), d1), ((.push 190 (.stay 191)), d0)]
theorem oracleMember781 : ((.walk 190), d1) ∈ rowCases770 := by
  exact List.mem_cons_self
theorem oracleMember782 : ((.push 190 (.stay 191)), d0) ∈ rowCases770 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases771 : List OracleBranch := [((.walk 188), d1)]
theorem oracleMember783 : ((.walk 188), d1) ∈ rowCases771 := by
  exact List.mem_cons_self
noncomputable def rowCases772 : List OracleBranch := [((.walk 168), d1)]
theorem oracleMember784 : ((.walk 168), d1) ∈ rowCases772 := by
  exact List.mem_cons_self
noncomputable def rowCases773 : List OracleBranch := [((.walk 166), d1)]
theorem oracleMember785 : ((.walk 166), d1) ∈ rowCases773 := by
  exact List.mem_cons_self
noncomputable def rowCases774 : List OracleBranch := [((.walk 212), d1)]
theorem oracleMember786 : ((.walk 212), d1) ∈ rowCases774 := by
  exact List.mem_cons_self
noncomputable def rowCases775 : List OracleBranch := [((.walk 210), d1)]
theorem oracleMember787 : ((.walk 210), d1) ∈ rowCases775 := by
  exact List.mem_cons_self
noncomputable def rowCases776 : List OracleBranch := [((.walk 168), d1), ((.push 168 (.stay 146)), d0)]
theorem oracleMember788 : ((.walk 168), d1) ∈ rowCases776 := by
  exact List.mem_cons_self
theorem oracleMember789 : ((.push 168 (.stay 146)), d0) ∈ rowCases776 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases777 : List OracleBranch := [((.walk 212), d1)]
theorem oracleMember790 : ((.walk 212), d1) ∈ rowCases777 := by
  exact List.mem_cons_self
noncomputable def rowCases778 : List OracleBranch := [((.walk 191), d1), ((.push 191 (.stay 192)), d0)]
theorem oracleMember791 : ((.walk 191), d1) ∈ rowCases778 := by
  exact List.mem_cons_self
theorem oracleMember792 : ((.push 191 (.stay 192)), d0) ∈ rowCases778 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases779 : List OracleBranch := [((.walk 189), d1), ((.push 189 (.stay 188)), d0)]
theorem oracleMember793 : ((.walk 189), d1) ∈ rowCases779 := by
  exact List.mem_cons_self
theorem oracleMember794 : ((.push 189 (.stay 188)), d0) ∈ rowCases779 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases780 : List OracleBranch := [((.walk 169), d1)]
theorem oracleMember795 : ((.walk 169), d1) ∈ rowCases780 := by
  exact List.mem_cons_self
noncomputable def rowCases781 : List OracleBranch := [((.walk 167), d1)]
theorem oracleMember796 : ((.walk 167), d1) ∈ rowCases781 := by
  exact List.mem_cons_self
noncomputable def rowCases782 : List OracleBranch := [((.walk 213), d1)]
theorem oracleMember797 : ((.walk 213), d1) ∈ rowCases782 := by
  exact List.mem_cons_self
noncomputable def rowCases783 : List OracleBranch := [((.walk 211), d1)]
theorem oracleMember798 : ((.walk 211), d1) ∈ rowCases783 := by
  exact List.mem_cons_self
noncomputable def rowCases784 : List OracleBranch := [((.walk 169), d1), ((.push 169 (.stay 147)), d0)]
theorem oracleMember799 : ((.walk 169), d1) ∈ rowCases784 := by
  exact List.mem_cons_self
theorem oracleMember800 : ((.push 169 (.stay 147)), d0) ∈ rowCases784 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases785 : List OracleBranch := [((.walk 213), d1)]
theorem oracleMember801 : ((.walk 213), d1) ∈ rowCases785 := by
  exact List.mem_cons_self
noncomputable def rowCases786 : List OracleBranch := [((.walk 192), d1), ((.push 192 (.stay 193)), d0)]
theorem oracleMember802 : ((.walk 192), d1) ∈ rowCases786 := by
  exact List.mem_cons_self
theorem oracleMember803 : ((.push 192 (.stay 193)), d0) ∈ rowCases786 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases787 : List OracleBranch := [((.walk 190), d1), ((.push 190 (.stay 189)), d0)]
theorem oracleMember804 : ((.walk 190), d1) ∈ rowCases787 := by
  exact List.mem_cons_self
theorem oracleMember805 : ((.push 190 (.stay 189)), d0) ∈ rowCases787 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases788 : List OracleBranch := [((.walk 170), d1)]
theorem oracleMember806 : ((.walk 170), d1) ∈ rowCases788 := by
  exact List.mem_cons_self
noncomputable def rowCases789 : List OracleBranch := [((.walk 168), d1)]
theorem oracleMember807 : ((.walk 168), d1) ∈ rowCases789 := by
  exact List.mem_cons_self
noncomputable def rowCases790 : List OracleBranch := [((.walk 214), d1)]
theorem oracleMember808 : ((.walk 214), d1) ∈ rowCases790 := by
  exact List.mem_cons_self
noncomputable def rowCases791 : List OracleBranch := [((.walk 212), d1)]
theorem oracleMember809 : ((.walk 212), d1) ∈ rowCases791 := by
  exact List.mem_cons_self
noncomputable def rowCases792 : List OracleBranch := [((.walk 170), d1), ((.push 170 (.stay 148)), d0)]
theorem oracleMember810 : ((.walk 170), d1) ∈ rowCases792 := by
  exact List.mem_cons_self
theorem oracleMember811 : ((.push 170 (.stay 148)), d0) ∈ rowCases792 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases793 : List OracleBranch := [((.walk 214), d1)]
theorem oracleMember812 : ((.walk 214), d1) ∈ rowCases793 := by
  exact List.mem_cons_self
noncomputable def rowCases794 : List OracleBranch := [((.walk 193), d1), ((.push 193 (.stay 194)), d0)]
theorem oracleMember813 : ((.walk 193), d1) ∈ rowCases794 := by
  exact List.mem_cons_self
theorem oracleMember814 : ((.push 193 (.stay 194)), d0) ∈ rowCases794 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases795 : List OracleBranch := [((.walk 191), d1), ((.push 191 (.stay 190)), d0)]
theorem oracleMember815 : ((.walk 191), d1) ∈ rowCases795 := by
  exact List.mem_cons_self
theorem oracleMember816 : ((.push 191 (.stay 190)), d0) ∈ rowCases795 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases796 : List OracleBranch := [((.walk 171), d1)]
theorem oracleMember817 : ((.walk 171), d1) ∈ rowCases796 := by
  exact List.mem_cons_self
noncomputable def rowCases797 : List OracleBranch := [((.walk 169), d1)]
theorem oracleMember818 : ((.walk 169), d1) ∈ rowCases797 := by
  exact List.mem_cons_self
noncomputable def rowCases798 : List OracleBranch := [((.walk 215), d1)]
theorem oracleMember819 : ((.walk 215), d1) ∈ rowCases798 := by
  exact List.mem_cons_self
noncomputable def rowCases799 : List OracleBranch := [((.walk 213), d1)]
theorem oracleMember820 : ((.walk 213), d1) ∈ rowCases799 := by
  exact List.mem_cons_self
end NetHack.Soko22Hazard87
