import NetHack.Soko22Hazard87.OracleCases00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases100 : List OracleBranch := []
noncomputable def rowCases101 : List OracleBranch := [((.walk 29), d56764)]
theorem oracleMember87 : ((.walk 29), d56764) ∈ rowCases101 := by
  exact List.mem_cons_self
noncomputable def rowCases102 : List OracleBranch := []
noncomputable def rowCases103 : List OracleBranch := [((.walk 73), d67300)]
theorem oracleMember88 : ((.walk 73), d67300) ∈ rowCases103 := by
  exact List.mem_cons_self
noncomputable def rowCases104 : List OracleBranch := [((.walk 45), d57571)]
theorem oracleMember89 : ((.walk 45), d57571) ∈ rowCases104 := by
  exact List.mem_cons_self
noncomputable def rowCases105 : List OracleBranch := [((.walk 89), d67301), ((.push 89 (.stay 111)), d67924)]
theorem oracleMember90 : ((.walk 89), d67301) ∈ rowCases105 := by
  exact List.mem_cons_self
theorem oracleMember91 : ((.push 89 (.stay 111)), d67924) ∈ rowCases105 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases106 : List OracleBranch := []
noncomputable def rowCases107 : List OracleBranch := []
noncomputable def rowCases108 : List OracleBranch := [((.walk 46), d58745)]
theorem oracleMember92 : ((.walk 46), d58745) ∈ rowCases108 := by
  exact List.mem_cons_self
noncomputable def rowCases109 : List OracleBranch := []
noncomputable def rowCases110 : List OracleBranch := [((.walk 90), d68223)]
theorem oracleMember93 : ((.walk 90), d68223) ∈ rowCases110 := by
  exact List.mem_cons_self
noncomputable def rowCases111 : List OracleBranch := []
noncomputable def rowCases112 : List OracleBranch := [((.walk 47), d58432), ((.push 47 (.stay 25)), d53870)]
theorem oracleMember94 : ((.walk 47), d58432) ∈ rowCases112 := by
  exact List.mem_cons_self
theorem oracleMember95 : ((.push 47 (.stay 25)), d53870) ∈ rowCases112 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases113 : List OracleBranch := [((.walk 91), d68751), ((.push 91 (.stay 113)), d70148)]
theorem oracleMember96 : ((.walk 91), d68751) ∈ rowCases113 := by
  exact List.mem_cons_self
theorem oracleMember97 : ((.push 91 (.stay 113)), d70148) ∈ rowCases113 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases114 : List OracleBranch := [((.walk 70), d61358), ((.push 70 (.stay 71)), d72603)]
theorem oracleMember98 : ((.walk 70), d61358) ∈ rowCases114 := by
  exact List.mem_cons_self
theorem oracleMember99 : ((.push 70 (.stay 71)), d72603) ∈ rowCases114 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases115 : List OracleBranch := []
noncomputable def rowCases116 : List OracleBranch := [((.walk 48), d62827)]
theorem oracleMember100 : ((.walk 48), d62827) ∈ rowCases116 := by
  exact List.mem_cons_self
noncomputable def rowCases117 : List OracleBranch := [((.walk 46), d58433)]
theorem oracleMember101 : ((.walk 46), d58433) ∈ rowCases117 := by
  exact List.mem_cons_self
noncomputable def rowCases118 : List OracleBranch := []
noncomputable def rowCases119 : List OracleBranch := [((.walk 90), d73191)]
theorem oracleMember102 : ((.walk 90), d73191) ∈ rowCases119 := by
  exact List.mem_cons_self
noncomputable def rowCases120 : List OracleBranch := [((.walk 48), d61807)]
theorem oracleMember103 : ((.walk 48), d61807) ∈ rowCases120 := by
  exact List.mem_cons_self
noncomputable def rowCases121 : List OracleBranch := []
noncomputable def rowCases122 : List OracleBranch := [((.walk 71), d62374)]
theorem oracleMember104 : ((.walk 71), d62374) ∈ rowCases122 := by
  exact List.mem_cons_self
noncomputable def rowCases123 : List OracleBranch := [((.walk 69), d61358)]
theorem oracleMember105 : ((.walk 69), d61358) ∈ rowCases123 := by
  exact List.mem_cons_self
noncomputable def rowCases124 : List OracleBranch := [((.walk 49), d64542)]
theorem oracleMember106 : ((.walk 49), d64542) ∈ rowCases124 := by
  exact List.mem_cons_self
noncomputable def rowCases125 : List OracleBranch := [((.walk 47), d61360)]
theorem oracleMember107 : ((.walk 47), d61360) ∈ rowCases125 := by
  exact List.mem_cons_self
noncomputable def rowCases126 : List OracleBranch := [((.walk 93), d73493)]
theorem oracleMember108 : ((.walk 93), d73493) ∈ rowCases126 := by
  exact List.mem_cons_self
noncomputable def rowCases127 : List OracleBranch := [((.walk 91), d73495)]
theorem oracleMember109 : ((.walk 91), d73495) ∈ rowCases127 := by
  exact List.mem_cons_self
noncomputable def rowCases128 : List OracleBranch := [((.walk 49), d62934), ((.push 49 (.stay 27)), d54981)]
theorem oracleMember110 : ((.walk 49), d62934) ∈ rowCases128 := by
  exact List.mem_cons_self
theorem oracleMember111 : ((.push 49 (.stay 27)), d54981) ∈ rowCases128 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases129 : List OracleBranch := [((.walk 93), d73492), ((.push 93 (.stay 115)), d73777)]
theorem oracleMember112 : ((.walk 93), d73492) ∈ rowCases129 := by
  exact List.mem_cons_self
theorem oracleMember113 : ((.push 93 (.stay 115)), d73777) ∈ rowCases129 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases130 : List OracleBranch := []
noncomputable def rowCases131 : List OracleBranch := [((.walk 70), d62374), ((.push 70 (.stay 69)), d72603)]
theorem oracleMember114 : ((.walk 70), d62374) ∈ rowCases131 := by
  exact List.mem_cons_self
theorem oracleMember115 : ((.push 70 (.stay 69)), d72603) ∈ rowCases131 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases132 : List OracleBranch := [((.walk 50), d64965)]
theorem oracleMember116 : ((.walk 50), d64965) ∈ rowCases132 := by
  exact List.mem_cons_self
noncomputable def rowCases133 : List OracleBranch := [((.walk 48), d62376)]
theorem oracleMember117 : ((.walk 48), d62376) ∈ rowCases133 := by
  exact List.mem_cons_self
noncomputable def rowCases134 : List OracleBranch := [((.walk 94), d74039)]
theorem oracleMember118 : ((.walk 94), d74039) ∈ rowCases134 := by
  exact List.mem_cons_self
noncomputable def rowCases135 : List OracleBranch := []
noncomputable def rowCases136 : List OracleBranch := [((.walk 51), d64793), ((.push 51 (.stay 29)), d56153)]
theorem oracleMember119 : ((.walk 51), d64793) ∈ rowCases136 := by
  exact List.mem_cons_self
theorem oracleMember120 : ((.push 51 (.stay 29)), d56153) ∈ rowCases136 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases137 : List OracleBranch := [((.walk 95), d74040)]
theorem oracleMember121 : ((.walk 95), d74040) ∈ rowCases137 := by
  exact List.mem_cons_self
noncomputable def rowCases138 : List OracleBranch := [((.walk 74), d66089)]
theorem oracleMember122 : ((.walk 74), d66089) ∈ rowCases138 := by
  exact List.mem_cons_self
noncomputable def rowCases139 : List OracleBranch := []
noncomputable def rowCases140 : List OracleBranch := [((.walk 52), d67300)]
theorem oracleMember123 : ((.walk 52), d67300) ∈ rowCases140 := by
  exact List.mem_cons_self
noncomputable def rowCases141 : List OracleBranch := [((.walk 50), d64794)]
theorem oracleMember124 : ((.walk 50), d64794) ∈ rowCases141 := by
  exact List.mem_cons_self
noncomputable def rowCases142 : List OracleBranch := [((.walk 96), d74046)]
theorem oracleMember125 : ((.walk 96), d74046) ∈ rowCases142 := by
  exact List.mem_cons_self
noncomputable def rowCases143 : List OracleBranch := [((.walk 94), d74047)]
theorem oracleMember126 : ((.walk 94), d74047) ∈ rowCases143 := by
  exact List.mem_cons_self
noncomputable def rowCases144 : List OracleBranch := [((.walk 52), d66275), ((.push 52 (.stay 30)), d56776)]
theorem oracleMember127 : ((.walk 52), d66275) ∈ rowCases144 := by
  exact List.mem_cons_self
theorem oracleMember128 : ((.push 52 (.stay 30)), d56776) ∈ rowCases144 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases145 : List OracleBranch := [((.walk 96), d74048), ((.push 96 (.stay 118)), d74052)]
theorem oracleMember129 : ((.walk 96), d74048) ∈ rowCases145 := by
  exact List.mem_cons_self
theorem oracleMember130 : ((.push 96 (.stay 118)), d74052) ∈ rowCases145 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases146 : List OracleBranch := []
noncomputable def rowCases147 : List OracleBranch := [((.walk 73), d66089)]
theorem oracleMember131 : ((.walk 73), d66089) ∈ rowCases147 := by
  exact List.mem_cons_self
noncomputable def rowCases148 : List OracleBranch := []
noncomputable def rowCases149 : List OracleBranch := [((.walk 51), d66091)]
theorem oracleMember132 : ((.walk 51), d66091) ∈ rowCases149 := by
  exact List.mem_cons_self
noncomputable def rowCases150 : List OracleBranch := [((.walk 97), d74056)]
theorem oracleMember133 : ((.walk 97), d74056) ∈ rowCases150 := by
  exact List.mem_cons_self
noncomputable def rowCases151 : List OracleBranch := [((.walk 95), d74062)]
theorem oracleMember134 : ((.walk 95), d74062) ∈ rowCases151 := by
  exact List.mem_cons_self
noncomputable def rowCases152 : List OracleBranch := []
noncomputable def rowCases153 : List OracleBranch := [((.walk 98), d74067), ((.push 98 (.stay 120)), d74072)]
theorem oracleMember135 : ((.walk 98), d74067) ∈ rowCases153 := by
  exact List.mem_cons_self
theorem oracleMember136 : ((.push 98 (.stay 120)), d74072) ∈ rowCases153 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases154 : List OracleBranch := []
noncomputable def rowCases155 : List OracleBranch := []
noncomputable def rowCases156 : List OracleBranch := []
noncomputable def rowCases157 : List OracleBranch := []
noncomputable def rowCases158 : List OracleBranch := []
noncomputable def rowCases159 : List OracleBranch := [((.walk 97), d74074)]
theorem oracleMember137 : ((.walk 97), d74074) ∈ rowCases159 := by
  exact List.mem_cons_self
noncomputable def rowCases160 : List OracleBranch := []
noncomputable def rowCases161 : List OracleBranch := [((.walk 100), d1), ((.push 100 (.stay 122)), d0)]
theorem oracleMember138 : ((.walk 100), d1) ∈ rowCases161 := by
  exact List.mem_cons_self
theorem oracleMember139 : ((.push 100 (.stay 122)), d0) ∈ rowCases161 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases162 : List OracleBranch := [((.walk 79), d1), ((.push 79 (.stay 80)), d0)]
theorem oracleMember140 : ((.walk 79), d1) ∈ rowCases162 := by
  exact List.mem_cons_self
theorem oracleMember141 : ((.push 79 (.stay 80)), d0) ∈ rowCases162 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases163 : List OracleBranch := []
noncomputable def rowCases164 : List OracleBranch := []
noncomputable def rowCases165 : List OracleBranch := []
noncomputable def rowCases166 : List OracleBranch := [((.walk 101), d1)]
theorem oracleMember142 : ((.walk 101), d1) ∈ rowCases166 := by
  exact List.mem_cons_self
noncomputable def rowCases167 : List OracleBranch := []
noncomputable def rowCases168 : List OracleBranch := []
noncomputable def rowCases169 : List OracleBranch := [((.walk 101), d1), ((.push 101 (.stay 123)), d0)]
theorem oracleMember143 : ((.walk 101), d1) ∈ rowCases169 := by
  exact List.mem_cons_self
theorem oracleMember144 : ((.push 101 (.stay 123)), d0) ∈ rowCases169 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases170 : List OracleBranch := [((.walk 80), d1), ((.push 80 (.stay 81)), d0)]
theorem oracleMember145 : ((.walk 80), d1) ∈ rowCases170 := by
  exact List.mem_cons_self
theorem oracleMember146 : ((.push 80 (.stay 81)), d0) ∈ rowCases170 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases171 : List OracleBranch := [((.walk 78), d1)]
theorem oracleMember147 : ((.walk 78), d1) ∈ rowCases171 := by
  exact List.mem_cons_self
noncomputable def rowCases172 : List OracleBranch := []
noncomputable def rowCases173 : List OracleBranch := []
noncomputable def rowCases174 : List OracleBranch := [((.walk 102), d1)]
theorem oracleMember148 : ((.walk 102), d1) ∈ rowCases174 := by
  exact List.mem_cons_self
noncomputable def rowCases175 : List OracleBranch := [((.walk 100), d1)]
theorem oracleMember149 : ((.walk 100), d1) ∈ rowCases175 := by
  exact List.mem_cons_self
noncomputable def rowCases176 : List OracleBranch := []
noncomputable def rowCases177 : List OracleBranch := [((.walk 102), d1), ((.push 102 (.stay 124)), d0)]
theorem oracleMember150 : ((.walk 102), d1) ∈ rowCases177 := by
  exact List.mem_cons_self
theorem oracleMember151 : ((.push 102 (.stay 124)), d0) ∈ rowCases177 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases178 : List OracleBranch := [((.walk 81), d1), ((.push 81 (.stay 82)), d0)]
theorem oracleMember152 : ((.walk 81), d1) ∈ rowCases178 := by
  exact List.mem_cons_self
theorem oracleMember153 : ((.push 81 (.stay 82)), d0) ∈ rowCases178 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases179 : List OracleBranch := [((.walk 79), d1), ((.push 79 (.stay 78)), d0)]
theorem oracleMember154 : ((.walk 79), d1) ∈ rowCases179 := by
  exact List.mem_cons_self
theorem oracleMember155 : ((.push 79 (.stay 78)), d0) ∈ rowCases179 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases180 : List OracleBranch := []
noncomputable def rowCases181 : List OracleBranch := []
noncomputable def rowCases182 : List OracleBranch := [((.walk 103), d1)]
theorem oracleMember156 : ((.walk 103), d1) ∈ rowCases182 := by
  exact List.mem_cons_self
noncomputable def rowCases183 : List OracleBranch := [((.walk 101), d1)]
theorem oracleMember157 : ((.walk 101), d1) ∈ rowCases183 := by
  exact List.mem_cons_self
noncomputable def rowCases184 : List OracleBranch := []
noncomputable def rowCases185 : List OracleBranch := [((.walk 103), d1), ((.push 103 (.stay 125)), d0)]
theorem oracleMember158 : ((.walk 103), d1) ∈ rowCases185 := by
  exact List.mem_cons_self
theorem oracleMember159 : ((.push 103 (.stay 125)), d0) ∈ rowCases185 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases186 : List OracleBranch := [((.walk 82), d1), ((.push 82 (.stay 83)), d0)]
theorem oracleMember160 : ((.walk 82), d1) ∈ rowCases186 := by
  exact List.mem_cons_self
theorem oracleMember161 : ((.push 82 (.stay 83)), d0) ∈ rowCases186 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases187 : List OracleBranch := [((.walk 80), d1), ((.push 80 (.stay 79)), d0)]
theorem oracleMember162 : ((.walk 80), d1) ∈ rowCases187 := by
  exact List.mem_cons_self
theorem oracleMember163 : ((.push 80 (.stay 79)), d0) ∈ rowCases187 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases188 : List OracleBranch := []
noncomputable def rowCases189 : List OracleBranch := []
noncomputable def rowCases190 : List OracleBranch := [((.walk 104), d1)]
theorem oracleMember164 : ((.walk 104), d1) ∈ rowCases190 := by
  exact List.mem_cons_self
noncomputable def rowCases191 : List OracleBranch := [((.walk 102), d1)]
theorem oracleMember165 : ((.walk 102), d1) ∈ rowCases191 := by
  exact List.mem_cons_self
noncomputable def rowCases192 : List OracleBranch := []
noncomputable def rowCases193 : List OracleBranch := [((.walk 104), d1), ((.push 104 (.stay 126)), d0)]
theorem oracleMember166 : ((.walk 104), d1) ∈ rowCases193 := by
  exact List.mem_cons_self
theorem oracleMember167 : ((.push 104 (.stay 126)), d0) ∈ rowCases193 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases194 : List OracleBranch := [((.walk 83), d1), ((.push 83 (.stay 84)), d0)]
theorem oracleMember168 : ((.walk 83), d1) ∈ rowCases194 := by
  exact List.mem_cons_self
theorem oracleMember169 : ((.push 83 (.stay 84)), d0) ∈ rowCases194 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases195 : List OracleBranch := [((.walk 81), d1), ((.push 81 (.stay 80)), d0)]
theorem oracleMember170 : ((.walk 81), d1) ∈ rowCases195 := by
  exact List.mem_cons_self
theorem oracleMember171 : ((.push 81 (.stay 80)), d0) ∈ rowCases195 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases196 : List OracleBranch := []
noncomputable def rowCases197 : List OracleBranch := []
noncomputable def rowCases198 : List OracleBranch := [((.walk 105), d1)]
theorem oracleMember172 : ((.walk 105), d1) ∈ rowCases198 := by
  exact List.mem_cons_self
noncomputable def rowCases199 : List OracleBranch := [((.walk 103), d1)]
theorem oracleMember173 : ((.walk 103), d1) ∈ rowCases199 := by
  exact List.mem_cons_self
end NetHack.Soko22Hazard87
