import NetHack.Soko22Hazard87.OracleStaticCorners10
import NetHack.Soko22Hazard87.GuardExtra222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
noncomputable def rowCases0 : List OracleBranch := []
noncomputable def rowCases1 : List OracleBranch := [((.walk 47), d51640), ((.push 47 (.stay 69)), d53870)]
theorem oracleMember0 : ((.walk 47), d51640) ∈ rowCases1 := by
  exact List.mem_cons_self
theorem oracleMember1 : ((.push 47 (.stay 69)), d53870) ∈ rowCases1 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases2 : List OracleBranch := []
noncomputable def rowCases3 : List OracleBranch := []
noncomputable def rowCases4 : List OracleBranch := []
noncomputable def rowCases5 : List OracleBranch := []
noncomputable def rowCases6 : List OracleBranch := [((.walk 48), d54186)]
theorem oracleMember2 : ((.walk 48), d54186) ∈ rowCases6 := by
  exact List.mem_cons_self
noncomputable def rowCases7 : List OracleBranch := [((.walk 46), d54513)]
theorem oracleMember3 : ((.walk 46), d54513) ∈ rowCases7 := by
  exact List.mem_cons_self
noncomputable def rowCases8 : List OracleBranch := []
noncomputable def rowCases9 : List OracleBranch := [((.walk 49), d54518), ((.push 49 (.stay 71)), d54981)]
theorem oracleMember4 : ((.walk 49), d54518) ∈ rowCases9 := by
  exact List.mem_cons_self
theorem oracleMember5 : ((.push 49 (.stay 71)), d54981) ∈ rowCases9 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases10 : List OracleBranch := [((.walk 28), d55597), ((.push 28 (.stay 29)), d55749)]
theorem oracleMember6 : ((.walk 28), d55597) ∈ rowCases10 := by
  exact List.mem_cons_self
theorem oracleMember7 : ((.push 28 (.stay 29)), d55749) ∈ rowCases10 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases11 : List OracleBranch := []
noncomputable def rowCases12 : List OracleBranch := []
noncomputable def rowCases13 : List OracleBranch := []
noncomputable def rowCases14 : List OracleBranch := [((.walk 50), d55757)]
theorem oracleMember8 : ((.walk 50), d55757) ∈ rowCases14 := by
  exact List.mem_cons_self
noncomputable def rowCases15 : List OracleBranch := [((.walk 48), d55879)]
theorem oracleMember9 : ((.walk 48), d55879) ∈ rowCases15 := by
  exact List.mem_cons_self
noncomputable def rowCases16 : List OracleBranch := []
noncomputable def rowCases17 : List OracleBranch := [((.walk 50), d55880)]
theorem oracleMember10 : ((.walk 50), d55880) ∈ rowCases17 := by
  exact List.mem_cons_self
noncomputable def rowCases18 : List OracleBranch := [((.walk 29), d55881), ((.push 29 (.stay 30)), d55886)]
theorem oracleMember11 : ((.walk 29), d55881) ∈ rowCases18 := by
  exact List.mem_cons_self
theorem oracleMember12 : ((.push 29 (.stay 30)), d55886) ∈ rowCases18 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases19 : List OracleBranch := [((.walk 27), d55597)]
theorem oracleMember13 : ((.walk 27), d55597) ∈ rowCases19 := by
  exact List.mem_cons_self
noncomputable def rowCases20 : List OracleBranch := []
noncomputable def rowCases21 : List OracleBranch := []
noncomputable def rowCases22 : List OracleBranch := [((.walk 51), d55894)]
theorem oracleMember14 : ((.walk 51), d55894) ∈ rowCases22 := by
  exact List.mem_cons_self
noncomputable def rowCases23 : List OracleBranch := [((.walk 49), d56147)]
theorem oracleMember15 : ((.walk 49), d56147) ∈ rowCases23 := by
  exact List.mem_cons_self
noncomputable def rowCases24 : List OracleBranch := []
noncomputable def rowCases25 : List OracleBranch := [((.walk 51), d56148), ((.push 51 (.stay 73)), d56153)]
theorem oracleMember16 : ((.walk 51), d56148) ∈ rowCases25 := by
  exact List.mem_cons_self
theorem oracleMember17 : ((.push 51 (.stay 73)), d56153) ∈ rowCases25 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases26 : List OracleBranch := [((.walk 30), d56756)]
theorem oracleMember18 : ((.walk 30), d56756) ∈ rowCases26 := by
  exact List.mem_cons_self
noncomputable def rowCases27 : List OracleBranch := [((.walk 28), d55881), ((.push 28 (.stay 27)), d55749)]
theorem oracleMember19 : ((.walk 28), d55881) ∈ rowCases27 := by
  exact List.mem_cons_self
theorem oracleMember20 : ((.push 28 (.stay 27)), d55749) ∈ rowCases27 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases28 : List OracleBranch := []
noncomputable def rowCases29 : List OracleBranch := []
noncomputable def rowCases30 : List OracleBranch := [((.walk 52), d56764)]
theorem oracleMember21 : ((.walk 52), d56764) ∈ rowCases30 := by
  exact List.mem_cons_self
noncomputable def rowCases31 : List OracleBranch := [((.walk 50), d56770)]
theorem oracleMember22 : ((.walk 50), d56770) ∈ rowCases31 := by
  exact List.mem_cons_self
noncomputable def rowCases32 : List OracleBranch := []
noncomputable def rowCases33 : List OracleBranch := [((.walk 52), d56771), ((.push 52 (.stay 74)), d56776)]
theorem oracleMember23 : ((.walk 52), d56771) ∈ rowCases33 := by
  exact List.mem_cons_self
theorem oracleMember24 : ((.push 52 (.stay 74)), d56776) ∈ rowCases33 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases34 : List OracleBranch := []
noncomputable def rowCases35 : List OracleBranch := [((.walk 29), d56756), ((.push 29 (.stay 28)), d55886)]
theorem oracleMember25 : ((.walk 29), d56756) ∈ rowCases35 := by
  exact List.mem_cons_self
theorem oracleMember26 : ((.push 29 (.stay 28)), d55886) ∈ rowCases35 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases36 : List OracleBranch := []
noncomputable def rowCases37 : List OracleBranch := []
noncomputable def rowCases38 : List OracleBranch := []
noncomputable def rowCases39 : List OracleBranch := [((.walk 51), d57566)]
theorem oracleMember27 : ((.walk 51), d57566) ∈ rowCases39 := by
  exact List.mem_cons_self
noncomputable def rowCases40 : List OracleBranch := []
noncomputable def rowCases41 : List OracleBranch := [((.walk 67), d57571), ((.push 67 (.stay 89)), d57576)]
theorem oracleMember28 : ((.walk 67), d57571) ∈ rowCases41 := by
  exact List.mem_cons_self
theorem oracleMember29 : ((.push 67 (.stay 89)), d57576) ∈ rowCases41 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases42 : List OracleBranch := [((.walk 46), d58123), ((.push 46 (.stay 47)), d58126)]
theorem oracleMember30 : ((.walk 46), d58123) ∈ rowCases42 := by
  exact List.mem_cons_self
theorem oracleMember31 : ((.push 46 (.stay 47)), d58126) ∈ rowCases42 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases43 : List OracleBranch := []
noncomputable def rowCases44 : List OracleBranch := []
noncomputable def rowCases45 : List OracleBranch := []
noncomputable def rowCases46 : List OracleBranch := []
noncomputable def rowCases47 : List OracleBranch := []
noncomputable def rowCases48 : List OracleBranch := []
noncomputable def rowCases49 : List OracleBranch := []
noncomputable def rowCases50 : List OracleBranch := [((.walk 47), d54512), ((.push 47 (.stay 48)), d58129)]
theorem oracleMember32 : ((.walk 47), d54512) ∈ rowCases50 := by
  exact List.mem_cons_self
theorem oracleMember33 : ((.push 47 (.stay 48)), d58129) ∈ rowCases50 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases51 : List OracleBranch := [((.walk 45), d58123)]
theorem oracleMember34 : ((.walk 45), d58123) ∈ rowCases51 := by
  exact List.mem_cons_self
noncomputable def rowCases52 : List OracleBranch := [((.walk 25), d54513)]
theorem oracleMember35 : ((.walk 25), d54513) ∈ rowCases52 := by
  exact List.mem_cons_self
noncomputable def rowCases53 : List OracleBranch := []
noncomputable def rowCases54 : List OracleBranch := [((.walk 69), d58433)]
theorem oracleMember36 : ((.walk 69), d58433) ∈ rowCases54 := by
  exact List.mem_cons_self
noncomputable def rowCases55 : List OracleBranch := [((.walk 67), d58745)]
theorem oracleMember37 : ((.walk 67), d58745) ∈ rowCases55 := by
  exact List.mem_cons_self
noncomputable def rowCases56 : List OracleBranch := [((.walk 25), d51640)]
theorem oracleMember38 : ((.walk 25), d51640) ∈ rowCases56 := by
  exact List.mem_cons_self
noncomputable def rowCases57 : List OracleBranch := [((.walk 69), d58432), ((.push 69 (.stay 91)), d58750)]
theorem oracleMember39 : ((.walk 69), d58432) ∈ rowCases57 := by
  exact List.mem_cons_self
theorem oracleMember40 : ((.push 69 (.stay 91)), d58750) ∈ rowCases57 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases58 : List OracleBranch := [((.walk 48), d54185), ((.push 48 (.stay 49)), d60241)]
theorem oracleMember41 : ((.walk 48), d54185) ∈ rowCases58 := by
  exact List.mem_cons_self
theorem oracleMember42 : ((.push 48 (.stay 49)), d60241) ∈ rowCases58 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases59 : List OracleBranch := [((.walk 46), d54512), ((.push 46 (.stay 45)), d58126)]
theorem oracleMember43 : ((.walk 46), d54512) ∈ rowCases59 := by
  exact List.mem_cons_self
theorem oracleMember44 : ((.push 46 (.stay 45)), d58126) ∈ rowCases59 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases60 : List OracleBranch := []
noncomputable def rowCases61 : List OracleBranch := []
noncomputable def rowCases62 : List OracleBranch := [((.walk 70), d61360)]
theorem oracleMember45 : ((.walk 70), d61360) ∈ rowCases62 := by
  exact List.mem_cons_self
noncomputable def rowCases63 : List OracleBranch := []
noncomputable def rowCases64 : List OracleBranch := []
noncomputable def rowCases65 : List OracleBranch := [((.walk 70), d61807)]
theorem oracleMember46 : ((.walk 70), d61807) ∈ rowCases65 := by
  exact List.mem_cons_self
noncomputable def rowCases66 : List OracleBranch := [((.walk 49), d55878), ((.push 49 (.stay 50)), d61810)]
theorem oracleMember47 : ((.walk 49), d55878) ∈ rowCases66 := by
  exact List.mem_cons_self
theorem oracleMember48 : ((.push 49 (.stay 50)), d61810) ∈ rowCases66 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases67 : List OracleBranch := [((.walk 47), d54185), ((.push 47 (.stay 46)), d58129)]
theorem oracleMember49 : ((.walk 47), d54185) ∈ rowCases67 := by
  exact List.mem_cons_self
theorem oracleMember50 : ((.push 47 (.stay 46)), d58129) ∈ rowCases67 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases68 : List OracleBranch := [((.walk 27), d55879)]
theorem oracleMember51 : ((.walk 27), d55879) ∈ rowCases68 := by
  exact List.mem_cons_self
noncomputable def rowCases69 : List OracleBranch := [((.walk 25), d54186)]
theorem oracleMember52 : ((.walk 25), d54186) ∈ rowCases69 := by
  exact List.mem_cons_self
noncomputable def rowCases70 : List OracleBranch := [((.walk 71), d62376)]
theorem oracleMember53 : ((.walk 71), d62376) ∈ rowCases70 := by
  exact List.mem_cons_self
noncomputable def rowCases71 : List OracleBranch := [((.walk 69), d62827)]
theorem oracleMember54 : ((.walk 69), d62827) ∈ rowCases71 := by
  exact List.mem_cons_self
noncomputable def rowCases72 : List OracleBranch := [((.walk 27), d54518)]
theorem oracleMember55 : ((.walk 27), d54518) ∈ rowCases72 := by
  exact List.mem_cons_self
noncomputable def rowCases73 : List OracleBranch := [((.walk 71), d62934), ((.push 71 (.stay 93)), d62939)]
theorem oracleMember56 : ((.walk 71), d62934) ∈ rowCases73 := by
  exact List.mem_cons_self
theorem oracleMember57 : ((.push 71 (.stay 93)), d62939) ∈ rowCases73 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases74 : List OracleBranch := [((.walk 50), d55755), ((.push 50 (.stay 51)), d64189)]
theorem oracleMember58 : ((.walk 50), d55755) ∈ rowCases74 := by
  exact List.mem_cons_self
theorem oracleMember59 : ((.push 50 (.stay 51)), d64189) ∈ rowCases74 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases75 : List OracleBranch := [((.walk 48), d55878), ((.push 48 (.stay 47)), d60241)]
theorem oracleMember60 : ((.walk 48), d55878) ∈ rowCases75 := by
  exact List.mem_cons_self
theorem oracleMember61 : ((.push 48 (.stay 47)), d60241) ∈ rowCases75 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases76 : List OracleBranch := [((.walk 28), d56147)]
theorem oracleMember62 : ((.walk 28), d56147) ∈ rowCases76 := by
  exact List.mem_cons_self
noncomputable def rowCases77 : List OracleBranch := []
noncomputable def rowCases78 : List OracleBranch := []
noncomputable def rowCases79 : List OracleBranch := [((.walk 70), d64542)]
theorem oracleMember63 : ((.walk 70), d64542) ∈ rowCases79 := by
  exact List.mem_cons_self
noncomputable def rowCases80 : List OracleBranch := [((.walk 28), d55880)]
theorem oracleMember64 : ((.walk 28), d55880) ∈ rowCases80 := by
  exact List.mem_cons_self
noncomputable def rowCases81 : List OracleBranch := []
noncomputable def rowCases82 : List OracleBranch := [((.walk 51), d55892), ((.push 51 (.stay 52)), d64664)]
theorem oracleMember65 : ((.walk 51), d55892) ∈ rowCases82 := by
  exact List.mem_cons_self
theorem oracleMember66 : ((.push 51 (.stay 52)), d64664) ∈ rowCases82 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases83 : List OracleBranch := [((.walk 49), d55755), ((.push 49 (.stay 48)), d61810)]
theorem oracleMember67 : ((.walk 49), d55755) ∈ rowCases83 := by
  exact List.mem_cons_self
theorem oracleMember68 : ((.push 49 (.stay 48)), d61810) ∈ rowCases83 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases84 : List OracleBranch := [((.walk 29), d56770)]
theorem oracleMember69 : ((.walk 29), d56770) ∈ rowCases84 := by
  exact List.mem_cons_self
noncomputable def rowCases85 : List OracleBranch := [((.walk 27), d55757)]
theorem oracleMember70 : ((.walk 27), d55757) ∈ rowCases85 := by
  exact List.mem_cons_self
noncomputable def rowCases86 : List OracleBranch := [((.walk 73), d64794)]
theorem oracleMember71 : ((.walk 73), d64794) ∈ rowCases86 := by
  exact List.mem_cons_self
noncomputable def rowCases87 : List OracleBranch := [((.walk 71), d64965)]
theorem oracleMember72 : ((.walk 71), d64965) ∈ rowCases87 := by
  exact List.mem_cons_self
noncomputable def rowCases88 : List OracleBranch := [((.walk 29), d56148)]
theorem oracleMember73 : ((.walk 29), d56148) ∈ rowCases88 := by
  exact List.mem_cons_self
noncomputable def rowCases89 : List OracleBranch := [((.walk 73), d64793), ((.push 73 (.stay 95)), d65090)]
theorem oracleMember74 : ((.walk 73), d64793) ∈ rowCases89 := by
  exact List.mem_cons_self
theorem oracleMember75 : ((.push 73 (.stay 95)), d65090) ∈ rowCases89 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases90 : List OracleBranch := [((.walk 52), d56762)]
theorem oracleMember76 : ((.walk 52), d56762) ∈ rowCases90 := by
  exact List.mem_cons_self
noncomputable def rowCases91 : List OracleBranch := [((.walk 50), d55892), ((.push 50 (.stay 49)), d64189)]
theorem oracleMember77 : ((.walk 50), d55892) ∈ rowCases91 := by
  exact List.mem_cons_self
theorem oracleMember78 : ((.push 50 (.stay 49)), d64189) ∈ rowCases91 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases92 : List OracleBranch := [((.walk 30), d57566)]
theorem oracleMember79 : ((.walk 30), d57566) ∈ rowCases92 := by
  exact List.mem_cons_self
noncomputable def rowCases93 : List OracleBranch := [((.walk 28), d55894)]
theorem oracleMember80 : ((.walk 28), d55894) ∈ rowCases93 := by
  exact List.mem_cons_self
noncomputable def rowCases94 : List OracleBranch := [((.walk 74), d66091)]
theorem oracleMember81 : ((.walk 74), d66091) ∈ rowCases94 := by
  exact List.mem_cons_self
noncomputable def rowCases95 : List OracleBranch := []
noncomputable def rowCases96 : List OracleBranch := [((.walk 30), d56771)]
theorem oracleMember82 : ((.walk 30), d56771) ∈ rowCases96 := by
  exact List.mem_cons_self
noncomputable def rowCases97 : List OracleBranch := [((.walk 74), d66275), ((.push 74 (.stay 96)), d66280)]
theorem oracleMember83 : ((.walk 74), d66275) ∈ rowCases97 := by
  exact List.mem_cons_self
theorem oracleMember84 : ((.push 74 (.stay 96)), d66280) ∈ rowCases97 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
noncomputable def rowCases98 : List OracleBranch := []
noncomputable def rowCases99 : List OracleBranch := [((.walk 51), d56762), ((.push 51 (.stay 50)), d64664)]
theorem oracleMember85 : ((.walk 51), d56762) ∈ rowCases99 := by
  exact List.mem_cons_self
theorem oracleMember86 : ((.push 51 (.stay 50)), d64664) ∈ rowCases99 := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
end NetHack.Soko22Hazard87
