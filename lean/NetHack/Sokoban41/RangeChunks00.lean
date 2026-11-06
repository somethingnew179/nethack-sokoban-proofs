/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Diagram
namespace NetHack.Sokoban41.Diagram
theorem range0 (pattern : Ten) : 0 ≤ d0 pattern ∧ d0 pattern ≤ 10 := by
  change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 10
  decide
theorem range1 (pattern : Ten) : 0 ≤ d1 pattern ∧ d1 pattern ≤ 10 := by
  change (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 10
  decide
theorem range2 (pattern : Ten) : 0 ≤ d2 pattern ∧ d2 pattern ≤ 10 := by
  change (0 : Int) ≤ 2 ∧ (2 : Int) ≤ 10
  decide
theorem range3 (pattern : Ten) : 0 ≤ d3 pattern ∧ d3 pattern ≤ 10 := by
  change (0 : Int) ≤ 3 ∧ (3 : Int) ≤ 10
  decide
theorem range4 (pattern : Ten) : 0 ≤ d4 pattern ∧ d4 pattern ≤ 10 := by
  change (0 : Int) ≤ 4 ∧ (4 : Int) ≤ 10
  decide
theorem range5 (pattern : Ten) : 0 ≤ d5 pattern ∧ d5 pattern ≤ 10 := by
  change (0 : Int) ≤ 5 ∧ (5 : Int) ≤ 10
  decide
theorem range6 (pattern : Ten) : 0 ≤ d6 pattern ∧ d6 pattern ≤ 10 := by
  change (0 : Int) ≤ 6 ∧ (6 : Int) ≤ 10
  decide
theorem range7 (pattern : Ten) : 0 ≤ d7 pattern ∧ d7 pattern ≤ 10 := by
  change (0 : Int) ≤ 7 ∧ (7 : Int) ≤ 10
  decide
theorem range8 (pattern : Ten) : 0 ≤ d8 pattern ∧ d8 pattern ≤ 10 := by
  change (0 : Int) ≤ 8 ∧ (8 : Int) ≤ 10
  decide
theorem range9 (pattern : Ten) : 0 ≤ d9 pattern ∧ d9 pattern ≤ 10 := by
  change (0 : Int) ≤ 9 ∧ (9 : Int) ≤ 10
  decide
theorem range10 (pattern : Ten) : 0 ≤ d10 pattern ∧ d10 pattern ≤ 10 := by
  change (0 : Int) ≤ 10 ∧ (10 : Int) ≤ 10
  decide
theorem range11 (pattern : Ten) : 0 ≤ d11 pattern ∧ d11 pattern ≤ 10 := by
  unfold d11
  split
  · exact range10 pattern
  · exact range9 pattern
theorem range12 (pattern : Ten) : 0 ≤ d12 pattern ∧ d12 pattern ≤ 10 := by
  unfold d12
  split
  · exact range10 pattern
  · exact range0 pattern
theorem range13 (pattern : Ten) : 0 ≤ d13 pattern ∧ d13 pattern ≤ 10 := by
  unfold d13
  split
  · exact range11 pattern
  · exact range0 pattern
theorem range14 (pattern : Ten) : 0 ≤ d14 pattern ∧ d14 pattern ≤ 10 := by
  unfold d14
  split
  · exact range10 pattern
  · exact range11 pattern
theorem range15 (pattern : Ten) : 0 ≤ d15 pattern ∧ d15 pattern ≤ 10 := by
  unfold d15
  split
  · exact range2 pattern
  · exact range0 pattern
theorem range16 (pattern : Ten) : 0 ≤ d16 pattern ∧ d16 pattern ≤ 10 := by
  unfold d16
  split
  · exact range10 pattern
  · exact range2 pattern
theorem range17 (pattern : Ten) : 0 ≤ d17 pattern ∧ d17 pattern ≤ 10 := by
  unfold d17
  split
  · exact range12 pattern
  · exact range0 pattern
theorem range18 (pattern : Ten) : 0 ≤ d18 pattern ∧ d18 pattern ≤ 10 := by
  unfold d18
  split
  · exact range10 pattern
  · exact range12 pattern
theorem range19 (pattern : Ten) : 0 ≤ d19 pattern ∧ d19 pattern ≤ 10 := by
  unfold d19
  split
  · exact range14 pattern
  · exact range13 pattern
theorem range20 (pattern : Ten) : 0 ≤ d20 pattern ∧ d20 pattern ≤ 10 := by
  unfold d20
  split
  · exact range10 pattern
  · exact range14 pattern
theorem range21 (pattern : Ten) : 0 ≤ d21 pattern ∧ d21 pattern ≤ 10 := by
  unfold d21
  split
  · exact range16 pattern
  · exact range15 pattern
theorem range22 (pattern : Ten) : 0 ≤ d22 pattern ∧ d22 pattern ≤ 10 := by
  unfold d22
  split
  · exact range10 pattern
  · exact range16 pattern
theorem range23 (pattern : Ten) : 0 ≤ d23 pattern ∧ d23 pattern ≤ 10 := by
  unfold d23
  split
  · exact range18 pattern
  · exact range17 pattern
theorem range24 (pattern : Ten) : 0 ≤ d24 pattern ∧ d24 pattern ≤ 10 := by
  unfold d24
  split
  · exact range20 pattern
  · exact range19 pattern
theorem range25 (pattern : Ten) : 0 ≤ d25 pattern ∧ d25 pattern ≤ 10 := by
  unfold d25
  split
  · exact range22 pattern
  · exact range21 pattern
theorem range26 (pattern : Ten) : 0 ≤ d26 pattern ∧ d26 pattern ≤ 10 := by
  unfold d26
  split
  · exact range10 pattern
  · exact range18 pattern
theorem range27 (pattern : Ten) : 0 ≤ d27 pattern ∧ d27 pattern ≤ 10 := by
  unfold d27
  split
  · exact range10 pattern
  · exact range20 pattern
theorem range28 (pattern : Ten) : 0 ≤ d28 pattern ∧ d28 pattern ≤ 10 := by
  unfold d28
  split
  · exact range10 pattern
  · exact range22 pattern
theorem range29 (pattern : Ten) : 0 ≤ d29 pattern ∧ d29 pattern ≤ 10 := by
  unfold d29
  split
  · exact range24 pattern
  · exact range23 pattern
theorem range30 (pattern : Ten) : 0 ≤ d30 pattern ∧ d30 pattern ≤ 10 := by
  unfold d30
  split
  · exact range24 pattern
  · exact range25 pattern
theorem range31 (pattern : Ten) : 0 ≤ d31 pattern ∧ d31 pattern ≤ 10 := by
  unfold d31
  split
  · exact range27 pattern
  · exact range26 pattern
theorem range32 (pattern : Ten) : 0 ≤ d32 pattern ∧ d32 pattern ≤ 10 := by
  unfold d32
  split
  · exact range27 pattern
  · exact range28 pattern
theorem range33 (pattern : Ten) : 0 ≤ d33 pattern ∧ d33 pattern ≤ 10 := by
  unfold d33
  split
  · exact range30 pattern
  · exact range29 pattern
theorem range34 (pattern : Ten) : 0 ≤ d34 pattern ∧ d34 pattern ≤ 10 := by
  unfold d34
  split
  · exact range32 pattern
  · exact range31 pattern
theorem range35 (pattern : Ten) : 0 ≤ d35 pattern ∧ d35 pattern ≤ 10 := by
  unfold d35
  split
  · exact range34 pattern
  · exact range33 pattern
theorem range36 (pattern : Ten) : 0 ≤ d36 pattern ∧ d36 pattern ≤ 10 := by
  unfold d36
  split
  · exact range10 pattern
  · exact range34 pattern
theorem range37 (pattern : Ten) : 0 ≤ d37 pattern ∧ d37 pattern ≤ 10 := by
  unfold d37
  split
  · exact range36 pattern
  · exact range35 pattern
theorem range38 (pattern : Ten) : 0 ≤ d38 pattern ∧ d38 pattern ≤ 10 := by
  unfold d38
  split
  · exact range8 pattern
  · exact range7 pattern
theorem range39 (pattern : Ten) : 0 ≤ d39 pattern ∧ d39 pattern ≤ 10 := by
  unfold d39
  split
  · exact range10 pattern
  · exact range9 pattern
theorem range40 (pattern : Ten) : 0 ≤ d40 pattern ∧ d40 pattern ≤ 10 := by
  unfold d40
  split
  · exact range8 pattern
  · exact range38 pattern
theorem range41 (pattern : Ten) : 0 ≤ d41 pattern ∧ d41 pattern ≤ 10 := by
  unfold d41
  split
  · exact range10 pattern
  · exact range39 pattern
theorem range42 (pattern : Ten) : 0 ≤ d42 pattern ∧ d42 pattern ≤ 10 := by
  unfold d42
  split
  · exact range10 pattern
  · exact range4 pattern
theorem range43 (pattern : Ten) : 0 ≤ d43 pattern ∧ d43 pattern ≤ 10 := by
  unfold d43
  split
  · exact range10 pattern
  · exact range6 pattern
theorem range44 (pattern : Ten) : 0 ≤ d44 pattern ∧ d44 pattern ≤ 10 := by
  unfold d44
  split
  · exact range4 pattern
  · exact range2 pattern
theorem range45 (pattern : Ten) : 0 ≤ d45 pattern ∧ d45 pattern ≤ 10 := by
  unfold d45
  split
  · exact range10 pattern
  · exact range8 pattern
theorem range46 (pattern : Ten) : 0 ≤ d46 pattern ∧ d46 pattern ≤ 10 := by
  unfold d46
  split
  · exact range10 pattern
  · exact range40 pattern
theorem range47 (pattern : Ten) : 0 ≤ d47 pattern ∧ d47 pattern ≤ 10 := by
  unfold d47
  split
  · exact range10 pattern
  · exact range41 pattern
theorem range48 (pattern : Ten) : 0 ≤ d48 pattern ∧ d48 pattern ≤ 10 := by
  unfold d48
  split
  · exact range42 pattern
  · exact range15 pattern
theorem range49 (pattern : Ten) : 0 ≤ d49 pattern ∧ d49 pattern ≤ 10 := by
  unfold d49
  split
  · exact range10 pattern
  · exact range43 pattern
theorem range50 (pattern : Ten) : 0 ≤ d50 pattern ∧ d50 pattern ≤ 10 := by
  unfold d50
  split
  · exact range43 pattern
  · exact range44 pattern
theorem range51 (pattern : Ten) : 0 ≤ d51 pattern ∧ d51 pattern ≤ 10 := by
  unfold d51
  split
  · exact range10 pattern
  · exact range45 pattern
theorem range52 (pattern : Ten) : 0 ≤ d52 pattern ∧ d52 pattern ≤ 10 := by
  unfold d52
  split
  · exact range10 pattern
  · exact range46 pattern
theorem range53 (pattern : Ten) : 0 ≤ d53 pattern ∧ d53 pattern ≤ 10 := by
  unfold d53
  split
  · exact range10 pattern
  · exact range47 pattern
theorem range54 (pattern : Ten) : 0 ≤ d54 pattern ∧ d54 pattern ≤ 10 := by
  unfold d54
  split
  · exact range49 pattern
  · exact range48 pattern
theorem range55 (pattern : Ten) : 0 ≤ d55 pattern ∧ d55 pattern ≤ 10 := by
  unfold d55
  split
  · exact range51 pattern
  · exact range50 pattern
theorem range56 (pattern : Ten) : 0 ≤ d56 pattern ∧ d56 pattern ≤ 10 := by
  unfold d56
  split
  · exact range10 pattern
  · exact range52 pattern
theorem range57 (pattern : Ten) : 0 ≤ d57 pattern ∧ d57 pattern ≤ 10 := by
  unfold d57
  split
  · exact range10 pattern
  · exact range53 pattern
theorem range58 (pattern : Ten) : 0 ≤ d58 pattern ∧ d58 pattern ≤ 10 := by
  unfold d58
  split
  · exact range27 pattern
  · exact range54 pattern
theorem range59 (pattern : Ten) : 0 ≤ d59 pattern ∧ d59 pattern ≤ 10 := by
  unfold d59
  split
  · exact range27 pattern
  · exact range55 pattern
theorem range60 (pattern : Ten) : 0 ≤ d60 pattern ∧ d60 pattern ≤ 10 := by
  unfold d60
  split
  · exact range10 pattern
  · exact range56 pattern
theorem range61 (pattern : Ten) : 0 ≤ d61 pattern ∧ d61 pattern ≤ 10 := by
  unfold d61
  split
  · exact range10 pattern
  · exact range57 pattern
theorem range62 (pattern : Ten) : 0 ≤ d62 pattern ∧ d62 pattern ≤ 10 := by
  unfold d62
  split
  · exact range59 pattern
  · exact range58 pattern
theorem range63 (pattern : Ten) : 0 ≤ d63 pattern ∧ d63 pattern ≤ 10 := by
  unfold d63
  split
  · exact range61 pattern
  · exact range60 pattern
theorem range64 (pattern : Ten) : 0 ≤ d64 pattern ∧ d64 pattern ≤ 10 := by
  unfold d64
  split
  · exact range62 pattern
  · exact range54 pattern
theorem range65 (pattern : Ten) : 0 ≤ d65 pattern ∧ d65 pattern ≤ 10 := by
  unfold d65
  split
  · exact range63 pattern
  · exact range56 pattern
theorem range66 (pattern : Ten) : 0 ≤ d66 pattern ∧ d66 pattern ≤ 10 := by
  unfold d66
  split
  · exact range65 pattern
  · exact range64 pattern
theorem range67 (pattern : Ten) : 0 ≤ d67 pattern ∧ d67 pattern ≤ 10 := by
  unfold d67
  split
  · exact range9 pattern
  · exact range0 pattern
theorem range68 (pattern : Ten) : 0 ≤ d68 pattern ∧ d68 pattern ≤ 10 := by
  unfold d68
  split
  · exact range10 pattern
  · exact range9 pattern
theorem range69 (pattern : Ten) : 0 ≤ d69 pattern ∧ d69 pattern ≤ 10 := by
  unfold d69
  split
  · exact range68 pattern
  · exact range67 pattern
theorem range70 (pattern : Ten) : 0 ≤ d70 pattern ∧ d70 pattern ≤ 10 := by
  unfold d70
  split
  · exact range10 pattern
  · exact range68 pattern
theorem range71 (pattern : Ten) : 0 ≤ d71 pattern ∧ d71 pattern ≤ 10 := by
  unfold d71
  split
  · exact range70 pattern
  · exact range69 pattern
theorem range72 (pattern : Ten) : 0 ≤ d72 pattern ∧ d72 pattern ≤ 10 := by
  unfold d72
  split
  · exact range10 pattern
  · exact range70 pattern
theorem range73 (pattern : Ten) : 0 ≤ d73 pattern ∧ d73 pattern ≤ 10 := by
  unfold d73
  split
  · exact range71 pattern
  · exact range23 pattern
theorem range74 (pattern : Ten) : 0 ≤ d74 pattern ∧ d74 pattern ≤ 10 := by
  unfold d74
  split
  · exact range71 pattern
  · exact range25 pattern
theorem range75 (pattern : Ten) : 0 ≤ d75 pattern ∧ d75 pattern ≤ 10 := by
  unfold d75
  split
  · exact range72 pattern
  · exact range26 pattern
theorem range76 (pattern : Ten) : 0 ≤ d76 pattern ∧ d76 pattern ≤ 10 := by
  unfold d76
  split
  · exact range72 pattern
  · exact range28 pattern
theorem range77 (pattern : Ten) : 0 ≤ d77 pattern ∧ d77 pattern ≤ 10 := by
  unfold d77
  split
  · exact range74 pattern
  · exact range73 pattern
theorem range78 (pattern : Ten) : 0 ≤ d78 pattern ∧ d78 pattern ≤ 10 := by
  unfold d78
  split
  · exact range76 pattern
  · exact range75 pattern
theorem range79 (pattern : Ten) : 0 ≤ d79 pattern ∧ d79 pattern ≤ 10 := by
  unfold d79
  split
  · exact range78 pattern
  · exact range77 pattern
theorem range80 (pattern : Ten) : 0 ≤ d80 pattern ∧ d80 pattern ≤ 10 := by
  unfold d80
  split
  · exact range10 pattern
  · exact range78 pattern
theorem range81 (pattern : Ten) : 0 ≤ d81 pattern ∧ d81 pattern ≤ 10 := by
  unfold d81
  split
  · exact range80 pattern
  · exact range79 pattern
theorem range82 (pattern : Ten) : 0 ≤ d82 pattern ∧ d82 pattern ≤ 10 := by
  unfold d82
  split
  · exact range7 pattern
  · exact range54 pattern
theorem range83 (pattern : Ten) : 0 ≤ d83 pattern ∧ d83 pattern ≤ 10 := by
  unfold d83
  split
  · exact range58 pattern
  · exact range82 pattern
theorem range84 (pattern : Ten) : 0 ≤ d84 pattern ∧ d84 pattern ≤ 10 := by
  unfold d84
  split
  · exact range60 pattern
  · exact range56 pattern
theorem range85 (pattern : Ten) : 0 ≤ d85 pattern ∧ d85 pattern ≤ 10 := by
  unfold d85
  split
  · exact range84 pattern
  · exact range83 pattern
theorem range86 (pattern : Ten) : 0 ≤ d86 pattern ∧ d86 pattern ≤ 10 := by
  unfold d86
  split
  · exact range4 pattern
  · exact range0 pattern
theorem range87 (pattern : Ten) : 0 ≤ d87 pattern ∧ d87 pattern ≤ 10 := by
  unfold d87
  split
  · exact range0 pattern
  · exact range86 pattern
theorem range88 (pattern : Ten) : 0 ≤ d88 pattern ∧ d88 pattern ≤ 10 := by
  unfold d88
  split
  · exact range10 pattern
  · exact range0 pattern
theorem range89 (pattern : Ten) : 0 ≤ d89 pattern ∧ d89 pattern ≤ 10 := by
  unfold d89
  split
  · exact range11 pattern
  · exact range0 pattern
theorem range90 (pattern : Ten) : 0 ≤ d90 pattern ∧ d90 pattern ≤ 10 := by
  unfold d90
  split
  · exact range10 pattern
  · exact range11 pattern
theorem range91 (pattern : Ten) : 0 ≤ d91 pattern ∧ d91 pattern ≤ 10 := by
  unfold d91
  split
  · exact range2 pattern
  · exact range0 pattern
theorem range92 (pattern : Ten) : 0 ≤ d92 pattern ∧ d92 pattern ≤ 10 := by
  unfold d92
  split
  · exact range10 pattern
  · exact range2 pattern
theorem range93 (pattern : Ten) : 0 ≤ d93 pattern ∧ d93 pattern ≤ 10 := by
  unfold d93
  split
  · exact range88 pattern
  · exact range87 pattern
theorem range94 (pattern : Ten) : 0 ≤ d94 pattern ∧ d94 pattern ≤ 10 := by
  unfold d94
  split
  · exact range90 pattern
  · exact range89 pattern
theorem range95 (pattern : Ten) : 0 ≤ d95 pattern ∧ d95 pattern ≤ 10 := by
  unfold d95
  split
  · exact range92 pattern
  · exact range91 pattern
theorem range96 (pattern : Ten) : 0 ≤ d96 pattern ∧ d96 pattern ≤ 10 := by
  unfold d96
  split
  · exact range10 pattern
  · exact range88 pattern
theorem range97 (pattern : Ten) : 0 ≤ d97 pattern ∧ d97 pattern ≤ 10 := by
  unfold d97
  split
  · exact range10 pattern
  · exact range90 pattern
theorem range98 (pattern : Ten) : 0 ≤ d98 pattern ∧ d98 pattern ≤ 10 := by
  unfold d98
  split
  · exact range10 pattern
  · exact range92 pattern
theorem range99 (pattern : Ten) : 0 ≤ d99 pattern ∧ d99 pattern ≤ 10 := by
  unfold d99
  split
  · exact range94 pattern
  · exact range93 pattern
theorem range100 (pattern : Ten) : 0 ≤ d100 pattern ∧ d100 pattern ≤ 10 := by
  unfold d100
  split
  · exact range94 pattern
  · exact range95 pattern
theorem range101 (pattern : Ten) : 0 ≤ d101 pattern ∧ d101 pattern ≤ 10 := by
  unfold d101
  split
  · exact range97 pattern
  · exact range96 pattern
theorem range102 (pattern : Ten) : 0 ≤ d102 pattern ∧ d102 pattern ≤ 10 := by
  unfold d102
  split
  · exact range97 pattern
  · exact range98 pattern
theorem range103 (pattern : Ten) : 0 ≤ d103 pattern ∧ d103 pattern ≤ 10 := by
  unfold d103
  split
  · exact range100 pattern
  · exact range99 pattern
theorem range104 (pattern : Ten) : 0 ≤ d104 pattern ∧ d104 pattern ≤ 10 := by
  unfold d104
  split
  · exact range102 pattern
  · exact range101 pattern
theorem range105 (pattern : Ten) : 0 ≤ d105 pattern ∧ d105 pattern ≤ 10 := by
  unfold d105
  split
  · exact range104 pattern
  · exact range103 pattern
theorem range106 (pattern : Ten) : 0 ≤ d106 pattern ∧ d106 pattern ≤ 10 := by
  unfold d106
  split
  · exact range10 pattern
  · exact range104 pattern
theorem range107 (pattern : Ten) : 0 ≤ d107 pattern ∧ d107 pattern ≤ 10 := by
  unfold d107
  split
  · exact range106 pattern
  · exact range105 pattern
theorem range108 (pattern : Ten) : 0 ≤ d108 pattern ∧ d108 pattern ≤ 10 := by
  unfold d108
  split
  · exact range5 pattern
  · exact range15 pattern
theorem range109 (pattern : Ten) : 0 ≤ d109 pattern ∧ d109 pattern ≤ 10 := by
  unfold d109
  split
  · exact range15 pattern
  · exact range108 pattern
theorem range110 (pattern : Ten) : 0 ≤ d110 pattern ∧ d110 pattern ≤ 10 := by
  unfold d110
  split
  · exact range14 pattern
  · exact range15 pattern
theorem range111 (pattern : Ten) : 0 ≤ d111 pattern ∧ d111 pattern ≤ 10 := by
  unfold d111
  split
  · exact range44 pattern
  · exact range15 pattern
theorem range112 (pattern : Ten) : 0 ≤ d112 pattern ∧ d112 pattern ≤ 10 := by
  unfold d112
  split
  · exact range10 pattern
  · exact range15 pattern
theorem range113 (pattern : Ten) : 0 ≤ d113 pattern ∧ d113 pattern ≤ 10 := by
  unfold d113
  split
  · exact range10 pattern
  · exact range14 pattern
theorem range114 (pattern : Ten) : 0 ≤ d114 pattern ∧ d114 pattern ≤ 10 := by
  unfold d114
  split
  · exact range10 pattern
  · exact range44 pattern
theorem range115 (pattern : Ten) : 0 ≤ d115 pattern ∧ d115 pattern ≤ 10 := by
  unfold d115
  split
  · exact range110 pattern
  · exact range109 pattern
theorem range116 (pattern : Ten) : 0 ≤ d116 pattern ∧ d116 pattern ≤ 10 := by
  unfold d116
  split
  · exact range110 pattern
  · exact range111 pattern
theorem range117 (pattern : Ten) : 0 ≤ d117 pattern ∧ d117 pattern ≤ 10 := by
  unfold d117
  split
  · exact range113 pattern
  · exact range112 pattern
theorem range118 (pattern : Ten) : 0 ≤ d118 pattern ∧ d118 pattern ≤ 10 := by
  unfold d118
  split
  · exact range113 pattern
  · exact range114 pattern
theorem range119 (pattern : Ten) : 0 ≤ d119 pattern ∧ d119 pattern ≤ 10 := by
  unfold d119
  split
  · exact range116 pattern
  · exact range115 pattern
theorem range120 (pattern : Ten) : 0 ≤ d120 pattern ∧ d120 pattern ≤ 10 := by
  unfold d120
  split
  · exact range118 pattern
  · exact range117 pattern
theorem range121 (pattern : Ten) : 0 ≤ d121 pattern ∧ d121 pattern ≤ 10 := by
  unfold d121
  split
  · exact range120 pattern
  · exact range119 pattern
theorem range122 (pattern : Ten) : 0 ≤ d122 pattern ∧ d122 pattern ≤ 10 := by
  unfold d122
  split
  · exact range10 pattern
  · exact range120 pattern
theorem range123 (pattern : Ten) : 0 ≤ d123 pattern ∧ d123 pattern ≤ 10 := by
  unfold d123
  split
  · exact range122 pattern
  · exact range121 pattern
theorem range124 (pattern : Ten) : 0 ≤ d124 pattern ∧ d124 pattern ≤ 10 := by
  unfold d124
  split
  · exact range6 pattern
  · exact range48 pattern
theorem range125 (pattern : Ten) : 0 ≤ d125 pattern ∧ d125 pattern ≤ 10 := by
  unfold d125
  split
  · exact range48 pattern
  · exact range124 pattern
theorem range126 (pattern : Ten) : 0 ≤ d126 pattern ∧ d126 pattern ≤ 10 := by
  unfold d126
  split
  · exact range20 pattern
  · exact range48 pattern
theorem range127 (pattern : Ten) : 0 ≤ d127 pattern ∧ d127 pattern ≤ 10 := by
  unfold d127
  split
  · exact range20 pattern
  · exact range50 pattern
theorem range128 (pattern : Ten) : 0 ≤ d128 pattern ∧ d128 pattern ≤ 10 := by
  unfold d128
  split
  · exact range48 pattern
  · exact range125 pattern
theorem range129 (pattern : Ten) : 0 ≤ d129 pattern ∧ d129 pattern ≤ 10 := by
  unfold d129
  split
  · exact range127 pattern
  · exact range126 pattern
theorem range130 (pattern : Ten) : 0 ≤ d130 pattern ∧ d130 pattern ≤ 10 := by
  unfold d130
  split
  · exact range129 pattern
  · exact range128 pattern
theorem range131 (pattern : Ten) : 0 ≤ d131 pattern ∧ d131 pattern ≤ 10 := by
  unfold d131
  split
  · exact range10 pattern
  · exact range129 pattern
theorem range132 (pattern : Ten) : 0 ≤ d132 pattern ∧ d132 pattern ≤ 10 := by
  unfold d132
  split
  · exact range131 pattern
  · exact range130 pattern
theorem range133 (pattern : Ten) : 0 ≤ d133 pattern ∧ d133 pattern ≤ 10 := by
  unfold d133
  split
  · exact range7 pattern
  · exact range64 pattern
theorem range134 (pattern : Ten) : 0 ≤ d134 pattern ∧ d134 pattern ≤ 10 := by
  unfold d134
  split
  · exact range8 pattern
  · exact range54 pattern
theorem range135 (pattern : Ten) : 0 ≤ d135 pattern ∧ d135 pattern ≤ 10 := by
  unfold d135
  split
  · exact range56 pattern
  · exact range134 pattern
theorem range136 (pattern : Ten) : 0 ≤ d136 pattern ∧ d136 pattern ≤ 10 := by
  unfold d136
  split
  · exact range10 pattern
  · exact range4 pattern
theorem range137 (pattern : Ten) : 0 ≤ d137 pattern ∧ d137 pattern ≤ 10 := by
  unfold d137
  split
  · exact range10 pattern
  · exact range136 pattern
theorem range138 (pattern : Ten) : 0 ≤ d138 pattern ∧ d138 pattern ≤ 10 := by
  unfold d138
  split
  · exact range137 pattern
  · exact range0 pattern
theorem range139 (pattern : Ten) : 0 ≤ d139 pattern ∧ d139 pattern ≤ 10 := by
  unfold d139
  split
  · exact range12 pattern
  · exact range138 pattern
theorem range140 (pattern : Ten) : 0 ≤ d140 pattern ∧ d140 pattern ≤ 10 := by
  unfold d140
  split
  · exact range14 pattern
  · exact range12 pattern
theorem range141 (pattern : Ten) : 0 ≤ d141 pattern ∧ d141 pattern ≤ 10 := by
  unfold d141
  split
  · exact range16 pattern
  · exact range12 pattern
theorem range142 (pattern : Ten) : 0 ≤ d142 pattern ∧ d142 pattern ≤ 10 := by
  unfold d142
  split
  · exact range18 pattern
  · exact range139 pattern
theorem range143 (pattern : Ten) : 0 ≤ d143 pattern ∧ d143 pattern ≤ 10 := by
  unfold d143
  split
  · exact range20 pattern
  · exact range140 pattern
theorem range144 (pattern : Ten) : 0 ≤ d144 pattern ∧ d144 pattern ≤ 10 := by
  unfold d144
  split
  · exact range22 pattern
  · exact range141 pattern
theorem range145 (pattern : Ten) : 0 ≤ d145 pattern ∧ d145 pattern ≤ 10 := by
  unfold d145
  split
  · exact range143 pattern
  · exact range142 pattern
theorem range146 (pattern : Ten) : 0 ≤ d146 pattern ∧ d146 pattern ≤ 10 := by
  unfold d146
  split
  · exact range143 pattern
  · exact range144 pattern
theorem range147 (pattern : Ten) : 0 ≤ d147 pattern ∧ d147 pattern ≤ 10 := by
  unfold d147
  split
  · exact range146 pattern
  · exact range145 pattern
theorem range148 (pattern : Ten) : 0 ≤ d148 pattern ∧ d148 pattern ≤ 10 := by
  unfold d148
  split
  · exact range34 pattern
  · exact range147 pattern
theorem range149 (pattern : Ten) : 0 ≤ d149 pattern ∧ d149 pattern ≤ 10 := by
  unfold d149
  split
  · exact range36 pattern
  · exact range148 pattern
theorem range150 (pattern : Ten) : 0 ≤ d150 pattern ∧ d150 pattern ≤ 10 := by
  unfold d150
  split
  · exact range9 pattern
  · exact range54 pattern
theorem range151 (pattern : Ten) : 0 ≤ d151 pattern ∧ d151 pattern ≤ 10 := by
  unfold d151
  split
  · exact range54 pattern
  · exact range150 pattern
theorem range152 (pattern : Ten) : 0 ≤ d152 pattern ∧ d152 pattern ≤ 10 := by
  unfold d152
  split
  · exact range55 pattern
  · exact range54 pattern
theorem range153 (pattern : Ten) : 0 ≤ d153 pattern ∧ d153 pattern ≤ 10 := by
  unfold d153
  split
  · exact range57 pattern
  · exact range56 pattern
theorem range154 (pattern : Ten) : 0 ≤ d154 pattern ∧ d154 pattern ≤ 10 := by
  unfold d154
  split
  · exact range152 pattern
  · exact range151 pattern
theorem range155 (pattern : Ten) : 0 ≤ d155 pattern ∧ d155 pattern ≤ 10 := by
  unfold d155
  split
  · exact range153 pattern
  · exact range56 pattern
theorem range156 (pattern : Ten) : 0 ≤ d156 pattern ∧ d156 pattern ≤ 10 := by
  unfold d156
  split
  · exact range155 pattern
  · exact range154 pattern
theorem range157 (pattern : Ten) : 0 ≤ d157 pattern ∧ d157 pattern ≤ 10 := by
  unfold d157
  split
  · exact range6 pattern
  · exact range4 pattern
theorem range158 (pattern : Ten) : 0 ≤ d158 pattern ∧ d158 pattern ≤ 10 := by
  unfold d158
  split
  · exact range45 pattern
  · exact range157 pattern
theorem range159 (pattern : Ten) : 0 ≤ d159 pattern ∧ d159 pattern ≤ 10 := by
  unfold d159
  split
  · exact range10 pattern
  · exact range158 pattern
theorem range160 (pattern : Ten) : 0 ≤ d160 pattern ∧ d160 pattern ≤ 10 := by
  unfold d160
  split
  · exact range55 pattern
  · exact range54 pattern
theorem range161 (pattern : Ten) : 0 ≤ d161 pattern ∧ d161 pattern ≤ 10 := by
  unfold d161
  split
  · exact range159 pattern
  · exact range54 pattern
theorem range162 (pattern : Ten) : 0 ≤ d162 pattern ∧ d162 pattern ≤ 10 := by
  unfold d162
  split
  · exact range10 pattern
  · exact range54 pattern
theorem range163 (pattern : Ten) : 0 ≤ d163 pattern ∧ d163 pattern ≤ 10 := by
  unfold d163
  split
  · exact range10 pattern
  · exact range55 pattern
theorem range164 (pattern : Ten) : 0 ≤ d164 pattern ∧ d164 pattern ≤ 10 := by
  unfold d164
  split
  · exact range57 pattern
  · exact range56 pattern
theorem range165 (pattern : Ten) : 0 ≤ d165 pattern ∧ d165 pattern ≤ 10 := by
  unfold d165
  split
  · exact range161 pattern
  · exact range160 pattern
theorem range166 (pattern : Ten) : 0 ≤ d166 pattern ∧ d166 pattern ≤ 10 := by
  unfold d166
  split
  · exact range163 pattern
  · exact range162 pattern
theorem range167 (pattern : Ten) : 0 ≤ d167 pattern ∧ d167 pattern ≤ 10 := by
  unfold d167
  split
  · exact range60 pattern
  · exact range164 pattern
theorem range168 (pattern : Ten) : 0 ≤ d168 pattern ∧ d168 pattern ≤ 10 := by
  unfold d168
  split
  · exact range166 pattern
  · exact range165 pattern
theorem range169 (pattern : Ten) : 0 ≤ d169 pattern ∧ d169 pattern ≤ 10 := by
  unfold d169
  split
  · exact range63 pattern
  · exact range167 pattern
theorem range170 (pattern : Ten) : 0 ≤ d170 pattern ∧ d170 pattern ≤ 10 := by
  unfold d170
  split
  · exact range169 pattern
  · exact range168 pattern
theorem range171 (pattern : Ten) : 0 ≤ d171 pattern ∧ d171 pattern ≤ 10 := by
  unfold d171
  split
  · exact range1 pattern
  · exact range0 pattern
theorem range172 (pattern : Ten) : 0 ≤ d172 pattern ∧ d172 pattern ≤ 10 := by
  unfold d172
  split
  · exact range3 pattern
  · exact range2 pattern
theorem range173 (pattern : Ten) : 0 ≤ d173 pattern ∧ d173 pattern ≤ 10 := by
  unfold d173
  split
  · exact range10 pattern
  · exact range171 pattern
theorem range174 (pattern : Ten) : 0 ≤ d174 pattern ∧ d174 pattern ≤ 10 := by
  unfold d174
  split
  · exact range172 pattern
  · exact range171 pattern
theorem range175 (pattern : Ten) : 0 ≤ d175 pattern ∧ d175 pattern ≤ 10 := by
  unfold d175
  split
  · exact range10 pattern
  · exact range172 pattern
theorem range176 (pattern : Ten) : 0 ≤ d176 pattern ∧ d176 pattern ≤ 10 := by
  unfold d176
  split
  · exact range173 pattern
  · exact range171 pattern
theorem range177 (pattern : Ten) : 0 ≤ d177 pattern ∧ d177 pattern ≤ 10 := by
  unfold d177
  split
  · exact range10 pattern
  · exact range173 pattern
theorem range178 (pattern : Ten) : 0 ≤ d178 pattern ∧ d178 pattern ≤ 10 := by
  unfold d178
  split
  · exact range175 pattern
  · exact range174 pattern
theorem range179 (pattern : Ten) : 0 ≤ d179 pattern ∧ d179 pattern ≤ 10 := by
  unfold d179
  split
  · exact range10 pattern
  · exact range175 pattern
end NetHack.Sokoban41.Diagram
