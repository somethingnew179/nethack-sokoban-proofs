import NetHack.Soko32Penalty5.Checks000
import NetHack.Soko32Penalty5.Checks001
import NetHack.Soko32Penalty5.Checks002
import NetHack.Soko32Penalty5.Checks003
import NetHack.Soko32Penalty5.Checks004
import NetHack.Soko32Penalty5.Checks005
import NetHack.Soko32Penalty5.Checks006
import NetHack.Soko32Penalty5.Checks007
import NetHack.Soko32Penalty5.Checks008
import NetHack.Soko32Penalty5.Checks009
import NetHack.Soko32Penalty5.Checks010
import NetHack.Soko32Penalty5.Checks011
import NetHack.Soko32Penalty5.Checks012
import NetHack.Soko32Penalty5.Checks013
import NetHack.Soko32Penalty5.Checks014
import NetHack.Soko32Penalty5.Checks015
import NetHack.Soko32Penalty5.Checks016
import NetHack.Soko32Penalty5.Checks017
import NetHack.Soko32Penalty5.Checks018
import NetHack.Soko32Penalty5.Checks019
import NetHack.Soko32Penalty5.Checks020
import NetHack.Soko32Penalty5.Checks021
import NetHack.Soko32Penalty5.Checks022
import NetHack.Soko32Penalty5.Checks023
import NetHack.Soko32Penalty5.Checks024
import NetHack.Soko32Penalty5.Checks025
import NetHack.Soko32Penalty5.Checks026
import NetHack.Soko32Penalty5.Checks027
import NetHack.Soko32Penalty5.Checks028
import NetHack.Soko32Penalty5.Checks029
import NetHack.Soko32Penalty5.Checks030
import NetHack.Soko32Penalty5.Checks031
import NetHack.Soko32Penalty5.Checks032
import NetHack.Soko32Penalty5.Checks033
import NetHack.Soko32Penalty5.Checks034
import NetHack.Soko32Penalty5.Checks035
import NetHack.Soko32Penalty5.Checks036
import NetHack.Soko32Penalty5.Checks037
import NetHack.Soko32Penalty5.Checks038
import NetHack.Soko32Penalty5.Checks039
import NetHack.Soko32Penalty5.Checks040
import NetHack.Soko32Penalty5.Checks041
import NetHack.Soko32Penalty5.Checks042
import NetHack.Soko32Penalty5.Checks043
import NetHack.Soko32Penalty5.Checks044
import NetHack.Soko32Penalty5.Checks045
import NetHack.Soko32Penalty5.Checks046
import NetHack.Soko32Penalty5.Checks047
import NetHack.Soko32Penalty5.Checks048
import NetHack.Soko32Penalty5.Checks049
import NetHack.Soko32Penalty5.Checks050
import NetHack.Soko32Penalty5.Checks051
import NetHack.Soko32Penalty5.Checks052
import NetHack.Soko32Penalty5.Checks053
import NetHack.Soko32Penalty5.Checks054
import NetHack.Soko32Penalty5.Checks055
import NetHack.Soko32Penalty5.Checks056
import NetHack.Soko32Penalty5.Checks057
import NetHack.Soko32Penalty5.Checks058
import NetHack.Soko32Penalty5.Checks059
import NetHack.Soko32Penalty5.Checks060
import NetHack.Soko32Penalty5.Checks061
import NetHack.Soko32Penalty5.Checks062
import NetHack.Soko32Penalty5.Checks063
import NetHack.Soko32Penalty5.Checks064
import NetHack.Soko32Penalty5.Checks065
import NetHack.Soko32Penalty5.Checks066
import NetHack.Soko32Penalty5.Checks067
import NetHack.Soko32Penalty5.Checks068
import NetHack.Soko32Penalty5.Checks069
import NetHack.Soko32Penalty5.Checks070
import NetHack.Soko32Penalty5.Checks071
import NetHack.Soko32Penalty5.Checks072
import NetHack.Soko32Penalty5.Checks073
import NetHack.Soko32Penalty5.Checks074
import NetHack.Soko32Penalty5.Checks075
import NetHack.Soko32Penalty5.Checks076
import NetHack.Soko32Penalty5.Checks077
import NetHack.Soko32Penalty5.Checks078
import NetHack.Soko32Penalty5.Checks079
import NetHack.Soko32Penalty5.Checks080
import NetHack.Soko32Penalty5.Checks081
import NetHack.Soko32Penalty5.Checks082
import NetHack.Soko32Penalty5.Checks083
import NetHack.Soko32Penalty5.Checks084
import NetHack.Soko32Penalty5.Checks085
import NetHack.Soko32Penalty5.Checks086
import NetHack.Soko32Penalty5.OriginalTrace
import NetHack.Soko32Penalty5.TableTools
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem indices_checked : (List.range' 0 5531).all
    (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) = true :=
  (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 0 64 5467 checks000 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 64 64 5403 checks001 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 128 64 5339 checks002 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 192 64 5275 checks003 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 256 64 5211 checks004 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 320 64 5147 checks005 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 384 64 5083 checks006 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 448 64 5019 checks007 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 512 64 4955 checks008 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 576 64 4891 checks009 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 640 64 4827 checks010 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 704 64 4763 checks011 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 768 64 4699 checks012 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 832 64 4635 checks013 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 896 64 4571 checks014 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 960 64 4507 checks015 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1024 64 4443 checks016 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1088 64 4379 checks017 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1152 64 4315 checks018 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1216 64 4251 checks019 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1280 64 4187 checks020 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1344 64 4123 checks021 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1408 64 4059 checks022 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1472 64 3995 checks023 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1536 64 3931 checks024 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1600 64 3867 checks025 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1664 64 3803 checks026 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1728 64 3739 checks027 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1792 64 3675 checks028 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1856 64 3611 checks029 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1920 64 3547 checks030 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 1984 64 3483 checks031 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2048 64 3419 checks032 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2112 64 3355 checks033 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2176 64 3291 checks034 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2240 64 3227 checks035 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2304 64 3163 checks036 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2368 64 3099 checks037 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2432 64 3035 checks038 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2496 64 2971 checks039 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2560 64 2907 checks040 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2624 64 2843 checks041 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2688 64 2779 checks042 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2752 64 2715 checks043 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2816 64 2651 checks044 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2880 64 2587 checks045 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 2944 64 2523 checks046 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3008 64 2459 checks047 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3072 64 2395 checks048 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3136 64 2331 checks049 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3200 64 2267 checks050 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3264 64 2203 checks051 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3328 64 2139 checks052 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3392 64 2075 checks053 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3456 64 2011 checks054 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3520 64 1947 checks055 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3584 64 1883 checks056 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3648 64 1819 checks057 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3712 64 1755 checks058 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3776 64 1691 checks059 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3840 64 1627 checks060 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3904 64 1563 checks061 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 3968 64 1499 checks062 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4032 64 1435 checks063 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4096 64 1371 checks064 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4160 64 1307 checks065 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4224 64 1243 checks066 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4288 64 1179 checks067 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4352 64 1115 checks068 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4416 64 1051 checks069 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4480 64 987 checks070 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4544 64 923 checks071 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4608 64 859 checks072 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4672 64 795 checks073 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4736 64 731 checks074 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4800 64 667 checks075 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4864 64 603 checks076 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4928 64 539 checks077 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 4992 64 475 checks078 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5056 64 411 checks079 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5120 64 347 checks080 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5184 64 283 checks081 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5248 64 219 checks082 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5312 64 155 checks083 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5376 64 91 checks084 (range_join (fun i => fastCheck table i (IndexedCertificateTable.get zeroRow table i)) 5440 64 27 checks085 checks086))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem keys_checked : IndexedCertificateTable.all (fun key _ => decide (key < 5531)) table = true := by decide +kernel

theorem table_sound (i : Nat) : Sound heroes actions table (IndexedCertificateTable.get zeroRow table i) := by
  apply check_sound heroes actions table i
  by_cases below : i < 5531
  · apply fastCheck_implies
    exact List.all_eq_true.mp indices_checked i (List.mem_range'.mpr ⟨i,below,by omega⟩)
  · have zero := get_above zeroRow table 5531 i keys_checked (by omega)
    rw [zero]
    rfl

theorem initial_ticket : Ticket heroes table initialGroup soko3_2.initial.player 5 := by
  have result := Ticket.row (heroes := heroes) (table := table) (boxes := initialGroup)
    (hero := soko3_2.initial.player) 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact result

/-- Universal original-start lower139, not a claimed optimum or move bound. -/
theorem pushes_lower_bound {dirs : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial dirs final pushes moves) (goal : Goal final) :
    139 ≤ pushes := original_lower_of_checked_table table table_sound initial_ticket trace goal

end NetHack.Soko32Penalty5
