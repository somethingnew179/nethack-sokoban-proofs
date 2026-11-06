import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1404_0_checked : (List.range' 718848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1404_1_checked : (List.range' 718976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1404_2_checked : (List.range' 719104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1404_3_checked : (List.range' 719232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1404_range (index : Nat) (lower : 718848 ≤ index) (upper : index < 719360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 719104 then
    if cut : index < 718976 then
      exact segment_sound _ 718848 128 Restriction1404_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 718976 128 Restriction1404_1_checked index (by omega) (by omega)
  else
    if cut : index < 719232 then
      exact segment_sound _ 719104 128 Restriction1404_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 719232 128 Restriction1404_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
