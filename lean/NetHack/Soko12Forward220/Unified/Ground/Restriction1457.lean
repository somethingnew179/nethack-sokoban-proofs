import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1457_0_checked : (List.range' 745984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1457_1_checked : (List.range' 746112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1457_2_checked : (List.range' 746240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1457_3_checked : (List.range' 746368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1457_range (index : Nat) (lower : 745984 ≤ index) (upper : index < 746496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 746240 then
    if cut : index < 746112 then
      exact segment_sound _ 745984 128 Restriction1457_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 746112 128 Restriction1457_1_checked index (by omega) (by omega)
  else
    if cut : index < 746368 then
      exact segment_sound _ 746240 128 Restriction1457_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 746368 128 Restriction1457_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
