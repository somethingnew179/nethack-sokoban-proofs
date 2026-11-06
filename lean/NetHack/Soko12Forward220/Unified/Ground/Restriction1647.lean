import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1647_0_checked : (List.range' 843264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1647_1_checked : (List.range' 843392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1647_2_checked : (List.range' 843520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1647_3_checked : (List.range' 843648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1647_range (index : Nat) (lower : 843264 ≤ index) (upper : index < 843776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 843520 then
    if cut : index < 843392 then
      exact segment_sound _ 843264 128 Restriction1647_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 843392 128 Restriction1647_1_checked index (by omega) (by omega)
  else
    if cut : index < 843648 then
      exact segment_sound _ 843520 128 Restriction1647_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 843648 128 Restriction1647_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
