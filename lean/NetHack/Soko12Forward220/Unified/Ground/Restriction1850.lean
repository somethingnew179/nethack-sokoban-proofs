import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1850_0_checked : (List.range' 947200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1850_1_checked : (List.range' 947328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1850_2_checked : (List.range' 947456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1850_3_checked : (List.range' 947584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1850_range (index : Nat) (lower : 947200 ≤ index) (upper : index < 947712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 947456 then
    if cut : index < 947328 then
      exact segment_sound _ 947200 128 Restriction1850_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 947328 128 Restriction1850_1_checked index (by omega) (by omega)
  else
    if cut : index < 947584 then
      exact segment_sound _ 947456 128 Restriction1850_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 947584 128 Restriction1850_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
