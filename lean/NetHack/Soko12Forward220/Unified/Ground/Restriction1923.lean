import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1923_0_checked : (List.range' 984576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1923_1_checked : (List.range' 984704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1923_2_checked : (List.range' 984832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1923_3_checked : (List.range' 984960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1923_range (index : Nat) (lower : 984576 ≤ index) (upper : index < 985088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 984832 then
    if cut : index < 984704 then
      exact segment_sound _ 984576 128 Restriction1923_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 984704 128 Restriction1923_1_checked index (by omega) (by omega)
  else
    if cut : index < 984960 then
      exact segment_sound _ 984832 128 Restriction1923_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 984960 128 Restriction1923_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
