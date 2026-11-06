import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1183_0_checked : (List.range' 605696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1183_1_checked : (List.range' 605824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1183_2_checked : (List.range' 605952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1183_3_checked : (List.range' 606080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1183_range (index : Nat) (lower : 605696 ≤ index) (upper : index < 606208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 605952 then
    if cut : index < 605824 then
      exact segment_sound _ 605696 128 Restriction1183_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 605824 128 Restriction1183_1_checked index (by omega) (by omega)
  else
    if cut : index < 606080 then
      exact segment_sound _ 605952 128 Restriction1183_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 606080 128 Restriction1183_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
