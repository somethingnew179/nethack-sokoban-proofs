import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1339_0_checked : (List.range' 685568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1339_1_checked : (List.range' 685696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1339_2_checked : (List.range' 685824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1339_3_checked : (List.range' 685952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1339_range (index : Nat) (lower : 685568 ≤ index) (upper : index < 686080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 685824 then
    if cut : index < 685696 then
      exact segment_sound _ 685568 128 Restriction1339_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 685696 128 Restriction1339_1_checked index (by omega) (by omega)
  else
    if cut : index < 685952 then
      exact segment_sound _ 685824 128 Restriction1339_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 685952 128 Restriction1339_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
