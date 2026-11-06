import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1087_0_checked : (List.range' 556544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1087_1_checked : (List.range' 556672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1087_2_checked : (List.range' 556800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1087_3_checked : (List.range' 556928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1087_range (index : Nat) (lower : 556544 ≤ index) (upper : index < 557056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 556800 then
    if cut : index < 556672 then
      exact segment_sound _ 556544 128 Restriction1087_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 556672 128 Restriction1087_1_checked index (by omega) (by omega)
  else
    if cut : index < 556928 then
      exact segment_sound _ 556800 128 Restriction1087_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 556928 128 Restriction1087_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
