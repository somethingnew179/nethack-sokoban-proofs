import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1412_0_checked : (List.range' 722944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1412_1_checked : (List.range' 723072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1412_2_checked : (List.range' 723200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1412_3_checked : (List.range' 723328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1412_range (index : Nat) (lower : 722944 ≤ index) (upper : index < 723456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 723200 then
    if cut : index < 723072 then
      exact segment_sound _ 722944 128 Restriction1412_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 723072 128 Restriction1412_1_checked index (by omega) (by omega)
  else
    if cut : index < 723328 then
      exact segment_sound _ 723200 128 Restriction1412_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 723328 128 Restriction1412_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
