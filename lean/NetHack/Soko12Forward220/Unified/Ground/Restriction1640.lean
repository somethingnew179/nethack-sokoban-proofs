import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1640_0_checked : (List.range' 839680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1640_1_checked : (List.range' 839808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1640_2_checked : (List.range' 839936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1640_3_checked : (List.range' 840064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1640_range (index : Nat) (lower : 839680 ≤ index) (upper : index < 840192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 839936 then
    if cut : index < 839808 then
      exact segment_sound _ 839680 128 Restriction1640_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 839808 128 Restriction1640_1_checked index (by omega) (by omega)
  else
    if cut : index < 840064 then
      exact segment_sound _ 839936 128 Restriction1640_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 840064 128 Restriction1640_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
