import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1220_0_checked : (List.range' 624640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1220_1_checked : (List.range' 624768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1220_2_checked : (List.range' 624896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1220_3_checked : (List.range' 625024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1220_range (index : Nat) (lower : 624640 ≤ index) (upper : index < 625152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 624896 then
    if cut : index < 624768 then
      exact segment_sound _ 624640 128 Restriction1220_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 624768 128 Restriction1220_1_checked index (by omega) (by omega)
  else
    if cut : index < 625024 then
      exact segment_sound _ 624896 128 Restriction1220_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 625024 128 Restriction1220_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
