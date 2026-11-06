import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1203_0_checked : (List.range' 615936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1203_1_checked : (List.range' 616064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1203_2_checked : (List.range' 616192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1203_3_checked : (List.range' 616320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1203_range (index : Nat) (lower : 615936 ≤ index) (upper : index < 616448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 616192 then
    if cut : index < 616064 then
      exact segment_sound _ 615936 128 Restriction1203_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 616064 128 Restriction1203_1_checked index (by omega) (by omega)
  else
    if cut : index < 616320 then
      exact segment_sound _ 616192 128 Restriction1203_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 616320 128 Restriction1203_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
