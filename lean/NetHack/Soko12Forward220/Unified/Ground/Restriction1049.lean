import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1049_0_checked : (List.range' 537088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1049_1_checked : (List.range' 537216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1049_2_checked : (List.range' 537344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1049_3_checked : (List.range' 537472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1049_range (index : Nat) (lower : 537088 ≤ index) (upper : index < 537600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 537344 then
    if cut : index < 537216 then
      exact segment_sound _ 537088 128 Restriction1049_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 537216 128 Restriction1049_1_checked index (by omega) (by omega)
  else
    if cut : index < 537472 then
      exact segment_sound _ 537344 128 Restriction1049_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 537472 128 Restriction1049_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
