import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0248_0_checked : (List.range' 126976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0248_1_checked : (List.range' 127104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0248_2_checked : (List.range' 127232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0248_3_checked : (List.range' 127360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0248_range (index : Nat) (lower : 126976 ≤ index) (upper : index < 127488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 127232 then
    if cut : index < 127104 then
      exact segment_sound _ 126976 128 Restriction0248_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 127104 128 Restriction0248_1_checked index (by omega) (by omega)
  else
    if cut : index < 127360 then
      exact segment_sound _ 127232 128 Restriction0248_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 127360 128 Restriction0248_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
