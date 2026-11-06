import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1259_0_checked : (List.range' 644608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1259_1_checked : (List.range' 644736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1259_2_checked : (List.range' 644864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1259_3_checked : (List.range' 644992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1259_range (index : Nat) (lower : 644608 ≤ index) (upper : index < 645120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 644864 then
    if cut : index < 644736 then
      exact segment_sound _ 644608 128 Restriction1259_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 644736 128 Restriction1259_1_checked index (by omega) (by omega)
  else
    if cut : index < 644992 then
      exact segment_sound _ 644864 128 Restriction1259_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 644992 128 Restriction1259_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
