import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2037_0_checked : (List.range' 1042944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2037_1_checked : (List.range' 1043072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2037_2_checked : (List.range' 1043200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2037_3_checked : (List.range' 1043328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2037_range (index : Nat) (lower : 1042944 ≤ index) (upper : index < 1043456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1043200 then
    if cut : index < 1043072 then
      exact segment_sound _ 1042944 128 Restriction2037_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1043072 128 Restriction2037_1_checked index (by omega) (by omega)
  else
    if cut : index < 1043328 then
      exact segment_sound _ 1043200 128 Restriction2037_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1043328 128 Restriction2037_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
