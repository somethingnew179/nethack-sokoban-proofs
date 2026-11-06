import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2083_0_checked : (List.range' 1066496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2083_1_checked : (List.range' 1066624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2083_2_checked : (List.range' 1066752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2083_3_checked : (List.range' 1066880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2083_range (index : Nat) (lower : 1066496 ≤ index) (upper : index < 1067008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1066752 then
    if cut : index < 1066624 then
      exact segment_sound _ 1066496 128 Restriction2083_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1066624 128 Restriction2083_1_checked index (by omega) (by omega)
  else
    if cut : index < 1066880 then
      exact segment_sound _ 1066752 128 Restriction2083_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1066880 128 Restriction2083_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
