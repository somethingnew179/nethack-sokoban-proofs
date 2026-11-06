import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2343_0_checked : (List.range' 1199616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2343_1_checked : (List.range' 1199744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2343_2_checked : (List.range' 1199872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2343_3_checked : (List.range' 1200000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2343_range (index : Nat) (lower : 1199616 ≤ index) (upper : index < 1200128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1199872 then
    if cut : index < 1199744 then
      exact segment_sound _ 1199616 128 Restriction2343_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1199744 128 Restriction2343_1_checked index (by omega) (by omega)
  else
    if cut : index < 1200000 then
      exact segment_sound _ 1199872 128 Restriction2343_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1200000 128 Restriction2343_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
