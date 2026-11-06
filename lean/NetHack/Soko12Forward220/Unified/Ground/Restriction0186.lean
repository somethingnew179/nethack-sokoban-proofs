import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0186_0_checked : (List.range' 95232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0186_1_checked : (List.range' 95360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0186_2_checked : (List.range' 95488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0186_3_checked : (List.range' 95616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0186_range (index : Nat) (lower : 95232 ≤ index) (upper : index < 95744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 95488 then
    if cut : index < 95360 then
      exact segment_sound _ 95232 128 Restriction0186_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 95360 128 Restriction0186_1_checked index (by omega) (by omega)
  else
    if cut : index < 95616 then
      exact segment_sound _ 95488 128 Restriction0186_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 95616 128 Restriction0186_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
