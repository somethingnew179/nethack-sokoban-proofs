import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0093_0_checked : (List.range' 47616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0093_1_checked : (List.range' 47744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0093_2_checked : (List.range' 47872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0093_3_checked : (List.range' 48000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0093_range (index : Nat) (lower : 47616 ≤ index) (upper : index < 48128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 47872 then
    if cut : index < 47744 then
      exact segment_sound _ 47616 128 Restriction0093_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 47744 128 Restriction0093_1_checked index (by omega) (by omega)
  else
    if cut : index < 48000 then
      exact segment_sound _ 47872 128 Restriction0093_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 48000 128 Restriction0093_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
