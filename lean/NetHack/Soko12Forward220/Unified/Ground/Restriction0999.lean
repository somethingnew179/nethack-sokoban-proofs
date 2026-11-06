import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0999_0_checked : (List.range' 511488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0999_1_checked : (List.range' 511616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0999_2_checked : (List.range' 511744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0999_3_checked : (List.range' 511872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0999_range (index : Nat) (lower : 511488 ≤ index) (upper : index < 512000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 511744 then
    if cut : index < 511616 then
      exact segment_sound _ 511488 128 Restriction0999_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 511616 128 Restriction0999_1_checked index (by omega) (by omega)
  else
    if cut : index < 511872 then
      exact segment_sound _ 511744 128 Restriction0999_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 511872 128 Restriction0999_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
