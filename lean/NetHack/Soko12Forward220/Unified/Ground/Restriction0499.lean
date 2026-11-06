import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0499_0_checked : (List.range' 255488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0499_1_checked : (List.range' 255616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0499_2_checked : (List.range' 255744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0499_3_checked : (List.range' 255872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0499_range (index : Nat) (lower : 255488 ≤ index) (upper : index < 256000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 255744 then
    if cut : index < 255616 then
      exact segment_sound _ 255488 128 Restriction0499_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 255616 128 Restriction0499_1_checked index (by omega) (by omega)
  else
    if cut : index < 255872 then
      exact segment_sound _ 255744 128 Restriction0499_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 255872 128 Restriction0499_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
