import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0741_0_checked : (List.range' 379392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0741_1_checked : (List.range' 379520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0741_2_checked : (List.range' 379648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0741_3_checked : (List.range' 379776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0741_range (index : Nat) (lower : 379392 ≤ index) (upper : index < 379904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 379648 then
    if cut : index < 379520 then
      exact segment_sound _ 379392 128 Restriction0741_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 379520 128 Restriction0741_1_checked index (by omega) (by omega)
  else
    if cut : index < 379776 then
      exact segment_sound _ 379648 128 Restriction0741_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 379776 128 Restriction0741_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
