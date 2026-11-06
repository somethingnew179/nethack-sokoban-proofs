import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0766_0_checked : (List.range' 392192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0766_1_checked : (List.range' 392320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0766_2_checked : (List.range' 392448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0766_3_checked : (List.range' 392576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0766_range (index : Nat) (lower : 392192 ≤ index) (upper : index < 392704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 392448 then
    if cut : index < 392320 then
      exact segment_sound _ 392192 128 Restriction0766_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 392320 128 Restriction0766_1_checked index (by omega) (by omega)
  else
    if cut : index < 392576 then
      exact segment_sound _ 392448 128 Restriction0766_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 392576 128 Restriction0766_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
