import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0768_0_checked : (List.range' 393216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0768_1_checked : (List.range' 393344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0768_2_checked : (List.range' 393472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0768_3_checked : (List.range' 393600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0768_range (index : Nat) (lower : 393216 ≤ index) (upper : index < 393728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 393472 then
    if cut : index < 393344 then
      exact segment_sound _ 393216 128 Restriction0768_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 393344 128 Restriction0768_1_checked index (by omega) (by omega)
  else
    if cut : index < 393600 then
      exact segment_sound _ 393472 128 Restriction0768_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 393600 128 Restriction0768_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
