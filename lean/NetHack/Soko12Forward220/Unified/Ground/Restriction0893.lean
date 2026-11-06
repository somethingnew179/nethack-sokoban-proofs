import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0893_0_checked : (List.range' 457216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0893_1_checked : (List.range' 457344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0893_2_checked : (List.range' 457472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0893_3_checked : (List.range' 457600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0893_range (index : Nat) (lower : 457216 ≤ index) (upper : index < 457728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 457472 then
    if cut : index < 457344 then
      exact segment_sound _ 457216 128 Restriction0893_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 457344 128 Restriction0893_1_checked index (by omega) (by omega)
  else
    if cut : index < 457600 then
      exact segment_sound _ 457472 128 Restriction0893_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 457600 128 Restriction0893_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
