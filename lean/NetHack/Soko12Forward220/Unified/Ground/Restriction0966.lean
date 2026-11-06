import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0966_0_checked : (List.range' 494592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0966_1_checked : (List.range' 494720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0966_2_checked : (List.range' 494848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0966_3_checked : (List.range' 494976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0966_range (index : Nat) (lower : 494592 ≤ index) (upper : index < 495104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 494848 then
    if cut : index < 494720 then
      exact segment_sound _ 494592 128 Restriction0966_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 494720 128 Restriction0966_1_checked index (by omega) (by omega)
  else
    if cut : index < 494976 then
      exact segment_sound _ 494848 128 Restriction0966_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 494976 128 Restriction0966_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
