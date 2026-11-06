import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0769_0_checked : (List.range' 393728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0769_1_checked : (List.range' 393856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0769_2_checked : (List.range' 393984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0769_3_checked : (List.range' 394112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0769_range (index : Nat) (lower : 393728 ≤ index) (upper : index < 394240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 393984 then
    if cut : index < 393856 then
      exact segment_sound _ 393728 128 Restriction0769_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 393856 128 Restriction0769_1_checked index (by omega) (by omega)
  else
    if cut : index < 394112 then
      exact segment_sound _ 393984 128 Restriction0769_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 394112 128 Restriction0769_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
