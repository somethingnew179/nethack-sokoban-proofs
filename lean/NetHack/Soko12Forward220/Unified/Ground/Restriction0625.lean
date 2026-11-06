import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0625_0_checked : (List.range' 320000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0625_1_checked : (List.range' 320128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0625_2_checked : (List.range' 320256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0625_3_checked : (List.range' 320384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0625_range (index : Nat) (lower : 320000 ≤ index) (upper : index < 320512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 320256 then
    if cut : index < 320128 then
      exact segment_sound _ 320000 128 Restriction0625_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 320128 128 Restriction0625_1_checked index (by omega) (by omega)
  else
    if cut : index < 320384 then
      exact segment_sound _ 320256 128 Restriction0625_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 320384 128 Restriction0625_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
