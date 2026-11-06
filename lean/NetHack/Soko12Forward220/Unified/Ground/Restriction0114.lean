import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0114_0_checked : (List.range' 58368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0114_1_checked : (List.range' 58496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0114_2_checked : (List.range' 58624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0114_3_checked : (List.range' 58752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0114_range (index : Nat) (lower : 58368 ≤ index) (upper : index < 58880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 58624 then
    if cut : index < 58496 then
      exact segment_sound _ 58368 128 Restriction0114_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 58496 128 Restriction0114_1_checked index (by omega) (by omega)
  else
    if cut : index < 58752 then
      exact segment_sound _ 58624 128 Restriction0114_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 58752 128 Restriction0114_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
