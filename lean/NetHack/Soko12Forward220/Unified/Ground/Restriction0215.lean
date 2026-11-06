import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0215_0_checked : (List.range' 110080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0215_1_checked : (List.range' 110208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0215_2_checked : (List.range' 110336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0215_3_checked : (List.range' 110464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0215_range (index : Nat) (lower : 110080 ≤ index) (upper : index < 110592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 110336 then
    if cut : index < 110208 then
      exact segment_sound _ 110080 128 Restriction0215_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 110208 128 Restriction0215_1_checked index (by omega) (by omega)
  else
    if cut : index < 110464 then
      exact segment_sound _ 110336 128 Restriction0215_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 110464 128 Restriction0215_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
