import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0245_0_checked : (List.range' 125440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0245_1_checked : (List.range' 125568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0245_2_checked : (List.range' 125696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0245_3_checked : (List.range' 125824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0245_range (index : Nat) (lower : 125440 ≤ index) (upper : index < 125952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 125696 then
    if cut : index < 125568 then
      exact segment_sound _ 125440 128 Restriction0245_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 125568 128 Restriction0245_1_checked index (by omega) (by omega)
  else
    if cut : index < 125824 then
      exact segment_sound _ 125696 128 Restriction0245_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 125824 128 Restriction0245_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
