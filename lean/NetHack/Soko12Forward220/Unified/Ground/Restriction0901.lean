import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0901_0_checked : (List.range' 461312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0901_1_checked : (List.range' 461440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0901_2_checked : (List.range' 461568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0901_3_checked : (List.range' 461696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0901_range (index : Nat) (lower : 461312 ≤ index) (upper : index < 461824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 461568 then
    if cut : index < 461440 then
      exact segment_sound _ 461312 128 Restriction0901_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 461440 128 Restriction0901_1_checked index (by omega) (by omega)
  else
    if cut : index < 461696 then
      exact segment_sound _ 461568 128 Restriction0901_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 461696 128 Restriction0901_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
