import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0528_0_checked : (List.range' 270336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0528_1_checked : (List.range' 270464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0528_2_checked : (List.range' 270592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0528_3_checked : (List.range' 270720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0528_range (index : Nat) (lower : 270336 ≤ index) (upper : index < 270848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 270592 then
    if cut : index < 270464 then
      exact segment_sound _ 270336 128 Restriction0528_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270464 128 Restriction0528_1_checked index (by omega) (by omega)
  else
    if cut : index < 270720 then
      exact segment_sound _ 270592 128 Restriction0528_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270720 128 Restriction0528_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
