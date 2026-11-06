import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0331_0_checked : (List.range' 169472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0331_1_checked : (List.range' 169600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0331_2_checked : (List.range' 169728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0331_3_checked : (List.range' 169856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0331_range (index : Nat) (lower : 169472 ≤ index) (upper : index < 169984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 169728 then
    if cut : index < 169600 then
      exact segment_sound _ 169472 128 Restriction0331_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 169600 128 Restriction0331_1_checked index (by omega) (by omega)
  else
    if cut : index < 169856 then
      exact segment_sound _ 169728 128 Restriction0331_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 169856 128 Restriction0331_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
