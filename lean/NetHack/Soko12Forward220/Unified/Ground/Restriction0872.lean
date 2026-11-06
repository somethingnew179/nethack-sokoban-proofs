import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0872_0_checked : (List.range' 446464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0872_1_checked : (List.range' 446592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0872_2_checked : (List.range' 446720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0872_3_checked : (List.range' 446848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0872_range (index : Nat) (lower : 446464 ≤ index) (upper : index < 446976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 446720 then
    if cut : index < 446592 then
      exact segment_sound _ 446464 128 Restriction0872_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 446592 128 Restriction0872_1_checked index (by omega) (by omega)
  else
    if cut : index < 446848 then
      exact segment_sound _ 446720 128 Restriction0872_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 446848 128 Restriction0872_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
