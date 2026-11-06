import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0262_0_checked : (List.range' 134144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0262_1_checked : (List.range' 134272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0262_2_checked : (List.range' 134400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0262_3_checked : (List.range' 134528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0262_range (index : Nat) (lower : 134144 ≤ index) (upper : index < 134656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 134400 then
    if cut : index < 134272 then
      exact segment_sound _ 134144 128 Restriction0262_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 134272 128 Restriction0262_1_checked index (by omega) (by omega)
  else
    if cut : index < 134528 then
      exact segment_sound _ 134400 128 Restriction0262_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 134528 128 Restriction0262_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
