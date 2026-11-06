import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1571_0_checked : (List.range' 804352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1571_1_checked : (List.range' 804480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1571_2_checked : (List.range' 804608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1571_3_checked : (List.range' 804736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1571_range (index : Nat) (lower : 804352 ≤ index) (upper : index < 804864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 804608 then
    if cut : index < 804480 then
      exact segment_sound _ 804352 128 Restriction1571_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 804480 128 Restriction1571_1_checked index (by omega) (by omega)
  else
    if cut : index < 804736 then
      exact segment_sound _ 804608 128 Restriction1571_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 804736 128 Restriction1571_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
