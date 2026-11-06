import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0655_0_checked : (List.range' 335360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0655_1_checked : (List.range' 335488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0655_2_checked : (List.range' 335616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0655_3_checked : (List.range' 335744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0655_range (index : Nat) (lower : 335360 ≤ index) (upper : index < 335872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 335616 then
    if cut : index < 335488 then
      exact segment_sound _ 335360 128 Restriction0655_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 335488 128 Restriction0655_1_checked index (by omega) (by omega)
  else
    if cut : index < 335744 then
      exact segment_sound _ 335616 128 Restriction0655_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 335744 128 Restriction0655_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
