import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0197_0_checked : (List.range' 100864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0197_1_checked : (List.range' 100992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0197_2_checked : (List.range' 101120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0197_3_checked : (List.range' 101248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0197_range (index : Nat) (lower : 100864 ≤ index) (upper : index < 101376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 101120 then
    if cut : index < 100992 then
      exact segment_sound _ 100864 128 Restriction0197_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 100992 128 Restriction0197_1_checked index (by omega) (by omega)
  else
    if cut : index < 101248 then
      exact segment_sound _ 101120 128 Restriction0197_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 101248 128 Restriction0197_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
