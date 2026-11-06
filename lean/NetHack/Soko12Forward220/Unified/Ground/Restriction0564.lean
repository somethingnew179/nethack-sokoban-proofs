import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0564_0_checked : (List.range' 288768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0564_1_checked : (List.range' 288896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0564_2_checked : (List.range' 289024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0564_3_checked : (List.range' 289152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0564_range (index : Nat) (lower : 288768 ≤ index) (upper : index < 289280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 289024 then
    if cut : index < 288896 then
      exact segment_sound _ 288768 128 Restriction0564_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 288896 128 Restriction0564_1_checked index (by omega) (by omega)
  else
    if cut : index < 289152 then
      exact segment_sound _ 289024 128 Restriction0564_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 289152 128 Restriction0564_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
