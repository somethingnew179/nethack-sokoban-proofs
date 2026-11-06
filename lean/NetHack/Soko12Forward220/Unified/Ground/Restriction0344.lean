import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0344_0_checked : (List.range' 176128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0344_1_checked : (List.range' 176256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0344_2_checked : (List.range' 176384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0344_3_checked : (List.range' 176512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0344_range (index : Nat) (lower : 176128 ≤ index) (upper : index < 176640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 176384 then
    if cut : index < 176256 then
      exact segment_sound _ 176128 128 Restriction0344_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 176256 128 Restriction0344_1_checked index (by omega) (by omega)
  else
    if cut : index < 176512 then
      exact segment_sound _ 176384 128 Restriction0344_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 176512 128 Restriction0344_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
