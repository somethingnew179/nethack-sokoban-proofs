import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0962_0_checked : (List.range' 492544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0962_1_checked : (List.range' 492672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0962_2_checked : (List.range' 492800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0962_3_checked : (List.range' 492928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0962_range (index : Nat) (lower : 492544 ≤ index) (upper : index < 493056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 492800 then
    if cut : index < 492672 then
      exact segment_sound _ 492544 128 Restriction0962_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 492672 128 Restriction0962_1_checked index (by omega) (by omega)
  else
    if cut : index < 492928 then
      exact segment_sound _ 492800 128 Restriction0962_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 492928 128 Restriction0962_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
