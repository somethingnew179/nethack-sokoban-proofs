import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0801_0_checked : (List.range' 410112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0801_1_checked : (List.range' 410240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0801_2_checked : (List.range' 410368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0801_3_checked : (List.range' 410496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0801_range (index : Nat) (lower : 410112 ≤ index) (upper : index < 410624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 410368 then
    if cut : index < 410240 then
      exact segment_sound _ 410112 128 Restriction0801_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 410240 128 Restriction0801_1_checked index (by omega) (by omega)
  else
    if cut : index < 410496 then
      exact segment_sound _ 410368 128 Restriction0801_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 410496 128 Restriction0801_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
