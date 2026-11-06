import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0433_0_checked : (List.range' 221696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0433_1_checked : (List.range' 221824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0433_2_checked : (List.range' 221952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0433_3_checked : (List.range' 222080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0433_range (index : Nat) (lower : 221696 ≤ index) (upper : index < 222208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 221952 then
    if cut : index < 221824 then
      exact segment_sound _ 221696 128 Restriction0433_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 221824 128 Restriction0433_1_checked index (by omega) (by omega)
  else
    if cut : index < 222080 then
      exact segment_sound _ 221952 128 Restriction0433_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 222080 128 Restriction0433_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
