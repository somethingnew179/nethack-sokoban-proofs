import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0207_0_checked : (List.range' 105984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0207_1_checked : (List.range' 106112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0207_2_checked : (List.range' 106240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0207_3_checked : (List.range' 106368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0207_range (index : Nat) (lower : 105984 ≤ index) (upper : index < 106496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 106240 then
    if cut : index < 106112 then
      exact segment_sound _ 105984 128 Restriction0207_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 106112 128 Restriction0207_1_checked index (by omega) (by omega)
  else
    if cut : index < 106368 then
      exact segment_sound _ 106240 128 Restriction0207_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 106368 128 Restriction0207_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
