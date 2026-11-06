import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0301_0_checked : (List.range' 154112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0301_1_checked : (List.range' 154240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0301_2_checked : (List.range' 154368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0301_3_checked : (List.range' 154496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0301_range (index : Nat) (lower : 154112 ≤ index) (upper : index < 154624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 154368 then
    if cut : index < 154240 then
      exact segment_sound _ 154112 128 Restriction0301_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 154240 128 Restriction0301_1_checked index (by omega) (by omega)
  else
    if cut : index < 154496 then
      exact segment_sound _ 154368 128 Restriction0301_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 154496 128 Restriction0301_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
