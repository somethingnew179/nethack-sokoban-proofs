import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0968_0_checked : (List.range' 495616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0968_1_checked : (List.range' 495744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0968_2_checked : (List.range' 495872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0968_3_checked : (List.range' 496000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0968_range (index : Nat) (lower : 495616 ≤ index) (upper : index < 496128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 495872 then
    if cut : index < 495744 then
      exact segment_sound _ 495616 128 Restriction0968_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 495744 128 Restriction0968_1_checked index (by omega) (by omega)
  else
    if cut : index < 496000 then
      exact segment_sound _ 495872 128 Restriction0968_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 496000 128 Restriction0968_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
