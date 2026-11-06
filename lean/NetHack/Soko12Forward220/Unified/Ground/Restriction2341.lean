import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2341_0_checked : (List.range' 1198592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2341_1_checked : (List.range' 1198720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2341_2_checked : (List.range' 1198848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2341_3_checked : (List.range' 1198976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2341_range (index : Nat) (lower : 1198592 ≤ index) (upper : index < 1199104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1198848 then
    if cut : index < 1198720 then
      exact segment_sound _ 1198592 128 Restriction2341_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1198720 128 Restriction2341_1_checked index (by omega) (by omega)
  else
    if cut : index < 1198976 then
      exact segment_sound _ 1198848 128 Restriction2341_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1198976 128 Restriction2341_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
