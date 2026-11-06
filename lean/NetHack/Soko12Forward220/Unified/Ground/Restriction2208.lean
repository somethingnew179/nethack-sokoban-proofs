import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2208_0_checked : (List.range' 1130496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2208_1_checked : (List.range' 1130624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2208_2_checked : (List.range' 1130752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2208_3_checked : (List.range' 1130880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2208_range (index : Nat) (lower : 1130496 ≤ index) (upper : index < 1131008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1130752 then
    if cut : index < 1130624 then
      exact segment_sound _ 1130496 128 Restriction2208_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1130624 128 Restriction2208_1_checked index (by omega) (by omega)
  else
    if cut : index < 1130880 then
      exact segment_sound _ 1130752 128 Restriction2208_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1130880 128 Restriction2208_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
