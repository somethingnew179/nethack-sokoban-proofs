import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2591_0_checked : (List.range' 1326592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2591_1_checked : (List.range' 1326720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2591_2_checked : (List.range' 1326848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2591_3_checked : (List.range' 1326976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2591_range (index : Nat) (lower : 1326592 ≤ index) (upper : index < 1327104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1326848 then
    if cut : index < 1326720 then
      exact segment_sound _ 1326592 128 Restriction2591_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1326720 128 Restriction2591_1_checked index (by omega) (by omega)
  else
    if cut : index < 1326976 then
      exact segment_sound _ 1326848 128 Restriction2591_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1326976 128 Restriction2591_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
