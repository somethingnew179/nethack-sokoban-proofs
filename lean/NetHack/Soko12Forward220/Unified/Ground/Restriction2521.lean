import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2521_0_checked : (List.range' 1290752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2521_1_checked : (List.range' 1290880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2521_2_checked : (List.range' 1291008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2521_3_checked : (List.range' 1291136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2521_range (index : Nat) (lower : 1290752 ≤ index) (upper : index < 1291264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1291008 then
    if cut : index < 1290880 then
      exact segment_sound _ 1290752 128 Restriction2521_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1290880 128 Restriction2521_1_checked index (by omega) (by omega)
  else
    if cut : index < 1291136 then
      exact segment_sound _ 1291008 128 Restriction2521_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1291136 128 Restriction2521_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
