import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2249_0_checked : (List.range' 1151488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2249_1_checked : (List.range' 1151616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2249_2_checked : (List.range' 1151744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2249_3_checked : (List.range' 1151872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2249_range (index : Nat) (lower : 1151488 ≤ index) (upper : index < 1152000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1151744 then
    if cut : index < 1151616 then
      exact segment_sound _ 1151488 128 Restriction2249_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1151616 128 Restriction2249_1_checked index (by omega) (by omega)
  else
    if cut : index < 1151872 then
      exact segment_sound _ 1151744 128 Restriction2249_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1151872 128 Restriction2249_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
