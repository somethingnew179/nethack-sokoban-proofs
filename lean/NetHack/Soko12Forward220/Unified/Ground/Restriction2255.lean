import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2255_0_checked : (List.range' 1154560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2255_1_checked : (List.range' 1154688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2255_2_checked : (List.range' 1154816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2255_3_checked : (List.range' 1154944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2255_range (index : Nat) (lower : 1154560 ≤ index) (upper : index < 1155072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1154816 then
    if cut : index < 1154688 then
      exact segment_sound _ 1154560 128 Restriction2255_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1154688 128 Restriction2255_1_checked index (by omega) (by omega)
  else
    if cut : index < 1154944 then
      exact segment_sound _ 1154816 128 Restriction2255_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1154944 128 Restriction2255_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
