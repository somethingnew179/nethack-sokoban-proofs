import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1255_0_checked : (List.range' 642560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1255_1_checked : (List.range' 642688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1255_2_checked : (List.range' 642816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1255_3_checked : (List.range' 642944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1255_range (index : Nat) (lower : 642560 ≤ index) (upper : index < 643072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 642816 then
    if cut : index < 642688 then
      exact segment_sound _ 642560 128 Restriction1255_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 642688 128 Restriction1255_1_checked index (by omega) (by omega)
  else
    if cut : index < 642944 then
      exact segment_sound _ 642816 128 Restriction1255_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 642944 128 Restriction1255_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
