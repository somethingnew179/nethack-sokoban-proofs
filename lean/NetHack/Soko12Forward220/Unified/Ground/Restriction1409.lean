import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1409_0_checked : (List.range' 721408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1409_1_checked : (List.range' 721536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1409_2_checked : (List.range' 721664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1409_3_checked : (List.range' 721792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1409_range (index : Nat) (lower : 721408 ≤ index) (upper : index < 721920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 721664 then
    if cut : index < 721536 then
      exact segment_sound _ 721408 128 Restriction1409_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 721536 128 Restriction1409_1_checked index (by omega) (by omega)
  else
    if cut : index < 721792 then
      exact segment_sound _ 721664 128 Restriction1409_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 721792 128 Restriction1409_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
