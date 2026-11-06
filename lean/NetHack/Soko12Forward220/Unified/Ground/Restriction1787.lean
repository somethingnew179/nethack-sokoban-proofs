import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1787_0_checked : (List.range' 914944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1787_1_checked : (List.range' 915072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1787_2_checked : (List.range' 915200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1787_3_checked : (List.range' 915328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1787_range (index : Nat) (lower : 914944 ≤ index) (upper : index < 915456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 915200 then
    if cut : index < 915072 then
      exact segment_sound _ 914944 128 Restriction1787_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 915072 128 Restriction1787_1_checked index (by omega) (by omega)
  else
    if cut : index < 915328 then
      exact segment_sound _ 915200 128 Restriction1787_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 915328 128 Restriction1787_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
