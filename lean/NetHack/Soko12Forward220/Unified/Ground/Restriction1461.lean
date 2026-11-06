import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1461_0_checked : (List.range' 748032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1461_1_checked : (List.range' 748160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1461_2_checked : (List.range' 748288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1461_3_checked : (List.range' 748416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1461_range (index : Nat) (lower : 748032 ≤ index) (upper : index < 748544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 748288 then
    if cut : index < 748160 then
      exact segment_sound _ 748032 128 Restriction1461_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 748160 128 Restriction1461_1_checked index (by omega) (by omega)
  else
    if cut : index < 748416 then
      exact segment_sound _ 748288 128 Restriction1461_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 748416 128 Restriction1461_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
