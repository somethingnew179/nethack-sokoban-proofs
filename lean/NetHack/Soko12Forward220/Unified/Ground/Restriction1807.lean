import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1807_0_checked : (List.range' 925184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1807_1_checked : (List.range' 925312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1807_2_checked : (List.range' 925440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1807_3_checked : (List.range' 925568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1807_range (index : Nat) (lower : 925184 ≤ index) (upper : index < 925696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 925440 then
    if cut : index < 925312 then
      exact segment_sound _ 925184 128 Restriction1807_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 925312 128 Restriction1807_1_checked index (by omega) (by omega)
  else
    if cut : index < 925568 then
      exact segment_sound _ 925440 128 Restriction1807_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 925568 128 Restriction1807_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
