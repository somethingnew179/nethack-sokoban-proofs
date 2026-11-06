import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1150_0_checked : (List.range' 588800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1150_1_checked : (List.range' 588928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1150_2_checked : (List.range' 589056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1150_3_checked : (List.range' 589184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1150_range (index : Nat) (lower : 588800 ≤ index) (upper : index < 589312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 589056 then
    if cut : index < 588928 then
      exact segment_sound _ 588800 128 Restriction1150_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 588928 128 Restriction1150_1_checked index (by omega) (by omega)
  else
    if cut : index < 589184 then
      exact segment_sound _ 589056 128 Restriction1150_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 589184 128 Restriction1150_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
