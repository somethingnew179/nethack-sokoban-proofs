import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1494_0_checked : (List.range' 764928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1494_1_checked : (List.range' 765056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1494_2_checked : (List.range' 765184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1494_3_checked : (List.range' 765312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1494_range (index : Nat) (lower : 764928 ≤ index) (upper : index < 765440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 765184 then
    if cut : index < 765056 then
      exact segment_sound _ 764928 128 Restriction1494_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 765056 128 Restriction1494_1_checked index (by omega) (by omega)
  else
    if cut : index < 765312 then
      exact segment_sound _ 765184 128 Restriction1494_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 765312 128 Restriction1494_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
