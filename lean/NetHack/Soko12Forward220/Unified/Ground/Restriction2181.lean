import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2181_0_checked : (List.range' 1116672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2181_1_checked : (List.range' 1116800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2181_2_checked : (List.range' 1116928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2181_3_checked : (List.range' 1117056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2181_range (index : Nat) (lower : 1116672 ≤ index) (upper : index < 1117184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1116928 then
    if cut : index < 1116800 then
      exact segment_sound _ 1116672 128 Restriction2181_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1116800 128 Restriction2181_1_checked index (by omega) (by omega)
  else
    if cut : index < 1117056 then
      exact segment_sound _ 1116928 128 Restriction2181_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1117056 128 Restriction2181_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
