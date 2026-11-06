import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2338_0_checked : (List.range' 1197056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2338_1_checked : (List.range' 1197184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2338_2_checked : (List.range' 1197312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2338_3_checked : (List.range' 1197440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2338_range (index : Nat) (lower : 1197056 ≤ index) (upper : index < 1197568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1197312 then
    if cut : index < 1197184 then
      exact segment_sound _ 1197056 128 Restriction2338_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1197184 128 Restriction2338_1_checked index (by omega) (by omega)
  else
    if cut : index < 1197440 then
      exact segment_sound _ 1197312 128 Restriction2338_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1197440 128 Restriction2338_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
