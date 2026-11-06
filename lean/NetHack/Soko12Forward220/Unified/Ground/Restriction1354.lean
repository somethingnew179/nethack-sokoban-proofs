import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1354_0_checked : (List.range' 693248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1354_1_checked : (List.range' 693376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1354_2_checked : (List.range' 693504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1354_3_checked : (List.range' 693632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1354_range (index : Nat) (lower : 693248 ≤ index) (upper : index < 693760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 693504 then
    if cut : index < 693376 then
      exact segment_sound _ 693248 128 Restriction1354_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 693376 128 Restriction1354_1_checked index (by omega) (by omega)
  else
    if cut : index < 693632 then
      exact segment_sound _ 693504 128 Restriction1354_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 693632 128 Restriction1354_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
