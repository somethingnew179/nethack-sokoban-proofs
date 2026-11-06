import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1438_0_checked : (List.range' 736256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1438_1_checked : (List.range' 736384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1438_2_checked : (List.range' 736512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1438_3_checked : (List.range' 736640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1438_range (index : Nat) (lower : 736256 ≤ index) (upper : index < 736768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 736512 then
    if cut : index < 736384 then
      exact segment_sound _ 736256 128 Restriction1438_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 736384 128 Restriction1438_1_checked index (by omega) (by omega)
  else
    if cut : index < 736640 then
      exact segment_sound _ 736512 128 Restriction1438_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 736640 128 Restriction1438_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
