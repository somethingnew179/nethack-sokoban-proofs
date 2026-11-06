import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1651_0_checked : (List.range' 845312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1651_1_checked : (List.range' 845440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1651_2_checked : (List.range' 845568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1651_3_checked : (List.range' 845696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1651_range (index : Nat) (lower : 845312 ≤ index) (upper : index < 845824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 845568 then
    if cut : index < 845440 then
      exact segment_sound _ 845312 128 Restriction1651_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 845440 128 Restriction1651_1_checked index (by omega) (by omega)
  else
    if cut : index < 845696 then
      exact segment_sound _ 845568 128 Restriction1651_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 845696 128 Restriction1651_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
