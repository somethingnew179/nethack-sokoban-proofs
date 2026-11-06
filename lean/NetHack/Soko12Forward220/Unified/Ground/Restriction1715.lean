import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1715_0_checked : (List.range' 878080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1715_1_checked : (List.range' 878208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1715_2_checked : (List.range' 878336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1715_3_checked : (List.range' 878464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1715_range (index : Nat) (lower : 878080 ≤ index) (upper : index < 878592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 878336 then
    if cut : index < 878208 then
      exact segment_sound _ 878080 128 Restriction1715_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 878208 128 Restriction1715_1_checked index (by omega) (by omega)
  else
    if cut : index < 878464 then
      exact segment_sound _ 878336 128 Restriction1715_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 878464 128 Restriction1715_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
