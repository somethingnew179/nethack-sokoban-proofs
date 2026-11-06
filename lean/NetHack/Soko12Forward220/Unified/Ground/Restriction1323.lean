import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1323_0_checked : (List.range' 677376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1323_1_checked : (List.range' 677504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1323_2_checked : (List.range' 677632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1323_3_checked : (List.range' 677760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1323_range (index : Nat) (lower : 677376 ≤ index) (upper : index < 677888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 677632 then
    if cut : index < 677504 then
      exact segment_sound _ 677376 128 Restriction1323_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 677504 128 Restriction1323_1_checked index (by omega) (by omega)
  else
    if cut : index < 677760 then
      exact segment_sound _ 677632 128 Restriction1323_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 677760 128 Restriction1323_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
