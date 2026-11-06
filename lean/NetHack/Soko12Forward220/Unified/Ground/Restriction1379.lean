import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1379_0_checked : (List.range' 706048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1379_1_checked : (List.range' 706176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1379_2_checked : (List.range' 706304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1379_3_checked : (List.range' 706432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1379_range (index : Nat) (lower : 706048 ≤ index) (upper : index < 706560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 706304 then
    if cut : index < 706176 then
      exact segment_sound _ 706048 128 Restriction1379_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 706176 128 Restriction1379_1_checked index (by omega) (by omega)
  else
    if cut : index < 706432 then
      exact segment_sound _ 706304 128 Restriction1379_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 706432 128 Restriction1379_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
