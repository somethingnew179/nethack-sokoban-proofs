import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1387_0_checked : (List.range' 710144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1387_1_checked : (List.range' 710272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1387_2_checked : (List.range' 710400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1387_3_checked : (List.range' 710528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1387_range (index : Nat) (lower : 710144 ≤ index) (upper : index < 710656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 710400 then
    if cut : index < 710272 then
      exact segment_sound _ 710144 128 Restriction1387_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 710272 128 Restriction1387_1_checked index (by omega) (by omega)
  else
    if cut : index < 710528 then
      exact segment_sound _ 710400 128 Restriction1387_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 710528 128 Restriction1387_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
