import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1793_0_checked : (List.range' 918016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1793_1_checked : (List.range' 918144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1793_2_checked : (List.range' 918272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1793_3_checked : (List.range' 918400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1793_range (index : Nat) (lower : 918016 ≤ index) (upper : index < 918528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 918272 then
    if cut : index < 918144 then
      exact segment_sound _ 918016 128 Restriction1793_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 918144 128 Restriction1793_1_checked index (by omega) (by omega)
  else
    if cut : index < 918400 then
      exact segment_sound _ 918272 128 Restriction1793_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 918400 128 Restriction1793_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
