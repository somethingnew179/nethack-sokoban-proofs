import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1590_0_checked : (List.range' 814080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1590_1_checked : (List.range' 814208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1590_2_checked : (List.range' 814336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1590_3_checked : (List.range' 814464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1590_range (index : Nat) (lower : 814080 ≤ index) (upper : index < 814592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 814336 then
    if cut : index < 814208 then
      exact segment_sound _ 814080 128 Restriction1590_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 814208 128 Restriction1590_1_checked index (by omega) (by omega)
  else
    if cut : index < 814464 then
      exact segment_sound _ 814336 128 Restriction1590_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 814464 128 Restriction1590_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
