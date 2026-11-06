import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1500_0_checked : (List.range' 768000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1500_1_checked : (List.range' 768128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1500_2_checked : (List.range' 768256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1500_3_checked : (List.range' 768384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1500_range (index : Nat) (lower : 768000 ≤ index) (upper : index < 768512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 768256 then
    if cut : index < 768128 then
      exact segment_sound _ 768000 128 Restriction1500_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 768128 128 Restriction1500_1_checked index (by omega) (by omega)
  else
    if cut : index < 768384 then
      exact segment_sound _ 768256 128 Restriction1500_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 768384 128 Restriction1500_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
