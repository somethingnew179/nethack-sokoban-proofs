import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1813_0_checked : (List.range' 928256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1813_1_checked : (List.range' 928384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1813_2_checked : (List.range' 928512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1813_3_checked : (List.range' 928640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1813_range (index : Nat) (lower : 928256 ≤ index) (upper : index < 928768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 928512 then
    if cut : index < 928384 then
      exact segment_sound _ 928256 128 Restriction1813_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 928384 128 Restriction1813_1_checked index (by omega) (by omega)
  else
    if cut : index < 928640 then
      exact segment_sound _ 928512 128 Restriction1813_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 928640 128 Restriction1813_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
