import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1094_0_checked : (List.range' 560128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1094_1_checked : (List.range' 560256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1094_2_checked : (List.range' 560384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1094_3_checked : (List.range' 560512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1094_range (index : Nat) (lower : 560128 ≤ index) (upper : index < 560640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 560384 then
    if cut : index < 560256 then
      exact segment_sound _ 560128 128 Restriction1094_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 560256 128 Restriction1094_1_checked index (by omega) (by omega)
  else
    if cut : index < 560512 then
      exact segment_sound _ 560384 128 Restriction1094_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 560512 128 Restriction1094_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
