import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1000_0_checked : (List.range' 512000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1000_1_checked : (List.range' 512128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1000_2_checked : (List.range' 512256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1000_3_checked : (List.range' 512384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1000_range (index : Nat) (lower : 512000 ≤ index) (upper : index < 512512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 512256 then
    if cut : index < 512128 then
      exact segment_sound _ 512000 128 Restriction1000_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 512128 128 Restriction1000_1_checked index (by omega) (by omega)
  else
    if cut : index < 512384 then
      exact segment_sound _ 512256 128 Restriction1000_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 512384 128 Restriction1000_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
