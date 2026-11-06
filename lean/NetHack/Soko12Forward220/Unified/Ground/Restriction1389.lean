import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1389_0_checked : (List.range' 711168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1389_1_checked : (List.range' 711296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1389_2_checked : (List.range' 711424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1389_3_checked : (List.range' 711552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1389_range (index : Nat) (lower : 711168 ≤ index) (upper : index < 711680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 711424 then
    if cut : index < 711296 then
      exact segment_sound _ 711168 128 Restriction1389_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 711296 128 Restriction1389_1_checked index (by omega) (by omega)
  else
    if cut : index < 711552 then
      exact segment_sound _ 711424 128 Restriction1389_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 711552 128 Restriction1389_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
