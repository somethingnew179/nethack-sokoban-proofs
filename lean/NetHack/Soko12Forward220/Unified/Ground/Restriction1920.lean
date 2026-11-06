import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1920_0_checked : (List.range' 983040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1920_1_checked : (List.range' 983168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1920_2_checked : (List.range' 983296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1920_3_checked : (List.range' 983424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1920_range (index : Nat) (lower : 983040 ≤ index) (upper : index < 983552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 983296 then
    if cut : index < 983168 then
      exact segment_sound _ 983040 128 Restriction1920_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 983168 128 Restriction1920_1_checked index (by omega) (by omega)
  else
    if cut : index < 983424 then
      exact segment_sound _ 983296 128 Restriction1920_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 983424 128 Restriction1920_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
