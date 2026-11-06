import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1028_0_checked : (List.range' 526336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1028_1_checked : (List.range' 526464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1028_2_checked : (List.range' 526592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1028_3_checked : (List.range' 526720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1028_range (index : Nat) (lower : 526336 ≤ index) (upper : index < 526848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 526592 then
    if cut : index < 526464 then
      exact segment_sound _ 526336 128 Restriction1028_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 526464 128 Restriction1028_1_checked index (by omega) (by omega)
  else
    if cut : index < 526720 then
      exact segment_sound _ 526592 128 Restriction1028_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 526720 128 Restriction1028_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
