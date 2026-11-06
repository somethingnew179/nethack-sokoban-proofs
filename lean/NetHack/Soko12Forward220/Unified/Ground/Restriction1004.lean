import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1004_0_checked : (List.range' 514048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1004_1_checked : (List.range' 514176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1004_2_checked : (List.range' 514304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1004_3_checked : (List.range' 514432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1004_range (index : Nat) (lower : 514048 ≤ index) (upper : index < 514560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 514304 then
    if cut : index < 514176 then
      exact segment_sound _ 514048 128 Restriction1004_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 514176 128 Restriction1004_1_checked index (by omega) (by omega)
  else
    if cut : index < 514432 then
      exact segment_sound _ 514304 128 Restriction1004_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 514432 128 Restriction1004_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
