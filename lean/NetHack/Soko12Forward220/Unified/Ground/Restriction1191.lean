import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1191_0_checked : (List.range' 609792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1191_1_checked : (List.range' 609920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1191_2_checked : (List.range' 610048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1191_3_checked : (List.range' 610176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1191_range (index : Nat) (lower : 609792 ≤ index) (upper : index < 610304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 610048 then
    if cut : index < 609920 then
      exact segment_sound _ 609792 128 Restriction1191_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 609920 128 Restriction1191_1_checked index (by omega) (by omega)
  else
    if cut : index < 610176 then
      exact segment_sound _ 610048 128 Restriction1191_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 610176 128 Restriction1191_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
