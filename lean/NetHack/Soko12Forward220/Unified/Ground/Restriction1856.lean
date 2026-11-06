import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1856_0_checked : (List.range' 950272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1856_1_checked : (List.range' 950400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1856_2_checked : (List.range' 950528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1856_3_checked : (List.range' 950656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1856_range (index : Nat) (lower : 950272 ≤ index) (upper : index < 950784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 950528 then
    if cut : index < 950400 then
      exact segment_sound _ 950272 128 Restriction1856_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 950400 128 Restriction1856_1_checked index (by omega) (by omega)
  else
    if cut : index < 950656 then
      exact segment_sound _ 950528 128 Restriction1856_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 950656 128 Restriction1856_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
