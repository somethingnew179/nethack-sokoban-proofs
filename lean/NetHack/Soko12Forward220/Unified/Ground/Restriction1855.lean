import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1855_0_checked : (List.range' 949760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1855_1_checked : (List.range' 949888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1855_2_checked : (List.range' 950016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1855_3_checked : (List.range' 950144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1855_range (index : Nat) (lower : 949760 ≤ index) (upper : index < 950272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 950016 then
    if cut : index < 949888 then
      exact segment_sound _ 949760 128 Restriction1855_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 949888 128 Restriction1855_1_checked index (by omega) (by omega)
  else
    if cut : index < 950144 then
      exact segment_sound _ 950016 128 Restriction1855_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 950144 128 Restriction1855_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
