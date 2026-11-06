import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1410_0_checked : (List.range' 721920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1410_1_checked : (List.range' 722048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1410_2_checked : (List.range' 722176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1410_3_checked : (List.range' 722304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1410_range (index : Nat) (lower : 721920 ≤ index) (upper : index < 722432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 722176 then
    if cut : index < 722048 then
      exact segment_sound _ 721920 128 Restriction1410_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 722048 128 Restriction1410_1_checked index (by omega) (by omega)
  else
    if cut : index < 722304 then
      exact segment_sound _ 722176 128 Restriction1410_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 722304 128 Restriction1410_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
