import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1730_0_checked : (List.range' 885760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1730_1_checked : (List.range' 885888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1730_2_checked : (List.range' 886016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1730_3_checked : (List.range' 886144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1730_range (index : Nat) (lower : 885760 ≤ index) (upper : index < 886272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 886016 then
    if cut : index < 885888 then
      exact segment_sound _ 885760 128 Restriction1730_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 885888 128 Restriction1730_1_checked index (by omega) (by omega)
  else
    if cut : index < 886144 then
      exact segment_sound _ 886016 128 Restriction1730_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 886144 128 Restriction1730_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
