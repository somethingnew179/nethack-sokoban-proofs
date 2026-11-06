import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1230_0_checked : (List.range' 629760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1230_1_checked : (List.range' 629888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1230_2_checked : (List.range' 630016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1230_3_checked : (List.range' 630144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1230_range (index : Nat) (lower : 629760 ≤ index) (upper : index < 630272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 630016 then
    if cut : index < 629888 then
      exact segment_sound _ 629760 128 Restriction1230_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 629888 128 Restriction1230_1_checked index (by omega) (by omega)
  else
    if cut : index < 630144 then
      exact segment_sound _ 630016 128 Restriction1230_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 630144 128 Restriction1230_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
