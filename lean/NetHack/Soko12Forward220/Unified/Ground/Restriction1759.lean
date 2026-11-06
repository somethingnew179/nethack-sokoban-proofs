import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1759_0_checked : (List.range' 900608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1759_1_checked : (List.range' 900736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1759_2_checked : (List.range' 900864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1759_3_checked : (List.range' 900992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1759_range (index : Nat) (lower : 900608 ≤ index) (upper : index < 901120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 900864 then
    if cut : index < 900736 then
      exact segment_sound _ 900608 128 Restriction1759_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 900736 128 Restriction1759_1_checked index (by omega) (by omega)
  else
    if cut : index < 900992 then
      exact segment_sound _ 900864 128 Restriction1759_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 900992 128 Restriction1759_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
