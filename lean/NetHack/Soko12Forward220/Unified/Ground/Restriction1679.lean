import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1679_0_checked : (List.range' 859648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1679_1_checked : (List.range' 859776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1679_2_checked : (List.range' 859904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1679_3_checked : (List.range' 860032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1679_range (index : Nat) (lower : 859648 ≤ index) (upper : index < 860160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 859904 then
    if cut : index < 859776 then
      exact segment_sound _ 859648 128 Restriction1679_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 859776 128 Restriction1679_1_checked index (by omega) (by omega)
  else
    if cut : index < 860032 then
      exact segment_sound _ 859904 128 Restriction1679_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 860032 128 Restriction1679_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
