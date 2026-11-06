import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1085_0_checked : (List.range' 555520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1085_1_checked : (List.range' 555648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1085_2_checked : (List.range' 555776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1085_3_checked : (List.range' 555904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1085_range (index : Nat) (lower : 555520 ≤ index) (upper : index < 556032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 555776 then
    if cut : index < 555648 then
      exact segment_sound _ 555520 128 Restriction1085_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 555648 128 Restriction1085_1_checked index (by omega) (by omega)
  else
    if cut : index < 555904 then
      exact segment_sound _ 555776 128 Restriction1085_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 555904 128 Restriction1085_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
