import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1111_0_checked : (List.range' 568832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1111_1_checked : (List.range' 568960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1111_2_checked : (List.range' 569088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1111_3_checked : (List.range' 569216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1111_range (index : Nat) (lower : 568832 ≤ index) (upper : index < 569344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 569088 then
    if cut : index < 568960 then
      exact segment_sound _ 568832 128 Restriction1111_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 568960 128 Restriction1111_1_checked index (by omega) (by omega)
  else
    if cut : index < 569216 then
      exact segment_sound _ 569088 128 Restriction1111_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 569216 128 Restriction1111_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
