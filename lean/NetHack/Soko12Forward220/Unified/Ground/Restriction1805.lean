import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1805_0_checked : (List.range' 924160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1805_1_checked : (List.range' 924288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1805_2_checked : (List.range' 924416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1805_3_checked : (List.range' 924544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1805_range (index : Nat) (lower : 924160 ≤ index) (upper : index < 924672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 924416 then
    if cut : index < 924288 then
      exact segment_sound _ 924160 128 Restriction1805_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 924288 128 Restriction1805_1_checked index (by omega) (by omega)
  else
    if cut : index < 924544 then
      exact segment_sound _ 924416 128 Restriction1805_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 924544 128 Restriction1805_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
