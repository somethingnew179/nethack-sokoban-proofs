import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1997_0_checked : (List.range' 1022464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1997_1_checked : (List.range' 1022592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1997_2_checked : (List.range' 1022720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1997_3_checked : (List.range' 1022848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1997_range (index : Nat) (lower : 1022464 ≤ index) (upper : index < 1022976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1022720 then
    if cut : index < 1022592 then
      exact segment_sound _ 1022464 128 Restriction1997_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1022592 128 Restriction1997_1_checked index (by omega) (by omega)
  else
    if cut : index < 1022848 then
      exact segment_sound _ 1022720 128 Restriction1997_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1022848 128 Restriction1997_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
