import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1648_0_checked : (List.range' 843776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1648_1_checked : (List.range' 843904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1648_2_checked : (List.range' 844032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1648_3_checked : (List.range' 844160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1648_range (index : Nat) (lower : 843776 ≤ index) (upper : index < 844288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 844032 then
    if cut : index < 843904 then
      exact segment_sound _ 843776 128 Restriction1648_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 843904 128 Restriction1648_1_checked index (by omega) (by omega)
  else
    if cut : index < 844160 then
      exact segment_sound _ 844032 128 Restriction1648_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 844160 128 Restriction1648_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
