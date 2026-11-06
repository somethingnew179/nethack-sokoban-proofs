import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1273_0_checked : (List.range' 651776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1273_1_checked : (List.range' 651904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1273_2_checked : (List.range' 652032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1273_3_checked : (List.range' 652160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1273_range (index : Nat) (lower : 651776 ≤ index) (upper : index < 652288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 652032 then
    if cut : index < 651904 then
      exact segment_sound _ 651776 128 Restriction1273_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 651904 128 Restriction1273_1_checked index (by omega) (by omega)
  else
    if cut : index < 652160 then
      exact segment_sound _ 652032 128 Restriction1273_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 652160 128 Restriction1273_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
