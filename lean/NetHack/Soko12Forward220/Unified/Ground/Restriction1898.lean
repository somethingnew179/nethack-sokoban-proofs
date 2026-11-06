import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1898_0_checked : (List.range' 971776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1898_1_checked : (List.range' 971904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1898_2_checked : (List.range' 972032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1898_3_checked : (List.range' 972160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1898_range (index : Nat) (lower : 971776 ≤ index) (upper : index < 972288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 972032 then
    if cut : index < 971904 then
      exact segment_sound _ 971776 128 Restriction1898_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 971904 128 Restriction1898_1_checked index (by omega) (by omega)
  else
    if cut : index < 972160 then
      exact segment_sound _ 972032 128 Restriction1898_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 972160 128 Restriction1898_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
