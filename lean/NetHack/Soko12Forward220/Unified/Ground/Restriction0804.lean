import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0804_0_checked : (List.range' 411648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0804_1_checked : (List.range' 411776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0804_2_checked : (List.range' 411904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0804_3_checked : (List.range' 412032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0804_range (index : Nat) (lower : 411648 ≤ index) (upper : index < 412160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 411904 then
    if cut : index < 411776 then
      exact segment_sound _ 411648 128 Restriction0804_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 411776 128 Restriction0804_1_checked index (by omega) (by omega)
  else
    if cut : index < 412032 then
      exact segment_sound _ 411904 128 Restriction0804_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 412032 128 Restriction0804_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
