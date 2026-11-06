import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1054_0_checked : (List.range' 539648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1054_1_checked : (List.range' 539776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1054_2_checked : (List.range' 539904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1054_3_checked : (List.range' 540032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1054_range (index : Nat) (lower : 539648 ≤ index) (upper : index < 540160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 539904 then
    if cut : index < 539776 then
      exact segment_sound _ 539648 128 Restriction1054_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 539776 128 Restriction1054_1_checked index (by omega) (by omega)
  else
    if cut : index < 540032 then
      exact segment_sound _ 539904 128 Restriction1054_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 540032 128 Restriction1054_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
