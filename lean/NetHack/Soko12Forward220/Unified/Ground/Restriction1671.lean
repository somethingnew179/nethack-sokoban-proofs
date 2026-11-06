import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1671_0_checked : (List.range' 855552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1671_1_checked : (List.range' 855680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1671_2_checked : (List.range' 855808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1671_3_checked : (List.range' 855936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1671_range (index : Nat) (lower : 855552 ≤ index) (upper : index < 856064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 855808 then
    if cut : index < 855680 then
      exact segment_sound _ 855552 128 Restriction1671_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 855680 128 Restriction1671_1_checked index (by omega) (by omega)
  else
    if cut : index < 855936 then
      exact segment_sound _ 855808 128 Restriction1671_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 855936 128 Restriction1671_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
