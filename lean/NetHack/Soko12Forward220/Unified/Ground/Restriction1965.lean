import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1965_0_checked : (List.range' 1006080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1965_1_checked : (List.range' 1006208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1965_2_checked : (List.range' 1006336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1965_3_checked : (List.range' 1006464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1965_range (index : Nat) (lower : 1006080 ≤ index) (upper : index < 1006592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1006336 then
    if cut : index < 1006208 then
      exact segment_sound _ 1006080 128 Restriction1965_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1006208 128 Restriction1965_1_checked index (by omega) (by omega)
  else
    if cut : index < 1006464 then
      exact segment_sound _ 1006336 128 Restriction1965_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1006464 128 Restriction1965_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
