import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1859_0_checked : (List.range' 951808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1859_1_checked : (List.range' 951936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1859_2_checked : (List.range' 952064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1859_3_checked : (List.range' 952192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1859_range (index : Nat) (lower : 951808 ≤ index) (upper : index < 952320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 952064 then
    if cut : index < 951936 then
      exact segment_sound _ 951808 128 Restriction1859_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 951936 128 Restriction1859_1_checked index (by omega) (by omega)
  else
    if cut : index < 952192 then
      exact segment_sound _ 952064 128 Restriction1859_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 952192 128 Restriction1859_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
