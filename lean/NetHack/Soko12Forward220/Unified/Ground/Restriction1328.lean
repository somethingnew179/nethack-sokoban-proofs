import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1328_0_checked : (List.range' 679936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1328_1_checked : (List.range' 680064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1328_2_checked : (List.range' 680192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1328_3_checked : (List.range' 680320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1328_range (index : Nat) (lower : 679936 ≤ index) (upper : index < 680448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 680192 then
    if cut : index < 680064 then
      exact segment_sound _ 679936 128 Restriction1328_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 680064 128 Restriction1328_1_checked index (by omega) (by omega)
  else
    if cut : index < 680320 then
      exact segment_sound _ 680192 128 Restriction1328_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 680320 128 Restriction1328_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
