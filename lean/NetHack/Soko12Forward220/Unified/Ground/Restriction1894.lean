import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1894_0_checked : (List.range' 969728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1894_1_checked : (List.range' 969856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1894_2_checked : (List.range' 969984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1894_3_checked : (List.range' 970112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1894_range (index : Nat) (lower : 969728 ≤ index) (upper : index < 970240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 969984 then
    if cut : index < 969856 then
      exact segment_sound _ 969728 128 Restriction1894_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 969856 128 Restriction1894_1_checked index (by omega) (by omega)
  else
    if cut : index < 970112 then
      exact segment_sound _ 969984 128 Restriction1894_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 970112 128 Restriction1894_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
