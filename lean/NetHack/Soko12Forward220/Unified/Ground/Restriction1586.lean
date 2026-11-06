import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1586_0_checked : (List.range' 812032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1586_1_checked : (List.range' 812160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1586_2_checked : (List.range' 812288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1586_3_checked : (List.range' 812416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1586_range (index : Nat) (lower : 812032 ≤ index) (upper : index < 812544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 812288 then
    if cut : index < 812160 then
      exact segment_sound _ 812032 128 Restriction1586_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 812160 128 Restriction1586_1_checked index (by omega) (by omega)
  else
    if cut : index < 812416 then
      exact segment_sound _ 812288 128 Restriction1586_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 812416 128 Restriction1586_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
