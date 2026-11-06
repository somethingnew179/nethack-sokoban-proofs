import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2357_0_checked : (List.range' 1206784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2357_1_checked : (List.range' 1206912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2357_2_checked : (List.range' 1207040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2357_3_checked : (List.range' 1207168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2357_range (index : Nat) (lower : 1206784 ≤ index) (upper : index < 1207296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1207040 then
    if cut : index < 1206912 then
      exact segment_sound _ 1206784 128 Restriction2357_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1206912 128 Restriction2357_1_checked index (by omega) (by omega)
  else
    if cut : index < 1207168 then
      exact segment_sound _ 1207040 128 Restriction2357_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1207168 128 Restriction2357_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
