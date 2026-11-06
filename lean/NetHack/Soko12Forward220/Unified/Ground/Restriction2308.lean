import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2308_0_checked : (List.range' 1181696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2308_1_checked : (List.range' 1181824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2308_2_checked : (List.range' 1181952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2308_3_checked : (List.range' 1182080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2308_range (index : Nat) (lower : 1181696 ≤ index) (upper : index < 1182208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1181952 then
    if cut : index < 1181824 then
      exact segment_sound _ 1181696 128 Restriction2308_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1181824 128 Restriction2308_1_checked index (by omega) (by omega)
  else
    if cut : index < 1182080 then
      exact segment_sound _ 1181952 128 Restriction2308_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1182080 128 Restriction2308_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
