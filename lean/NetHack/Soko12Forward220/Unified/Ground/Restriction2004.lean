import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2004_0_checked : (List.range' 1026048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2004_1_checked : (List.range' 1026176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2004_2_checked : (List.range' 1026304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2004_3_checked : (List.range' 1026432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2004_range (index : Nat) (lower : 1026048 ≤ index) (upper : index < 1026560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1026304 then
    if cut : index < 1026176 then
      exact segment_sound _ 1026048 128 Restriction2004_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1026176 128 Restriction2004_1_checked index (by omega) (by omega)
  else
    if cut : index < 1026432 then
      exact segment_sound _ 1026304 128 Restriction2004_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1026432 128 Restriction2004_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
