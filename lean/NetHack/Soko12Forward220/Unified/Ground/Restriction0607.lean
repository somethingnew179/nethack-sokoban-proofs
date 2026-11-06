import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0607_0_checked : (List.range' 310784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0607_1_checked : (List.range' 310912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0607_2_checked : (List.range' 311040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0607_3_checked : (List.range' 311168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0607_range (index : Nat) (lower : 310784 ≤ index) (upper : index < 311296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 311040 then
    if cut : index < 310912 then
      exact segment_sound _ 310784 128 Restriction0607_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 310912 128 Restriction0607_1_checked index (by omega) (by omega)
  else
    if cut : index < 311168 then
      exact segment_sound _ 311040 128 Restriction0607_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 311168 128 Restriction0607_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
