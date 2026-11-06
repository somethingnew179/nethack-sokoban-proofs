import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2382_0_checked : (List.range' 1219584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2382_1_checked : (List.range' 1219712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2382_2_checked : (List.range' 1219840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2382_3_checked : (List.range' 1219968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2382_range (index : Nat) (lower : 1219584 ≤ index) (upper : index < 1220096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1219840 then
    if cut : index < 1219712 then
      exact segment_sound _ 1219584 128 Restriction2382_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1219712 128 Restriction2382_1_checked index (by omega) (by omega)
  else
    if cut : index < 1219968 then
      exact segment_sound _ 1219840 128 Restriction2382_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1219968 128 Restriction2382_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
