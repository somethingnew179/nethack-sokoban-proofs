import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0144_0_checked : (List.range' 73728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0144_1_checked : (List.range' 73856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0144_2_checked : (List.range' 73984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0144_3_checked : (List.range' 74112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0144_range (index : Nat) (lower : 73728 ≤ index) (upper : index < 74240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 73984 then
    if cut : index < 73856 then
      exact segment_sound _ 73728 128 Restriction0144_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 73856 128 Restriction0144_1_checked index (by omega) (by omega)
  else
    if cut : index < 74112 then
      exact segment_sound _ 73984 128 Restriction0144_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 74112 128 Restriction0144_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
