import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0541_0_checked : (List.range' 276992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0541_1_checked : (List.range' 277120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0541_2_checked : (List.range' 277248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0541_3_checked : (List.range' 277376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0541_range (index : Nat) (lower : 276992 ≤ index) (upper : index < 277504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 277248 then
    if cut : index < 277120 then
      exact segment_sound _ 276992 128 Restriction0541_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 277120 128 Restriction0541_1_checked index (by omega) (by omega)
  else
    if cut : index < 277376 then
      exact segment_sound _ 277248 128 Restriction0541_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 277376 128 Restriction0541_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
