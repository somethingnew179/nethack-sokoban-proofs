import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2593_0_checked : (List.range' 1327616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2593_1_checked : (List.range' 1327744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2593_2_checked : (List.range' 1327872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2593_3_checked : (List.range' 1328000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2593_range (index : Nat) (lower : 1327616 ≤ index) (upper : index < 1328128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1327872 then
    if cut : index < 1327744 then
      exact segment_sound _ 1327616 128 Restriction2593_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1327744 128 Restriction2593_1_checked index (by omega) (by omega)
  else
    if cut : index < 1328000 then
      exact segment_sound _ 1327872 128 Restriction2593_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1328000 128 Restriction2593_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
