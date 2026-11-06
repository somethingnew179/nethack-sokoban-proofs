import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0113_0_checked : (List.range' 57856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0113_1_checked : (List.range' 57984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0113_2_checked : (List.range' 58112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0113_3_checked : (List.range' 58240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0113_range (index : Nat) (lower : 57856 ≤ index) (upper : index < 58368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 58112 then
    if cut : index < 57984 then
      exact segment_sound _ 57856 128 Restriction0113_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 57984 128 Restriction0113_1_checked index (by omega) (by omega)
  else
    if cut : index < 58240 then
      exact segment_sound _ 58112 128 Restriction0113_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 58240 128 Restriction0113_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
