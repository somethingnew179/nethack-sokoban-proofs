import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0668_0_checked : (List.range' 342016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0668_1_checked : (List.range' 342144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0668_2_checked : (List.range' 342272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0668_3_checked : (List.range' 342400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0668_range (index : Nat) (lower : 342016 ≤ index) (upper : index < 342528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 342272 then
    if cut : index < 342144 then
      exact segment_sound _ 342016 128 Restriction0668_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342144 128 Restriction0668_1_checked index (by omega) (by omega)
  else
    if cut : index < 342400 then
      exact segment_sound _ 342272 128 Restriction0668_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342400 128 Restriction0668_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
