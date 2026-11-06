import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0299_0_checked : (List.range' 153088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0299_1_checked : (List.range' 153216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0299_2_checked : (List.range' 153344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0299_3_checked : (List.range' 153472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0299_range (index : Nat) (lower : 153088 ≤ index) (upper : index < 153600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 153344 then
    if cut : index < 153216 then
      exact segment_sound _ 153088 128 Restriction0299_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153216 128 Restriction0299_1_checked index (by omega) (by omega)
  else
    if cut : index < 153472 then
      exact segment_sound _ 153344 128 Restriction0299_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153472 128 Restriction0299_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
