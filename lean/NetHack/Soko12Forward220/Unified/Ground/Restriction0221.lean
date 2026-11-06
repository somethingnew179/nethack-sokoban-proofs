import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0221_0_checked : (List.range' 113152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0221_1_checked : (List.range' 113280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0221_2_checked : (List.range' 113408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0221_3_checked : (List.range' 113536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0221_range (index : Nat) (lower : 113152 ≤ index) (upper : index < 113664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 113408 then
    if cut : index < 113280 then
      exact segment_sound _ 113152 128 Restriction0221_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 113280 128 Restriction0221_1_checked index (by omega) (by omega)
  else
    if cut : index < 113536 then
      exact segment_sound _ 113408 128 Restriction0221_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 113536 128 Restriction0221_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
