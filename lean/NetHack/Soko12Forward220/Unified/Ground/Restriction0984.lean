import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0984_0_checked : (List.range' 503808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0984_1_checked : (List.range' 503936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0984_2_checked : (List.range' 504064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0984_3_checked : (List.range' 504192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0984_range (index : Nat) (lower : 503808 ≤ index) (upper : index < 504320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 504064 then
    if cut : index < 503936 then
      exact segment_sound _ 503808 128 Restriction0984_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 503936 128 Restriction0984_1_checked index (by omega) (by omega)
  else
    if cut : index < 504192 then
      exact segment_sound _ 504064 128 Restriction0984_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 504192 128 Restriction0984_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
