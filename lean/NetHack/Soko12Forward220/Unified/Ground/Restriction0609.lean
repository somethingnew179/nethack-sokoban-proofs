import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0609_0_checked : (List.range' 311808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0609_1_checked : (List.range' 311936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0609_2_checked : (List.range' 312064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0609_3_checked : (List.range' 312192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0609_range (index : Nat) (lower : 311808 ≤ index) (upper : index < 312320) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 312064 then
    if cut : index < 311936 then
      exact segment_sound _ 311808 128 Restriction0609_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 311936 128 Restriction0609_1_checked index (by omega) (by omega)
  else
    if cut : index < 312192 then
      exact segment_sound _ 312064 128 Restriction0609_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 312192 128 Restriction0609_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
