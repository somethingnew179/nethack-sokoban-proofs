import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0172_0_checked : (List.range' 88064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0172_1_checked : (List.range' 88192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0172_2_checked : (List.range' 88320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0172_3_checked : (List.range' 88448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0172_range (index : Nat) (lower : 88064 ≤ index) (upper : index < 88576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 88320 then
    if cut : index < 88192 then
      exact segment_sound _ 88064 128 Restriction0172_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 88192 128 Restriction0172_1_checked index (by omega) (by omega)
  else
    if cut : index < 88448 then
      exact segment_sound _ 88320 128 Restriction0172_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 88448 128 Restriction0172_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
