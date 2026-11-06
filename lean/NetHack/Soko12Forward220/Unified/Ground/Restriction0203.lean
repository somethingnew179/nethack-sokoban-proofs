import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0203_0_checked : (List.range' 103936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0203_1_checked : (List.range' 104064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0203_2_checked : (List.range' 104192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0203_3_checked : (List.range' 104320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0203_range (index : Nat) (lower : 103936 ≤ index) (upper : index < 104448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 104192 then
    if cut : index < 104064 then
      exact segment_sound _ 103936 128 Restriction0203_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 104064 128 Restriction0203_1_checked index (by omega) (by omega)
  else
    if cut : index < 104320 then
      exact segment_sound _ 104192 128 Restriction0203_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 104320 128 Restriction0203_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
