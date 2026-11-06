import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0047_0_checked : (List.range' 24064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0047_1_checked : (List.range' 24192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0047_2_checked : (List.range' 24320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0047_3_checked : (List.range' 24448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0047_range (index : Nat) (lower : 24064 ≤ index) (upper : index < 24576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 24320 then
    if cut : index < 24192 then
      exact segment_sound _ 24064 128 Restriction0047_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24192 128 Restriction0047_1_checked index (by omega) (by omega)
  else
    if cut : index < 24448 then
      exact segment_sound _ 24320 128 Restriction0047_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24448 128 Restriction0047_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
