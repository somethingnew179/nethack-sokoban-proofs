import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0890_0_checked : (List.range' 455680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0890_1_checked : (List.range' 455808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0890_2_checked : (List.range' 455936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0890_3_checked : (List.range' 456064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0890_range (index : Nat) (lower : 455680 ≤ index) (upper : index < 456192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 455936 then
    if cut : index < 455808 then
      exact segment_sound _ 455680 128 Restriction0890_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 455808 128 Restriction0890_1_checked index (by omega) (by omega)
  else
    if cut : index < 456064 then
      exact segment_sound _ 455936 128 Restriction0890_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 456064 128 Restriction0890_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
