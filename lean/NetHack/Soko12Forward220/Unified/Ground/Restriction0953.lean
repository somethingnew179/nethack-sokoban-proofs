import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0953_0_checked : (List.range' 487936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0953_1_checked : (List.range' 488064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0953_2_checked : (List.range' 488192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0953_3_checked : (List.range' 488320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0953_range (index : Nat) (lower : 487936 ≤ index) (upper : index < 488448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 488192 then
    if cut : index < 488064 then
      exact segment_sound _ 487936 128 Restriction0953_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 488064 128 Restriction0953_1_checked index (by omega) (by omega)
  else
    if cut : index < 488320 then
      exact segment_sound _ 488192 128 Restriction0953_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 488320 128 Restriction0953_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
