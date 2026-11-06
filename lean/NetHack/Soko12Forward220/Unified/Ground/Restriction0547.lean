import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0547_0_checked : (List.range' 280064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0547_1_checked : (List.range' 280192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0547_2_checked : (List.range' 280320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0547_3_checked : (List.range' 280448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0547_range (index : Nat) (lower : 280064 ≤ index) (upper : index < 280576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 280320 then
    if cut : index < 280192 then
      exact segment_sound _ 280064 128 Restriction0547_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 280192 128 Restriction0547_1_checked index (by omega) (by omega)
  else
    if cut : index < 280448 then
      exact segment_sound _ 280320 128 Restriction0547_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 280448 128 Restriction0547_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
