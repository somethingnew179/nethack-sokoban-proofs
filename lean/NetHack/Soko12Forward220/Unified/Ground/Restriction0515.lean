import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0515_0_checked : (List.range' 263680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0515_1_checked : (List.range' 263808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0515_2_checked : (List.range' 263936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0515_3_checked : (List.range' 264064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0515_range (index : Nat) (lower : 263680 ≤ index) (upper : index < 264192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 263936 then
    if cut : index < 263808 then
      exact segment_sound _ 263680 128 Restriction0515_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 263808 128 Restriction0515_1_checked index (by omega) (by omega)
  else
    if cut : index < 264064 then
      exact segment_sound _ 263936 128 Restriction0515_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 264064 128 Restriction0515_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
