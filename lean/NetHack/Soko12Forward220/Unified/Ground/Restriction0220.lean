import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0220_0_checked : (List.range' 112640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0220_1_checked : (List.range' 112768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0220_2_checked : (List.range' 112896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0220_3_checked : (List.range' 113024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0220_range (index : Nat) (lower : 112640 ≤ index) (upper : index < 113152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 112896 then
    if cut : index < 112768 then
      exact segment_sound _ 112640 128 Restriction0220_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 112768 128 Restriction0220_1_checked index (by omega) (by omega)
  else
    if cut : index < 113024 then
      exact segment_sound _ 112896 128 Restriction0220_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 113024 128 Restriction0220_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
