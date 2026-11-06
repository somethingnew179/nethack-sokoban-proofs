import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0626_0_checked : (List.range' 320512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0626_1_checked : (List.range' 320640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0626_2_checked : (List.range' 320768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0626_3_checked : (List.range' 320896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0626_range (index : Nat) (lower : 320512 ≤ index) (upper : index < 321024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 320768 then
    if cut : index < 320640 then
      exact segment_sound _ 320512 128 Restriction0626_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 320640 128 Restriction0626_1_checked index (by omega) (by omega)
  else
    if cut : index < 320896 then
      exact segment_sound _ 320768 128 Restriction0626_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 320896 128 Restriction0626_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
