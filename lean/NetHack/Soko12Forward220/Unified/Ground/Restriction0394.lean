import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0394_0_checked : (List.range' 201728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0394_1_checked : (List.range' 201856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0394_2_checked : (List.range' 201984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0394_3_checked : (List.range' 202112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0394_range (index : Nat) (lower : 201728 ≤ index) (upper : index < 202240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 201984 then
    if cut : index < 201856 then
      exact segment_sound _ 201728 128 Restriction0394_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 201856 128 Restriction0394_1_checked index (by omega) (by omega)
  else
    if cut : index < 202112 then
      exact segment_sound _ 201984 128 Restriction0394_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 202112 128 Restriction0394_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
