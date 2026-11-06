import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0152_0_checked : (List.range' 77824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0152_1_checked : (List.range' 77952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0152_2_checked : (List.range' 78080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0152_3_checked : (List.range' 78208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0152_range (index : Nat) (lower : 77824 ≤ index) (upper : index < 78336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 78080 then
    if cut : index < 77952 then
      exact segment_sound _ 77824 128 Restriction0152_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 77952 128 Restriction0152_1_checked index (by omega) (by omega)
  else
    if cut : index < 78208 then
      exact segment_sound _ 78080 128 Restriction0152_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 78208 128 Restriction0152_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
