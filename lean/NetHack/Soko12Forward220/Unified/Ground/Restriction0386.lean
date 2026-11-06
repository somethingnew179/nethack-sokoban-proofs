import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0386_0_checked : (List.range' 197632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0386_1_checked : (List.range' 197760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0386_2_checked : (List.range' 197888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0386_3_checked : (List.range' 198016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0386_range (index : Nat) (lower : 197632 ≤ index) (upper : index < 198144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 197888 then
    if cut : index < 197760 then
      exact segment_sound _ 197632 128 Restriction0386_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 197760 128 Restriction0386_1_checked index (by omega) (by omega)
  else
    if cut : index < 198016 then
      exact segment_sound _ 197888 128 Restriction0386_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 198016 128 Restriction0386_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
