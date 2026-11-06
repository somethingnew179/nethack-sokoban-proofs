import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0174_0_checked : (List.range' 89088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0174_1_checked : (List.range' 89216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0174_2_checked : (List.range' 89344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0174_3_checked : (List.range' 89472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0174_range (index : Nat) (lower : 89088 ≤ index) (upper : index < 89600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 89344 then
    if cut : index < 89216 then
      exact segment_sound _ 89088 128 Restriction0174_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89216 128 Restriction0174_1_checked index (by omega) (by omega)
  else
    if cut : index < 89472 then
      exact segment_sound _ 89344 128 Restriction0174_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89472 128 Restriction0174_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
