import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2458_0_checked : (List.range' 1258496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2458_1_checked : (List.range' 1258624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2458_2_checked : (List.range' 1258752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2458_3_checked : (List.range' 1258880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2458_range (index : Nat) (lower : 1258496 ≤ index) (upper : index < 1259008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1258752 then
    if cut : index < 1258624 then
      exact segment_sound _ 1258496 128 Restriction2458_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1258624 128 Restriction2458_1_checked index (by omega) (by omega)
  else
    if cut : index < 1258880 then
      exact segment_sound _ 1258752 128 Restriction2458_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1258880 128 Restriction2458_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
