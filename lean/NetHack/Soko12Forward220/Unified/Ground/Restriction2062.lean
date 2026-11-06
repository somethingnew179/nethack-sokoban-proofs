import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2062_0_checked : (List.range' 1055744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2062_1_checked : (List.range' 1055872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2062_2_checked : (List.range' 1056000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2062_3_checked : (List.range' 1056128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2062_range (index : Nat) (lower : 1055744 ≤ index) (upper : index < 1056256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1056000 then
    if cut : index < 1055872 then
      exact segment_sound _ 1055744 128 Restriction2062_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1055872 128 Restriction2062_1_checked index (by omega) (by omega)
  else
    if cut : index < 1056128 then
      exact segment_sound _ 1056000 128 Restriction2062_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1056128 128 Restriction2062_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
