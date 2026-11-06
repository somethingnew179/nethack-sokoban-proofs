import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2000_0_checked : (List.range' 1024000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2000_1_checked : (List.range' 1024128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2000_2_checked : (List.range' 1024256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2000_3_checked : (List.range' 1024384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2000_range (index : Nat) (lower : 1024000 ≤ index) (upper : index < 1024512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1024256 then
    if cut : index < 1024128 then
      exact segment_sound _ 1024000 128 Restriction2000_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1024128 128 Restriction2000_1_checked index (by omega) (by omega)
  else
    if cut : index < 1024384 then
      exact segment_sound _ 1024256 128 Restriction2000_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1024384 128 Restriction2000_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
