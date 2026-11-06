import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2452_0_checked : (List.range' 1255424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2452_1_checked : (List.range' 1255552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2452_2_checked : (List.range' 1255680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2452_3_checked : (List.range' 1255808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2452_range (index : Nat) (lower : 1255424 ≤ index) (upper : index < 1255936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1255680 then
    if cut : index < 1255552 then
      exact segment_sound _ 1255424 128 Restriction2452_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1255552 128 Restriction2452_1_checked index (by omega) (by omega)
  else
    if cut : index < 1255808 then
      exact segment_sound _ 1255680 128 Restriction2452_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1255808 128 Restriction2452_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
