import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1202_0_checked : (List.range' 615424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1202_1_checked : (List.range' 615552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1202_2_checked : (List.range' 615680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1202_3_checked : (List.range' 615808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1202_range (index : Nat) (lower : 615424 ≤ index) (upper : index < 615936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 615680 then
    if cut : index < 615552 then
      exact segment_sound _ 615424 128 Restriction1202_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 615552 128 Restriction1202_1_checked index (by omega) (by omega)
  else
    if cut : index < 615808 then
      exact segment_sound _ 615680 128 Restriction1202_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 615808 128 Restriction1202_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
