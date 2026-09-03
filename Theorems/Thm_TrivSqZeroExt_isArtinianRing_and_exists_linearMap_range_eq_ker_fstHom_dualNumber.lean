import Mathlib
import P2M.Util
import P2M.Sol.S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber

set_option autoImplicit false

open IsLocalRing

theorem TrivSqZeroExt.isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber
    (k : Type) [Field k] :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    IsArtinianRing (DualNumber k) ∧
    Function.Surjective (algebraMap (DualNumber k) k) ∧
    IsNilpotent (RingHom.ker (algebraMap (DualNumber k) k)) ∧
    RingHom.ker (algebraMap (DualNumber k) k) * maximalIdeal (DualNumber k) = ⊥ ∧
    RingHom.ker (algebraMap (DualNumber k) k) ≤ maximalIdeal (DualNumber k) ∧
    (∃ ι : ResidueField (DualNumber k) →ₗ[DualNumber k] DualNumber k,
      Function.Injective ι ∧
      LinearMap.range ι = Submodule.restrictScalars (DualNumber k) (RingHom.ker (algebraMap (DualNumber k) k))) ∧
    Function.Bijective ((residue (DualNumber k)).comp (algebraMap k (DualNumber k))) ∧
    (IsAlgClosed k → IsAlgClosed (ResidueField (DualNumber k))) := by p2m_exact_reverting @_root_.P2MW.S_TrivSqZeroExt_isArtinianRing_and_exists_linearMap_range_eq_ker_fstHom_dualNumber.solution
