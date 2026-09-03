import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.nonempty_matching_classSetHeckeData_heckeData
    {a b : ℚ} (M s q' : ℕ) [NeZero M] [Fact s.Prime] [Fact q'.Prime]
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hU : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R)
    (hlaws : ClassSetHeckeLaws M s Λ R n)
    (K : Type) [Field K] [CharP K q'] [DecidableEq K]
    (X : SSLevelDatum q' K M s)
    [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)] [DecidableEq ↥(ssPlaces q' M K)]
    (hX : X.HeckeLaws)
    (eE : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) ≃ ↥(ssPlaces q' (M * s) K))
    (eV : ClassSet (Submodule.finiteIdeleStabilizer R) ≃ ↥(ssPlaces q' M K))
    (ha : ∀ e, X.degeneracyData.a (eE e) = eV ((classSetDegeneracyData R n).a e))
    (hw : ∀ e, X.degeneracyData.w (eE e) = (classSetDegeneracyData R n).w e)
    (hT : ∀ (ℓ : Nat.Primes) (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ),
      (X.edgeHecke ℓ).mulVecLin (x ∘ eE.symm) = ((classSetEdgeHecke M s Λ R n ℓ).mulVecLin x) ∘ eE.symm)
    (hAL : ∀ e, eE (classSetShift _ n e) = X.atkinLehnerPerm (eE e)) :
    ∃ 𝓜 : Matching (classSetHeckeData M s Λ R n) X.heckeData,
      𝓜.eE = eE ∧ 𝓜.eV = eV ∧ 𝓜.bad = ∅ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_nonempty_matching_classSetHeckeData_heckeData.solution
