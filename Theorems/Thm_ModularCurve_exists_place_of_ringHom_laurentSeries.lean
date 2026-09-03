import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_place_of_ringHom_laurentSeries

open AlgebraicCurve
theorem ModularCurve.exists_place_of_ringHom_laurentSeries
    {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    (θ : F →+* LaurentSeries K)
    (hθ : ∀ a : k, θ (algebraMap k F a) = HahnSeries.C (algebraMap k K a))
    (hunif : ∃ x : F, (θ x).order = 1) :
    ∃ v : AlgebraicCurve.Place k F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ 0 ≤ (θ f).order) ∧
      (∀ f : F, v.ord f = (θ f).order) ∧
      ∃ ι : v.ResidueField →ₐ[k] K,
        ∀ x : v.toValuationSubring, ι (IsLocalRing.residue v.toValuationSubring x) = (θ (x : F)).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_place_of_ringHom_laurentSeries.solution
