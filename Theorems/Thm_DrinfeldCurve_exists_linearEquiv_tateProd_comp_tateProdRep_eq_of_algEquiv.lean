import Definitions.Def_DrinfeldCurve_TateRep
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv

set_option autoImplicit false

open scoped TensorProduct

theorem DrinfeldCurve.exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (k' : Type) [Field k'] [Algebra (GaloisField q 2) k'] [IsDomain (DrinfeldCurve.CoordRing q k')]
    (e : k ≃ₐ[GaloisField q 2] k')
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra ℚ_[ℓ] E] (S : Type) :
    ∃ Θ : DrinfeldCurve.tateProd q k ℓ E S ≃ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S,
      ∀ h : DrinfeldCurve.hSubgroup q,
        (Θ : DrinfeldCurve.tateProd q k ℓ E S →ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S) ∘ₗ
            DrinfeldCurve.tateProdRep q k ℓ E S h =
          DrinfeldCurve.tateProdRep q k' ℓ E S h ∘ₗ
            (Θ : DrinfeldCurve.tateProd q k ℓ E S →ₗ[E] DrinfeldCurve.tateProd q k' ℓ E S) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_linearEquiv_tateProd_comp_tateProdRep_eq_of_algEquiv.solution
