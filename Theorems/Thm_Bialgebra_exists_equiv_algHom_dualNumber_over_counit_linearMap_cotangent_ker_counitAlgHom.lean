import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom

set_option autoImplicit false

theorem Bialgebra.exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom
    (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Bialgebra k B] :
    ∃ γ : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b} ≃
        ((RingHom.ker (Bialgebra.counitAlgHom k B)).Cotangent →ₗ[k] k),
      (∀ (D : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b})
          (x : ↥(RingHom.ker (Bialgebra.counitAlgHom k B))),
          γ D ((RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent x) =
            TrivSqZeroExt.snd (D.1 (x : B))) ∧
      (∀ (q : B →ₐ[k] B)
          (hq : RingHom.ker (Bialgebra.counitAlgHom k B) ≤
            (RingHom.ker (Bialgebra.counitAlgHom k B)).comap q)
          (D D' : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b}),
          (∀ b : B, D'.1 b = D.1 (q b)) →
          γ D' = γ D ∘ₗ
            (RingHom.ker (Bialgebra.counitAlgHom k B)).mapCotangent
              (RingHom.ker (Bialgebra.counitAlgHom k B)) q hq) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom.solution
