import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
    (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    (ι : Type) [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i : ι, IsLocalRing (H ⧸ Ideal.span {1 - e i}))
    (i₀ : ι) (h₀ : Coalgebra.counit (R := R) (e i₀) = 1) :
    ∀ i : ι,
      Module.Free R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.FaithfullyFlat R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.finrank R (H ⧸ Ideal.span {1 - e i}) = Module.finrank R (H ⧸ Ideal.span {1 - e i₀}) ∧
      ∃ ρ : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}),
        ρ.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))).comp
            (Bialgebra.comulAlgHom R H) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.TensorProduct.includeLeft :
              (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}))
            ρ (fun _ _ => Commute.all _ _)) ∧
        ∀ (L : Type) [CommRing L] [Algebra R L]
          (t : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] L) (w : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] L),
          ((Algebra.TensorProduct.lift t w (fun _ _ => Commute.all _ _)).comp ρ).comp
              (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
            (WithConv.toConv (t.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) *
              WithConv.toConv (w.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀})))).ofConv := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one.solution
