import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Flat R H]

    (E₀ : Type (max u v)) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    (ι₀ : E₀ →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H)
    (hι₀ : Function.Injective ι₀)
    (hE₀ : Algebra.Etale (IsLocalRing.ResidueField R) E₀)
    (huniv₀ : ∀ (E' : Type (max u v)) [CommRing E'] [HopfAlgebra (IsLocalRing.ResidueField R) E']
        [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E'] [Module.Finite (IsLocalRing.ResidueField R) E']
        [Algebra.Etale (IsLocalRing.ResidueField R) E']
        (f : E' →ₐc[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R ⊗[R] H),
        ∃! g : E' →ₐc[IsLocalRing.ResidueField R] E₀, ι₀.comp g = f)
    (hbc₀ : ∀ (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
        (E' : Type (max u v)) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
        [Module.Finite K E'] [Algebra.Etale K E']
        (f : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] (IsLocalRing.ResidueField R ⊗[R] H)),
        ∃! g : E' →ₐc[K] K ⊗[IsLocalRing.ResidueField R] E₀,
          (Bialgebra.TensorProduct.map (BialgHom.id K K) ι₀).comp g = f) :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E) (ι : E →ₐc[R] H),
      Function.Injective ι ∧

      Algebra.Etale R E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra R E'] [Coalgebra.IsCocomm R E']
          [Module.Free R E'] [Module.Finite R E'] [Algebra.Etale R E']
          (f : E' →ₐc[R] H), ∃! g : E' →ₐc[R] E, ι.comp g = f) ∧

      (∀ φ : H →ₐc[R] H, ∃! ψ : E →ₐc[R] E, ι.comp ψ = φ.comp ι) ∧

      Module.Free R (H ⧸ LinearMap.range (ι : E →ₐ[R] H).toLinearMap) ∧

      (∀ (R' : Type u) [CommRing R'] [HenselianLocalRing R'] [Algebra R R'],
          IsLocalHom (algebraMap R R') →
          Algebra.Etale R' (R' ⊗[R] E) ∧
          ∀ (E' : Type v) [CommRing E'] [HopfAlgebra R' E'] [Coalgebra.IsCocomm R' E']
            [Module.Free R' E'] [Module.Finite R' E'] [Algebra.Etale R' E']
            (f : E' →ₐc[R'] R' ⊗[R] H),
              ∃! g : E' →ₐc[R'] R' ⊗[R] E,
                (Bialgebra.TensorProduct.map (BialgHom.id R' R') ι).comp g = f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField.solution
