import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct

open TensorProduct

theorem Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom)) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.solution
