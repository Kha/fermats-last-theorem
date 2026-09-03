import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion

set_option autoImplicit false

universe u v

open WithConv

theorem HopfAlgebra.exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
    {R : Type u} [CommRing R] (n : ℕ)
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type v) [CommRing H'] [HopfAlgebra R H']
    (ι : ∀ (T : Type v) [CommRing T] [Algebra R T], (H →ₐ[R] T) → (H' →ₐ[R] T))
    (hnat : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (g : T →ₐ[R] T') (ψ : H →ₐ[R] T), ι T' (g.comp ψ) = g.comp (ι T ψ))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ₁ ψ₂ : H →ₐ[R] T),
      ι T (toConv ψ₁ * toConv ψ₂).ofConv = (toConv (ι T ψ₁) * toConv (ι T ψ₂)).ofConv)
    (hinj : ∀ (T : Type v) [CommRing T] [Algebra R T], Function.Injective (ι T))
    (htors : ∀ (T : Type v) [CommRing T] [Algebra R T] (x : H' →ₐ[R] T),
      x ∈ Set.range (ι T) ↔ toConv x ^ n = 1) :
    ∃ π : H' →ₐc[R] H, Function.Surjective π ∧
      ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ : H →ₐ[R] T), ι T ψ = ψ.comp (π : H' →ₐ[R] H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion.solution
