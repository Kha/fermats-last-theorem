import Mathlib
import P2M.Util
namespace P2MW.S_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField

theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] (w : L) :
    ‖((Algebra.norm K w : K) : PadicAlgCl q)‖ = ‖(w : PadicAlgCl q)‖ ^ Module.finrank K L := by
  classical

  have key : ∀ y : PadicAlgCl q, ‖y‖ = spectralValue (minpoly ℚ_[q] y) := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq]; rfl
  have hemb : ∀ σ : L →ₐ[K] PadicAlgCl q, ‖σ w‖ = ‖(w : PadicAlgCl q)‖ := fun σ => by
    rw [key, key]
    congr 1
    have h1 : minpoly ℚ_[q] (σ w) = minpoly ℚ_[q] w :=
      minpoly.algHom_eq (σ.restrictScalars ℚ_[q]) (σ.restrictScalars ℚ_[q]).injective w
    have h2 : minpoly ℚ_[q] ((w : PadicAlgCl q)) = minpoly ℚ_[q] w :=
      minpoly.algHom_eq ((L.val).restrictScalars ℚ_[q]) ((L.val).restrictScalars ℚ_[q]).injective w
    rw [h1, h2]
  have hprod := Algebra.norm_eq_prod_embeddings K (PadicAlgCl q) w
  change ((Algebra.norm K w : K) : PadicAlgCl q) = _ at hprod
  rw [hprod, norm_prod, Finset.prod_congr rfl (fun σ _ => hemb σ), Finset.prod_const, Finset.card_univ,
    AlgHom.card]
