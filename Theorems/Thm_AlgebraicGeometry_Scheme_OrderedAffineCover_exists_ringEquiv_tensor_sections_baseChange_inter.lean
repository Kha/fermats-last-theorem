import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (A : Type u) [CommRing A] [Algebra R A] {i : ℕ} (s : 𝒰.Idx i) :
    letI := algebraOfHom π (𝒰.inter s)
    letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter s)
    ∃ σ : (A ⊗[R] Γ(X, 𝒰.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s),
      (∀ x : Γ(X, 𝒰.inter s),
        σ ((1 : A) ⊗ₜ[R] x) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter s)).hom x)) ∧
      (∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, 𝒰.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter.solution
