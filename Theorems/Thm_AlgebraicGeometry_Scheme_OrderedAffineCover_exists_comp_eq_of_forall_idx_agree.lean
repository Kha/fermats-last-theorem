import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) [IsSeparated p]
    (p₀ : P₀ ⟶ Spec (CommRingCat.of T)) (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) (μ : P₀ ⟶ A)
    (𝒲 : P.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmμ : ∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ)
    (v : ∀ t : 𝒲.Idx 0, Spec (CommRingCat.of Γ(P, 𝒲.inter t)) ⟶ A)
    (hvf : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      v t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, 𝒲.inter t))))
    (hvm : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter p 𝒲 t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫ v t)
    (hagree : ∀ s : 𝒲.Idx 1, letI := algebraOfHom p (𝒲.inter s)
      letI := algebraOfHom p (𝒲.inter (𝒲.face s 0)); letI := algebraOfHom p (𝒲.inter (𝒲.face s 1))
      Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 1)).toRingHom) ≫ v (𝒲.face s 1) =
        Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 0)).toRingHom) ≫ v (𝒲.face s 0)) :
    ∃ m' : P ⟶ A, m' ≫ f = p ∧ G ≫ m' = μ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree.solution
