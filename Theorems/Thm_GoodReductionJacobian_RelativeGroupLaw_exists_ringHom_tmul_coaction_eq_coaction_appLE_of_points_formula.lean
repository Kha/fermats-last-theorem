import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)

    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A)
    (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (N : A ⟶ A) (hN : N ≫ f = f)
    (hsh : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N = act ≫ N) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen (N ⁻¹ᵁ (U : A.Opens)))

    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_snd : ∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
      ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(A, V)) ⊗ₜ[K] h)
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))

    (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))

    (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hφ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ φ =
        (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ]; exact Q.2⟩).1)
    (hφN : φ ≫ N = N ≫ φ) (φH : H →ₐ[K] H)
    (hφH : ∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
      ((e T (.toConv (q.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T q).val.1 ≫ φ)
    (U W : A.affineOpens) (hWU : N ⁻¹ᵁ (W : A.Opens) ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
    ∃ Ξ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →+* Γ(A, N ⁻¹ᵁ (W : A.Opens)) ⊗[K] H,
      (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
          Ξ (s ⊗ₜ[K] (1 : H)) = (φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hWU).hom s ⊗ₜ[K] (1 : H)) ∧
      (∀ x : H, Ξ ((1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] x) = (1 : Γ(A, N ⁻¹ᵁ (W : A.Opens))) ⊗ₜ[K] φH x) ∧
      (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
          Ξ (ρ U s) = ρ W ((φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hWU).hom s)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_ringHom_tmul_coaction_eq_coaction_appLE_of_points_formula.solution
