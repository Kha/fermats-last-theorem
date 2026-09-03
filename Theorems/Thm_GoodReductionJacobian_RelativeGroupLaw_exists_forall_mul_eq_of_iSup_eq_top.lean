import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_eq_of_iSup_eq_top
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (U : ι → (Spec (CommRingCat.of R)).Opens) (hU : ⨆ i, U i = ⊤)
    (L : ∀ i, RelativeGroupLaw R ((f ⁻¹ᵁ U i).ι ≫ f))
    (hagree : ∀ (i j : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ (U i ⊓ U j)).ι ≫ f)),
      ((L i).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_left), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U i).ι =
      ((L j).mul t
          ⟨x.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact x.2⟩
          ⟨y.1 ≫ A.homOfLE (f.preimage_mono inf_le_right), by
            rw [Category.assoc, ← Category.assoc (A.homOfLE _), Scheme.homOfLE_ι]; exact y.2⟩).1 ≫ (f ⁻¹ᵁ U j).ι) :
    ∃ G : RelativeGroupLaw R f, ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : SchemeHomOver t ((f ⁻¹ᵁ U i).ι ≫ f)),
      (G.mul t ⟨x.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact x.2⟩
        ⟨y.1 ≫ (f ⁻¹ᵁ U i).ι, by rw [Category.assoc]; exact y.2⟩).1 =
      ((L i).mul t x y).1 ≫ (f ⁻¹ᵁ U i).ι := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_eq_of_iSup_eq_top.solution
