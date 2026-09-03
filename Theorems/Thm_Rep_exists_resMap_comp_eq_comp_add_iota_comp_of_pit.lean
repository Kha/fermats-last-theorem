import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import P2M.Util
import P2M.Sol.S_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_resMap_comp_eq_comp_add_iota_comp_of_pit
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (t : Rep.relationModuleInt B ⟶ T.X₂) :
    ∃ (t' : Rep.relationModuleInt (Rep.res π B) ⟶ T'.X₁) (χ : Rep.free ℤ G' (Rep.res π B) ⟶ T'.X₂),
      Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map t ≫ φ₂ =
        t' ≫ T'.f + Rep.relationModuleInt.ι (Rep.res π B) ≫ χ := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_resMap_comp_eq_comp_add_iota_comp_of_pit.solution
