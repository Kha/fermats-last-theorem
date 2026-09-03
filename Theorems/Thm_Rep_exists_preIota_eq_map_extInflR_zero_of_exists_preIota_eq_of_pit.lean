import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage
import Definitions.Def_GroupCohomology_RelationHomDefect
import P2M.Util
import P2M.Sol.S_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit
    {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (π : G' →* G) (B : Rep ℤ G) (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0)
    {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) {T' : ShortComplex (Rep ℤ G')} (hT' : T'.ShortExact) [Finite T.X₃] [Finite T'.X₃]
    (φ₁ : Rep.res π T.X₁ ⟶ T'.X₁) (φ₂ : Rep.res π T.X₂ ⟶ T'.X₂) (φ₃ : Rep.res π T.X₃ ⟶ T'.X₃)
    (w₁ : (Rep.resFunctor π).map T.f ≫ φ₂ = φ₁ ≫ T'.f) (w₂ : (Rep.resFunctor π).map T.g ≫ φ₃ = φ₂ ≫ T'.g)
    (hpit : ∀ c : T.X₃, (∃ k : ℕ, p ^ k • c = 0) → φ₃.hom c = 0)
    (z : groupCohomology ((ihom (Rep.relationModuleInt B)).obj T.X₁) 0)
    (hz : ∃ ψ : groupCohomology ((ihom (Rep.free ℤ G B)).obj T.X₂) 0,
      (groupCohomology.map (MonoidHom.id G) (Rep.preι B T.X₂) 0).hom ψ =
        (groupCohomology.map (MonoidHom.id G) ((ihom (Rep.relationModuleInt B)).map T.f) 0).hom z) :
    ∃ ψ' : groupCohomology ((ihom (Rep.free ℤ G' (Rep.res π B))).obj T'.X₁) 0,
      (groupCohomology.map (MonoidHom.id G') (Rep.preι (Rep.res π B) T'.X₁) 0).hom ψ' =
        (groupCohomology.map π (Rep.extInflR π B T.X₁ T'.X₁ φ₁) 0).hom z := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_preIota_eq_map_extInflR_zero_of_exists_preIota_eq_of_pit.solution
