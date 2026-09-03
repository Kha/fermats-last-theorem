import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology~nonempty_linearEquiv_of_iso_res_mulEquiv~inf_injective_and_exact_of_isZero_res~isZero_H1_res_units_of_smul_eq"

theorem IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y))
    (i : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)
    (hi : ∀ a : Lˣ, i.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap L M : L →* M) a)) :
    Function.Injective (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom ∧
    ∀ y : groupCohomology (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ) 2,
      (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ))) 2).hom y = 0 →
      ∃ β : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ) 2,
        (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) i 2).hom β = y := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_map_two_units_injective_and_exists_of_map_subtype_eq_zero.solution
