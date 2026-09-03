import Mathlib
import P2M.Util
import P2M.Sol.S_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq

set_option autoImplicit false
open CategoryTheory

theorem IsGalois.exists_units_quotientToInvariants_iso_res_apply_eq
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) :
    ∃ e : (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ).quotientToInvariants S ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ),
      ∀ a : Lˣ, (e.inv.hom (Additive.ofMul a)).1 = Additive.ofMul (Units.map (algebraMap L M : L →* M) a) := by p2m_exact_reverting @_root_.P2MW.S_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq.solution
