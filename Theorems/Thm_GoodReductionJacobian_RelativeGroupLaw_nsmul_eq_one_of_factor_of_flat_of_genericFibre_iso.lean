import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f) (N : ℕ)
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK]
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t gK),
      (L.genericFibre K).nsmul t N (NeronModelInfra.schemeHomOverComp x iK) = (L.genericFibre K).one t)
    {E : Scheme.{u}} (ι : E ⟶ J) [Flat (ι ≫ f)]
    (e : SchemeHomOver (pullback.snd (ι ≫ f) (specGenericFibreInclusion R K)) gK) (hiso : IsIso e.1)
    (hecomp : e.1 ≫ iK.1 =
      pullback.map (ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) ι (𝟙 _) (𝟙 _) (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (hx : ∃ e₀ : T ⟶ E, e₀ ≫ ι = x.1) :
    L.nsmul t N x = L.one t := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_factor_of_flat_of_genericFibre_iso.solution
