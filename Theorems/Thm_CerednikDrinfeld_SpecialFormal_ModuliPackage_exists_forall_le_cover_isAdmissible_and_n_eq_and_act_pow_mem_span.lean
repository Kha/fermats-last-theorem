import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType
attribute [-simp] GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    :
    ∀ (S : Type) [CommRing S] [IsNoetherianRing S] [Algebra (WittVector p k ⧸ pIdeal p (WittVector p k)) S] (hS : IsNilpotent (p : S))
      (x : M.obj S ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) hS),
      ∃ n₀ m₀ : ℕ, ∀ (n m : ℕ), n₀ ≤ n → m₀ ≤ m →
        ∃ (r : ℕ) (f : Fin r → S), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin r) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra S L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) ∧ t.n = n ∧
                (∀ j : Fin 2, (t.Φbar ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))).act ((p : Zp2 p) ^ (n + m)) j ∈ Ideal.span (Set.range t.ρ)) ∧
                η L ((algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hL t =
                  M.map (ψ' := (algebraMap S L).comp ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) S).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k))))) hS hL (algebraMap S L) rfl x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span.solution
