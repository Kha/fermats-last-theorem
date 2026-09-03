import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_eta_eq_of_isLocalRing
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{0, 0} p O)
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
      ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
          (hL : IsNilpotent (p : L)),
          ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
            η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) :
    ∃ t : Rigidified p Φ B, t.IsAdmissible ι ψ ∧ η B ψ hB t = m := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing.solution
