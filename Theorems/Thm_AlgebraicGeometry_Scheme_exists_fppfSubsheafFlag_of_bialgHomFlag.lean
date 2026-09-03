import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

theorem AlgebraicGeometry.Scheme.exists_fppfSubsheafFlag_of_bialgHomFlag
    (S : Scheme.{0}) (𝒥 : Sheaf (smallFppfTopology S) Ab.{1})
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (sectionsEquiv : ∀ U : S.Fppf,
      𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (sectionsNat : ∀ {U V : S.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sectionsEquiv U (𝒥.1.map f.op s))) h
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (sectionsEquiv V s)) h))
    (n : ℕ) (B : Fin (n + 1) → Type) [∀ i, CommRing (B i)] [∀ i, HopfAlgebra ℤ (B i)]
    (π : ∀ i, H →ₐc[ℤ] B i) (hπ : ∀ i, Function.Surjective (π i))
    (φ : ∀ i : Fin n, B i.succ →ₐc[ℤ] B i.castSucc)
    (hφ : ∀ i : Fin n, (φ i).comp (π i.succ) = π i.castSucc)
    (hlast : Function.Bijective (π (Fin.last n))) :
    ∃ (F : Fin (n + 1) → Sheaf (smallFppfTopology S) Ab.{1})
      (ι : ∀ i, F i ⟶ 𝒥) (incl : ∀ i : Fin n, F i.castSucc ⟶ F i.succ)
      (FE : ∀ (i : Fin (n + 1)) (U : S.Fppf),
        (F i).1.obj (op U) ≃+ Additive (WithConv (B i →ₐ[ℤ] Γ(U.left, ⊤)))),
      (∀ i, Mono (ι i)) ∧ (∀ i : Fin n, incl i ≫ ι i.succ = ι i.castSucc) ∧
      IsIso (ι (Fin.last n)) ∧
      ∀ (i : Fin (n + 1)) (U : S.Fppf) (s : (F i).1.obj (op U)) (h : H),
        WithConv.ofConv (Additive.toMul (sectionsEquiv U ((ι i).1.app (op U) s))) h
          = WithConv.ofConv (Additive.toMul (FE i U s)) (π i h) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_fppfSubsheafFlag_of_bialgHomFlag.solution
