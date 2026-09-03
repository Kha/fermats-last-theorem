import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] [NeZero d] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] [Algebra S R]
    (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S R))) u.f)
    (hx0 : x 0 = u.L.one _) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul _ (x h) (x h'))
    (hxinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) (h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))),
      Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h')
    (hxK : ∀ (R'' : Type) [CommRing R''] [Algebra R R'']
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap R R'').comp (algebraMap S R)))) u.f),
      Polarisation.MemKernel u.f u.L u.pol _ y ↔
        ∃ (m : ℕ) (r : Fin m → R''), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))),
          Spec.map (CommRingCat.ofHom (algebraMap R'' (Localization.Away (r j)))) ≫ y.1 =
            Spec.map (CommRingCat.ofHom ((algebraMap R'' (Localization.Away (r j))).comp (algebraMap R R''))) ≫ (x h).1)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R)))) (hθ₀ : ∀ k, (θ₀ k).pt = x k)
    (e : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → Rˣ)
    (he : ∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))).obj u.pol, ⊤)),
      (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) (e k k' : R) • (θ₀ k').act ((θ₀ k).act s))
    (ε : ((((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) → R) (hε : CompleteOrthogonalIdempotents ε)
    (hεe : ∀ (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (hB : ε B ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (φ : R →+* K), φ (ε B) = 1 ∧
      ∃ (xK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f)
        (θK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R))))),
        (∀ h, (xK h).1 = Spec.map (CommRingCat.ofHom φ) ≫ (x h).1) ∧
        xK 0 = u.L.one _ ∧ (∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), xK (h + h') = u.L.mul _ (xK h) (xK h')) ∧
        Function.Injective xK ∧
        (∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f, Polarisation.MemKernel u.f u.L u.pol _ y → ∃ h, y = xK h) ∧
        (∀ h, (θK h).pt = xK h) ∧
        (∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))))).obj u.pol, ⊤)),
          (θK k).act ((θK k').act s) =
            baseScalar u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) (φ ζ ^ (B k k').val) • (θK k').act ((θK k).act s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero.solution
