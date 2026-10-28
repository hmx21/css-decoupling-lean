import Decoupling.HighDim.ToricConjugateDifferential
import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The native conjugate-dual Koszul tail and the actual toric model

Source: `drafts/main.tex`, the toric-profile calculation following the
finite free model of `𝒮_X`.

This module compares actual complexes, including every differential.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] [IsDomain K] (D a : ℕ)

def conjugateTailResolution : ProjectiveResolution
    (Layers.conjugate (ModuleCat.of (Laurent K D) (TailCokernel K D a))) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).mapProjectiveResolution
    (tailResolution K D a)

def tailDual : CochainComplex (ModuleCat (Laurent K D)) ℕ :=
  ResolutionCohomology.dualComplex (conjugateTailResolution K D a)
    (ModuleCat.of (Laurent K D) (Laurent K D))

def tailDualCoordinates (n : ℕ) : (tailDual K D a).X n ≃ₗ[Laurent K D]
    Module.Dual (Laurent K D) (Term (Laurent K D) D (a + n)) :=
  conjugateHomCoordinates K (a + n)

theorem tailDual_d_coordinates (n : ℕ) (f : (tailDual K D a).X n) :
    tailDualCoordinates K D a (n + 1) ((tailDual K D a).d n (n + 1) f) =
      (boundary (Laurent K D) (fun i => bar (difference K i)) (a + n)).hom.dualMap
        (tailDualCoordinates K D a n f) := by
  change conjugateHomCoordinates K (a + n + 1)
    ((ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).map
      ((laurentComplex K D).d (a + n + 1) (a + n)) ≫ f) = _
  simp only [laurentComplex, complex_d]
  exact conjugateHomCoordinates_precomp K (a + n) (difference K) f

theorem tailDual_isZero (n : ℕ) (hn : D < a + n) : IsZero ((tailDual K D a).X n) := by
  let : Subsingleton (Term (Laurent K D) D (a + n)) := term_subsingleton (Laurent K D) hn
  let : Subsingleton ((tailDual K D a).X n) := (tailDualCoordinates K D a n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

def rightPart (j : ℕ) : CochainComplex (ModuleCat (Laurent K D)) ℕ :=
  (model K D j).restriction ComplexShape.embeddingUpNat

def rightPartTermIso (j n b : ℕ) (h : (j : ℤ) - b = n) :
    (rightPart K D j).X n ≅ ModuleCat.of (Laurent K D) (Term (Laurent K D) D b) :=
  (laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) h

variable (j : ℕ) (h : a + j = D)

def tailModelComponent (n : ℕ) : (rightPart K D j).X n ≅ (tailDual K D a).X n :=
  if hn : n ≤ j then
    rightPartTermIso K D j n (j - n) (by omega) ≪≫
      ((Hodge.dualLattice K (by omega : (j - n) + (a + n) = D)).trans
        (tailDualCoordinates K D a n).symm).toModuleIso
  else
    ((model K D j).isZero_of_isStrictlyLE j n (by omega)).iso
      (tailDual_isZero K D a n (by omega))

theorem tailModelComponent_coordinates (n b : ℕ) (hb : n + b = j)
    (x : (rightPart K D j).X n) :
    tailDualCoordinates K D a n ((tailModelComponent K D a j h n).hom x) =
      Hodge.dualLattice K (by omega : b + (a + n) = D)
        ((rightPartTermIso K D j n b (by omega)).hom x) := by
  have hn : n ≤ j := by omega
  have hb' : b = j - n := by omega
  subst b
  simp only [tailModelComponent, dite_eq_left hn]
  change tailDualCoordinates K D a n
    ((tailDualCoordinates K D a n).symm (Hodge.dualLattice K _
      ((rightPartTermIso K D j n (j - n) _).hom x))) = _
  exact (tailDualCoordinates K D a n).apply_symm_apply _

omit [IsDomain K] in
theorem rightPart_d_coordinates (n b : ℕ) (hb : n + b + 1 = j)
    (x : (rightPart K D j).X n) :
    (rightPartTermIso K D j (n + 1) b (by omega)).hom
      ((rightPart K D j).d n (n + 1) x) =
      boundary (Laurent K D) (difference K) b
        ((rightPartTermIso K D j n (b + 1) (by omega)).hom x) := by
  dsimp only [rightPart, HomologicalComplex.restriction, rightPartTermIso, model]
  erw [(laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE j)
    (i := b + 1) (j := b) (i' := (n : ℤ)) (j' := (n + 1 : ℕ))
      (by change (j : ℤ) - (b + 1 : ℕ) = n; omega)
      (by change (j : ℤ) - b = (n + 1 : ℕ); omega)]
  simp [laurentComplex]

theorem tailModelComponent_comm (n : ℕ) :
    (tailModelComponent K D a j h n).hom ≫ (tailDual K D a).d n (n + 1) =
      (rightPart K D j).d n (n + 1) ≫ (tailModelComponent K D a j h (n + 1)).hom := by
  by_cases hn : n + 1 ≤ j
  · let b := j - (n + 1)
    have hb : n + b + 1 = j := by omega
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (tailDualCoordinates K D a (n + 1)).injective
    change tailDualCoordinates K D a (n + 1)
      ((tailDual K D a).d n (n + 1) ((tailModelComponent K D a j h n).hom x)) =
        tailDualCoordinates K D a (n + 1)
          ((tailModelComponent K D a j h (n + 1)).hom ((rightPart K D j).d n (n + 1) x))
    rw [tailDual_d_coordinates, tailModelComponent_coordinates K D a j h n (b + 1) (by omega),
      tailModelComponent_coordinates K D a j h (n + 1) b (by omega),
      rightPart_d_coordinates K D a j n b hb]
    have he := congrArg (fun L => L ((rightPartTermIso K D j n (b + 1) (by omega)).hom x))
      (Hodge.dualLattice_boundary K (by omega : b + 1 + (a + n) = D))
    exact he.symm
  · exact (tailDual_isZero K D a (n + 1) (by omega)).eq_of_tgt _ _

def tailModelIso : rightPart K D j ≅ tailDual K D a :=
  HomologicalComplex.Hom.isoOfComponents (tailModelComponent K D a j h)
    (fun n m hnm => by
      change n + 1 = m at hnm
      subst m
      exact tailModelComponent_comm K D a j h n)

end
end Decoupling.HighDim.Toric
