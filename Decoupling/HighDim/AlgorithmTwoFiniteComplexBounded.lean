import Decoupling.HighDim.AlgorithmTwoFiniteComplexBasis

/-!
# Total finite basis from an interval of original free coordinates

The total order is the explicit `finSigmaFinEquiv` order, preserving each
input term's basis. Outside the interval the supplied rank is zero.
This is a representation construction, not a freeness assertion about
an unknown projective summand.
-/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory
noncomputable section
universe u
variable {R : Type u} [CommRing R]

abbrev totalRank (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ) :=
  ∑ i : Fin length, rank (lo + i)

def totalDegree (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ) : Vector ℤ (totalRank rank lo length) :=
  Vector.ofFn fun a => lo + ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm a).1

theorem totalDegree_get (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ)
    (a : Fin (totalRank rank lo length)) :
    (totalDegree rank lo length).get a =
      lo + ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm a).1 := by
  change (Vector.ofFn (fun b => lo + ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm b).1))[a.val] = _
  rw [Vector.getElem_ofFn]

@[simp] theorem totalDegree_at (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ)
    (a : (i : Fin length) × Fin (rank (lo+i))) :
    (totalDegree rank lo length).get (finSigmaFinEquiv a) = lo + a.1 := by
  rw [totalDegree_get, Equiv.symm_apply_apply]

def fiberIndex (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ) (j : ℤ)
    (a : Fiber (totalDegree rank lo length) j) : Fin (rank j) :=
  let z := (finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm a.val
  Fin.cast (congrArg rank (show lo + z.1 = j by simpa only [totalDegree_get] using a.property)) z.2

theorem fiberIndex_injective (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ) (j : ℤ) :
    Function.Injective (fiberIndex rank lo length j) := by
  intro a b hab
  apply Subtype.ext
  apply (finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm.injective
  let za := (finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm a.val
  let zb := (finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm b.val
  have ha : lo + za.1 = j := by simpa only [totalDegree_get] using a.property
  have hb : lo + zb.1 = j := by simpa only [totalDegree_get] using b.property
  have hfst : za.1 = zb.1 := by apply Fin.ext; omega
  have hsnd : za.2.val = zb.2.val := congrArg Fin.val hab
  apply Sigma.ext hfst
  exact (Fin.heq_ext_iff (congrArg (fun i : Fin length => rank (lo+i)) hfst)).mpr hsnd

theorem fiberIndex_surjective (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo + length ≤ j → rank j = 0) (j : ℤ) :
    Function.Surjective (fiberIndex rank lo length j) := by
  intro a
  have hj : lo ≤ j ∧ j < lo + length := by
    have ha := a.isLt
    by_contra hn
    have hz : rank j = 0 := outside j (by omega)
    omega
  let slot : Fin length := ⟨(j-lo).toNat, by omega⟩
  have hslot : lo + (slot : ℤ) = j := by dsimp [slot]; omega
  let z : (i : Fin length) × Fin (rank (lo+i)) :=
    ⟨slot, Fin.cast (congrArg rank hslot).symm a⟩
  refine ⟨⟨finSigmaFinEquiv z, by simpa using hslot⟩, ?_⟩
  apply Fin.ext
  change (((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm
    ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))) z)).2).val = a.val
  rw [Equiv.symm_apply_apply]
  rfl

def fiberIndexEquiv (rank : ℤ → ℕ) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo + length ≤ j → rank j = 0) (j : ℤ) :
    Fiber (totalDegree rank lo length) j ≃ Fin (rank j) :=
  Equiv.ofBijective (fiberIndex rank lo length j)
    ⟨fiberIndex_injective rank lo length j, fiberIndex_surjective rank lo length outside j⟩

/-- The original coordinates, only reindexed by explicit degree and
within-degree integer indices, supply the total coordinate interface. -/
def Coordinates.ofBounded {C : CochainComplex (ModuleCat R) ℤ}
    (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo + length ≤ j → c.rank j = 0) :
    Coordinates C (totalRank c.rank lo length) :=
  Coordinates.ofDegreewise (totalDegree c.rank lo length) (fun j =>
    (c.equiv j).trans (LinearEquiv.funCongrLeft R R (fiberIndexEquiv c.rank lo length outside j)))

/-- Zero terms force zero original coordinate rank over a nonzero ring. -/
theorem rank_zero_of_isZero [Nontrivial R] {C : CochainComplex (ModuleCat R) ℤ}
    (c : StableFree.Coordinates C) (j : ℤ) (hz : CategoryTheory.Limits.IsZero (C.X j)) : c.rank j = 0 := by
  let := ModuleCat.subsingleton_of_isZero hz
  by_contra hn
  have hp : 0 < c.rank j := Nat.pos_of_ne_zero hn
  have he : (fun _ : Fin (c.rank j) => (1 : R)) = 0 := by
    simpa using congrArg (c.equiv j)
      (Subsingleton.elim ((c.equiv j).symm (fun _ => 1)) ((c.equiv j).symm 0))
  exact one_ne_zero (congrFun he ⟨0,hp⟩)

/-- Native strict bounds discharge the zero-rank conditions internally. -/
def Coordinates.ofStrictBounds [Nontrivial R] {C : CochainComplex (ModuleCat R) ℤ}
    (c : StableFree.Coordinates C) (lo hi : ℤ) [C.IsStrictlyGE lo] [C.IsStrictlyLE hi] :
    Coordinates C (totalRank c.rank lo (hi-lo+1).toNat) :=
  Coordinates.ofBounded c lo (hi-lo+1).toNat (by
    intro j hj
    apply rank_zero_of_isZero c j
    rcases hj with hj | hj
    · exact C.isZero_of_isStrictlyGE lo j hj
    · exact C.isZero_of_isStrictlyLE hi j (by omega))

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
