import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-! # Exercises to practice -/

variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup

-- Prove that the trivial subgroup of the integers has index zero.
example : (⊥ : AddSubgroup ℤ).index = 0 := by
  rw [@AddSubgroup.index_bot]
  exact Nat.card_eq_zero_of_infinite

/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    Subgroup.comap (ψ.comp φ) U = Subgroup.comap φ (Subgroup.comap ψ U) := by
  rw [Subgroup.comap_comap]

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    Subgroup.map (ψ.comp φ) S = Subgroup.map ψ (Subgroup.map φ S) := by
  rw [Subgroup.map_map]


/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  calc
    m + m = (2 : R) • m := by rw [two_smul]
    _ = 0 • m := by simp [h2]
    _ = 0 := by simp

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R where
  toFun := fun x => x ^ p
  map_one' := one_pow p
  map_mul' := fun x y => mul_pow x y p
  map_zero' := zero_pow (Nat.Prime.ne_zero hp.out)
  map_add' x y := add_pow_char x y p

@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := by rfl

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusMorphism_def, ← pow_mul, ← pow_succ]
  done

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by
  intro x y hxy
  simp [frobeniusMorphism_def] at hxy
  have h : (x - y) ^ p = 0 := by
    rw [sub_eq_add_neg, add_pow_char]
    sorry
  exact sub_eq_zero.mp (pow_eq_zero h)
  done

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by
  constructor
  · exact frobeniusMorphism_injective p R
  · exact Finite.surjective_of_injective (frobeniusMorphism_injective p R)
  done

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by
  constructor
  · intro h
    rw [← iterate_frobeniusMorphism] at h
    have bij := frobeniusMorphism_bijective p R
    induction k generalizing x with
    | zero => simp at h; exact h
    | succ n ih =>
      rw [Function.iterate_succ_apply'] at h
      apply ih
      apply bij.1
      rw [h, map_one]
  · intro h; rw [h]; simp
  done

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by
  have bij := frobeniusMorphism_bijective 2 R
  obtain ⟨y, hy⟩ := bij.2 x
  use y
  rw [← hy]
  simp [frobeniusMorphism_def]
  ring
  done

end Frobenius

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

lemma IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by
  unfold IsAUnit at *
  obtain ⟨xinv, hxi⟩ := hx
  obtain ⟨yinv, hyi⟩ := hy
  use (xinv * yinv)
  rw [mul_right_comm xinv yinv (x * y)]
  rw [← mul_assoc xinv x y]
  simp_rw [hxi, one_mul]
  rw [mul_comm y yinv, hyi]
  done


noncomputable instance groupUnits : Group {x : R // IsAUnit x} where
  mul := fun x y ↦ ⟨(x * y), by exact IsAUnit.mul x.property y.property⟩
  mul_assoc := by
    simp
    intro a ha b hb c hc
    ext
    apply mul_assoc
  one := ⟨1, by use 1; simp⟩
  one_mul := by
    intro a
    ext
    exact one_mul a.val
  mul_one := by
    intro a
    ext
    exact mul_one a.val
  npow_zero := by
    intro a
    exact rfl
  npow_succ := by
    intro a b
    exact rfl
  inv := fun x ↦ ⟨ Exists.choose x.property, by
    use x.val
    rw [mul_comm]
    exact Exists.choose_spec x.property⟩
  div_eq_mul_inv := by
    intro a b
    ext
    rfl
  zpow_zero' := by exact fun a ↦ rfl
  zpow_succ' := by exact fun n a ↦ rfl
  zpow_neg' := by exact fun n a ↦ rfl
  inv_mul_cancel := by
    intro a
    ext
    exact Exists.choose_spec a.property


-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring


/-! # Exercises to hand in -/

section conjugate

/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {x * h * x⁻¹ | h ∈ H}
  mul_mem' := by
    intro a b ha hb
    simp at *
    obtain ⟨h1, ha1, hg1⟩ := ha
    obtain ⟨h2, hb2, hg2⟩ := hb
    use h1 * h2
    constructor
    · exact (Subgroup.mul_mem_cancel_right H hb2).mpr ha1
    · rw [← hg1, ← hg2]
      simp
  one_mem' := by simp
  inv_mem' := by
    simp
    intro a hy
    use a⁻¹
    constructor
    · simp [hy]
    · simp [mul_assoc]

-- Characterise normal subgroups in terms of your definition.
example {H : Subgroup G} : H.Normal ↔ (∀ g : G, ∀ h ∈ H, g * h * g⁻¹ ∈ H) := by
  constructor
  · exact fun a g h a_1 ↦ Normal.conj_mem a h a_1 g
  · exact fun a ↦ { conj_mem := fun n a_1 g ↦ a g n a_1 }

/- Prove the following lemmas. In the language of group action (next Tuesday), they prove that
a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  unfold conjugate
  simp
  rfl

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by
  unfold conjugate
  simp
  ext
  constructor
  · simp
    intro a ha hha
    use a
    constructor
    · exact ha
    · rw [← hha]
      simp [mul_assoc]
  · simp
    intro a ha hha
    use a
    constructor
    · exact ha
    · rw [← hha]
      simp [mul_assoc]

end conjugate

section finite

section

variable {G : AddSubgroup ℚ}

-- In this section, you will prove a nice group theory fact: `(ℚ, +)` has no non-trivial subgroup
-- of finite index: any finite index subgroup must be `⊤`. Follow the steps below.

-- In the proof we will consider the following subgroup, consisting of all `n`-fold multiples
-- of rational numbers.
def multiple (n : ℕ) : AddSubgroup ℚ where
  carrier := {q : ℚ | ∃ r, n * r = q}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ra, rfl⟩ := ha
    obtain ⟨rb, rfl⟩ := hb
    use ra + rb
    ring
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    intro a ha
    obtain ⟨r, rfl⟩ := ha
    use -r
    ring

-- If your definition above is correct, this proof is true by rfl.
lemma mem_multiple_iff (n : ℕ) (q : ℚ) : q ∈ multiple n ↔ ∃ r, n * r = q := by rfl

-- The next lemma is a general fact from group theory: use mathlib to find the right lemma.
-- Hint: it's similar to `Subgroup.pow_index_mem`.

lemma step1 {n : ℕ} (hG : G.index = n) (q : ℚ) : n • q ∈ G := by
  rw [← hG]
  exact AddSubgroup.nsmul_index_mem G q

lemma step2 {n : ℕ} (hG : G.index = n) : multiple n ≤ G := by
  intro q hq
  obtain ⟨r, rfl⟩ := hq
  exact step1 hG r


lemma step3 {n : ℕ} (hn : n ≠ 0) : multiple n = ⊤ := by
  ext q
  simp
  use q / n
  field_simp

-- The goal of this exercise: (ℚ, +) has no non-trivial subgroups of finite index.
example (hG : G.index ≠ 0) : G = ⊤ := by
  have h1 : multiple G.index ≤ G := step2 rfl
  have h2 : multiple G.index = ⊤ := step3 hG
  rw [h2] at h1
  exact le_antisymm le_top h1

end

end finite

section frobenius

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
omit [IsDomain R] in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p) := by
    ext i
    simp only [mem_range, mem_insert, mem_Ioo]
    constructor
    · intro hi
      by_cases h : i = 0
      · left
        exact h
      · right
        constructor
        · omega
        · omega
    · intro hi
      cases hi with
      | inl h => subst h; exact hp'.pos
      | inr h => exact h.2
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    simp only [mem_Ioo] at hi
    exact hp'.dvd_choose_self (Nat.pos_iff_ne_zero.mp hi.1) hi.2
  have h6 : ∑ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 := by
    apply sum_eq_zero
    intro i hi
    have : p ∣ Nat.choose p i := dvd_choose i hi
    obtain ⟨k, hk⟩ := this
    rw [hk, Nat.cast_mul, CharP.cast_eq_zero]
    simp
  rw [add_pow, sum_range_succ, range_eq_insert_Ioo]
  simp [sum_insert (by simp [mem_Ioo] : (0 : ℕ) ∉ Ioo 0 p)]
  simp [h6]
  ring

end frobenius
