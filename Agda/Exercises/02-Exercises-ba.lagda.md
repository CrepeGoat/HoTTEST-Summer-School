# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises-ba where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) =  (inl a) , (inl b)
[i] (inr c) =  (inr c) , (inr c)

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] f = (λ x →  f (inl x)) , λ x →  f (inr x)

--[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
--[iv] = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] if-A-then-B  not-b a = not-b (if-A-then-B a)

--[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
--[vi] = {!!}

--[vii] : {A B : Type} → ((A → B) → A) → A
--[vii] = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii]  x a b =  x (a , b)

--[ix] : {A : Type} {B : A → Type}
--    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
--[ix] = {!!}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
pr₁ ([x] g) a =  pr₁ (g a)
pr₂ ([x] g) a =  pr₂ (g a)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne nnnA a =  nnnA (λ nA → nA a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor A-then-B nnA nB = nnA (nB ∘ A-then-B)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli A-then-nnB nnA nB = nnA (λ a → A-then-nnB a nB)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
-- bool-≡-char₁ b b' eq = ?
bool-≡-char₁ b b (refl b) = id , id
```


### Exercise 3 (★★)

Using ex. 2, conclude that
```agda
true≢false : ¬ (true ≡ false)
true≢false t-eq-f = bool-≡-char₁ true false t-eq-f .pr₁ ⋆
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (b2b' , b'2b) = refl true
bool-≡-char₂ true false (b2b' , b'2b) = 𝟘-elim (b2b' ⋆)
bool-≡-char₂ false true (b2b' , b'2b) = 𝟘-elim (b'2b ⋆)
bool-≡-char₂ false false (b2b' , b'2b) = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A .pr₁ dec-= .pr₁ x y
  with dec-= x y
... | inl q = true
... | inr ¬q  = false
decidable-equality-char A .pr₁ dec-= .pr₂ x y .pr₁ p
  with dec-= x y
... | inl q = refl true
... | inr ¬q = 𝟘-nondep-elim (¬q p)
decidable-equality-char A .pr₁ dec-= .pr₂ x y .pr₂ f
  with dec-= x y
... | inl q = q

decidable-equality-char A .pr₂ (does-a₁=a₂ , bool-dec) x y
  with Bool-has-decidable-equality (does-a₁=a₂ x y) true
... | inl q = inl ((bool-dec x y .pr₂) q  )
... | inr q = inr ((q) ∘ (bool-dec x y .pr₁))
```
