open import Data.Nat as ℕ using (ℕ; zero; suc; _<?_; _<_; _*_; _≤_; z≤n; s≤s) renaming (_≟_ to _≟ⁿ_)
import Data.Nat.Properties as ℕₚ
open import Data.List as List using (List; []; _∷_)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; _≟_; toℕ; fromℕ; fromℕ<; suc; zero)
open import Data.Product using (_×_; proj₁; proj₂; _,_; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_; case_of_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no; does; proof; ¬?; _because_; ofⁿ; ofʸ)
open import Relation.Nullary.Decidable using (_×-dec_; _⊎-dec_)
open import Data.Unit using (⊤; tt)
open import Level using (Level)
open import Relation.Nullary.Negation using (¬_)


module NQueens where 

module For (n : ℕ) where

  Pos : Set 
  Pos = Fin n × Fin n

  ≟-× : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′}
      → (eqA : (a b : A) → Dec (a ≡ b)) → (eqB : (a b : B) → Dec (a ≡ b)) 
      → (x y : A × B)
      → Dec (x ≡ y)
  ≟-× eqA eqB (xa , xb) (ya , yb) 
      with eqA xa ya
  ...    | no ¬a = false because ofⁿ (λ {refl → ¬a refl})
  ...    | yes a 
        with eqB xb yb 
  ...      | no ¬b = false because ofⁿ (λ {refl → ¬b refl})
  ...      | yes b = true because ofʸ
                   (subst (λ s → (xa , xb) ≡ (s , yb)) a 
                 $ (subst (λ s → (xa , xb) ≡ (xa , s)) b refl))             


  _≟ᵖ_ : (p q : Pos) → (Dec (p ≡ q))
  _≟ᵖ_ = ≟-× _≟_ _≟_ 

  {-
        + – – – – – – – → x
        |
        |
        |
        |
        |
        |
        |
        ↓ 
        y
  -}

  row : Pos → Pos → Set 
  row (x₁ , y₁) (x₂ , y₂) = y₁ ≡ y₂

  row? : (p q : Pos) → Dec (row p q)
  row? (x₁ , y₁) (x₂ , y₂) = y₁ ≟ y₂

  col : Pos → Pos → Set 
  col (x₁ , y₁) (x₂ , y₂) = x₁ ≡ x₂

  col? : (p q : Pos) → Dec (col p q)
  col? (x₁ , y₁) (x₂ , y₂) = x₁ ≟ x₂

  raise : ∀ {m} → Fin m → Fin (suc m)
  raise zero = zero 
  raise (suc x) = suc (raise x)

  ∣_-ᶠ_∣ : ∀ {m} → Fin m → Fin m → Fin m
  ∣ zero   -ᶠ zero   ∣ = zero
  ∣ zero   -ᶠ suc n ∣ = suc n
  ∣ suc m -ᶠ zero   ∣ = suc m
  ∣ suc m -ᶠ suc n ∣ = raise ∣ m -ᶠ n ∣

  slash : Pos → Pos → Set 
  slash (x , y) (x′ , y′) = ∣ x -ᶠ x′ ∣ ≡ ∣ y -ᶠ y′ ∣ 

  slash? : (p q : Pos) → Dec (slash p q)
  slash? (x , y) (x′ , y′) = ∣ x -ᶠ x′ ∣ ≟ ∣ y -ᶠ y′ ∣ 

  safe : Pos → Pos → Set 
  safe p q = ¬ (row p q) × ¬ (col p q) × ¬ (slash p q) ⊎ p ≡ q

  safe? : (p q : Pos) → Dec (safe p q)
  safe? p q =     ¬? (row? p q)
            ×-dec ¬? (col? p q)
            ×-dec ¬? (slash? p q)
            ⊎-dec (p ≟ᵖ q)

  Board : ℕ → Set 
  Board m = Vec Pos m

  allCombine : (n : ℕ) → Vec (Fin n × Fin n) (n * n) 
  allCombine n = 
    Vec.concat $ 
      Vec.map (λ f → Vec.map (_, f) (Vec.allFin n)) (Vec.allFin n) 

  allProp : ∀ {n} → Vec Set n → Set
  allProp [] = ⊤
  allProp (x ∷ xs) = x × allProp xs

  allProp? : ∀ {n} 
           → (vec : Vec (Σ Set Dec) n) 
           → Dec (allProp (Vec.map proj₁ vec))
  allProp? [] = true because ofʸ tt 
  allProp? ((x , xd) ∷ xs) = xd ×-dec allProp? xs

  eachSafe : ∀ {n} → Board n → Vec (Σ Set Dec) (n * n)
  eachSafe b = 
      Vec.map 
        (λ {(i , j) → 
          ( safe  (lookup b i) (lookup b j) 
          , safe? (lookup b i) (lookup b j))}) 
        (allCombine _)

  AllSafe : ∀ {n} → Board n → Set 
  AllSafe {n} b = allProp (Vec.map proj₁ (eachSafe b))

  AllSafe? : {n : ℕ} → (b : Board n) → Dec (AllSafe b)
  AllSafe? {n} b = allProp? (eachSafe b)

  Solution : Board n → Set 
  Solution b = AllSafe b

  ----------------------------------------------------------------------

  OrderBoard : ∀ {m} → Board m → Set 
  OrderBoard {m} [] = ⊤ 
  OrderBoard {m} ((_ , row₁) ∷ rest) = suc (toℕ row₁) ≡ m × OrderBoard rest

  OrderBoard? : ∀ {m} → (b : Board m) → Dec (OrderBoard b)
  OrderBoard? {m} [] = true because ofʸ tt
  OrderBoard? {m} ((_ , row₁) ∷ rest) 
    with suc (toℕ row₁) ≟ⁿ m | OrderBoard? rest 
  ...  | yes a               | yes b = true because ofʸ (a , b)
  ...  | _                   | no ¬b = false because ofⁿ (¬b ∘ proj₂)
  ...  | no ¬a               | _     = false because ofⁿ (¬a ∘ proj₁)

  decFilter : ∀ {m} {A : Set} 
            → (f : A → Set) 
            → (∀ a → Dec (f a)) 
            → Vec A m → List (Σ A f) 
  decFilter f f-dec [] = [] 
  decFilter f f-dec (x ∷ xs) 
    with f-dec x 
  ...  | yes a = (x , a) ∷ decFilter f f-dec xs
  ...  | no ¬a = decFilter f f-dec xs

  OrderSafe : ∀ {m} → Board m → Set 
  OrderSafe board = AllSafe board × OrderBoard board

  OrderSafe? : ∀ {m} → (b : Board m) → Dec (OrderSafe b)
  OrderSafe? board = AllSafe? board ×-dec OrderBoard? board 

  putNext : {m : ℕ} 
          → m < n
          →      (Σ (Board      m ) OrderSafe) 
          → List (Σ (Board (suc m)) OrderSafe)
  putNext {m} h (board , safe , order) = decFilter OrderSafe OrderSafe? newBoard
    where 
      newBoard : Vec (Board (suc m)) n
      newBoard = 
        Vec.map 
          (λ x → ((x , fromℕ< h) ∷ board))
          (Vec.allFin n)

  solve : ∀ m → suc m ≤ n → List (Σ (Board (suc m)) OrderSafe)
  solve zero (s≤s h) = putNext {zero} (s≤s z≤n) ([] , tt , tt)
  solve (suc m) (s≤s h) = List.concatMap (putNext (s≤s h)) (solve m (ℕₚ.m≤n⇒m≤1+n h))


  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  solutions′ : List (Σ (Board n) AllSafe)
  solutions′ = case inspect n of λ where 
    (zero with≡ _) → []
    (suc n′ with≡ h) → subst (λ n → List (Σ (Board n) AllSafe)) (sym h) 
      (List.map (λ {(b , s , _) → (b , s)}) 
                (solve n′ (subst (_≤ n) h ℕₚ.≤-refl)))
  
  solutions : List (Σ (Board n) Solution)             
  solutions = solutions′ 

-- open For 8
-- so slow
-- _ : List.length solutions ≡ 92
-- _ = refl