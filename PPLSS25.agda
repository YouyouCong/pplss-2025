module PPLSS25 where

open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _≤_; z≤n; s≤s; compare; less; equal; greater)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 変数宣言
variable
  A B : Set
  m n k : ℕ


------------------------------
-- 入門編：リスト操作
------------------------------

-- List 上の append 関数
appendL : List A → List A → List A
appendL []       l = l
appendL (x ∷ xs) l = x ∷ appendL xs l

-- Vec 上の append 関数
appendV : Vec A m → Vec A n → Vec A (m + n)
appendV []       l = l
appendV (x ∷ xs) l = x ∷ appendV xs l

-- List 上の map 関数
mapL : (A → B) → List A → List B
mapL f []       = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

-- 演習問題１: Vec 上の map 関数
mapV : (A → B) → Vec A n → Vec B n
mapV f []       = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

-- List 上の head 関数
-- headL : List A → A
-- headL []       = ?
-- headL (x ∷ xs) = x

headL : List A → Maybe A
headL []       = nothing
headL (x ∷ xs) = just x

-- Vec 上の head 関数
headV : Vec A (suc n) → A
headV (x ∷ xs) = x

-- List 上の lookup 関数
-- lookupL : List A → ℕ → A
-- lookupL []       n       = ?
-- lookupL (x ∷ xs) zero    = x
-- lookupL (x ∷ xs) (suc n) = lookupL xs n

-- Vec 上の lookup 関数
lookupV : Vec A n → Fin n → A
lookupV (x ∷ xs) zero    = x
lookupV (x ∷ xs) (suc n) = lookupV xs n

-- List 上の lookup 関数 (別解)
lookupL2 : (l : List A) → Fin (length l) → A
lookupL2 (x ∷ xs) zero    = x
lookupL2 (x ∷ xs) (suc n) = lookupL2 xs n


------------------------------
-- 初級編：型付き言語とインタプリタ
------------------------------

-- BoolNat 言語の式 (型なし)
data Exp : Set where
  tru  : Exp
  fls  : Exp
  num  : ℕ → Exp
  ifte : Exp → Exp → Exp → Exp

-- 型なしの式の例
exp1 : Exp
exp1 = ifte tru (num 1) (num 0)

exp2 : Exp
exp2 = ifte (num 1) (num 1) (num 0)

exp3 : Exp
exp3 = ifte tru (num 1) fls

-- BoolNat 言語の値 (型なし)
data Val : Set where
  vtru : Val
  vfls : Val
  vnum : ℕ → Val

-- 型なし言語のインタプリタ
-- interp : Exp → Val
-- interp tru     = vtru
-- interp fls     = vfls
-- interp (num n) = vnum n
-- interp (ifte e₁ e₂ e₃) with interp e₁
-- ... | vtru   = interp e₂
-- ... | vfls   = interp e₃
-- ... | vnum n = {!   !}

-- BoolNat 言語の型
data Ty : Set where
  boolty : Ty
  numty  : Ty

variable
  τ : Ty

-- BoolNat 言語の式 (型付き)
data TExp : Ty → Set where
  tru  : TExp boolty
  fls  : TExp boolty
  num  : ℕ → TExp numty
  ifte : TExp boolty → TExp τ → TExp τ → TExp τ
  -- 演習問題２：is0 を追加

-- 型付きの式の例
texp1 : TExp numty
texp1 = ifte tru (num 1) (num 0)

-- texp2 : TExp numty
-- texp2 = ifte (num 1) (num 1) (num 0)

-- texp3 : TExp numty
-- texp3 = ifte tru (num 1) fls

-- BoolNat 言語の値 (型付き)
data TVal : Ty → Set where
  vtru  : TVal boolty
  vfls  : TVal boolty
  vnum  : ℕ → TVal numty

-- 型付き言語のインタプリタ
interp2 : TExp τ → TVal τ
interp2 tru     = vtru
interp2 fls     = vfls
interp2 (num n) = vnum n
interp2 (ifte e₁ e₂ e₃) with interp2 e₁
... | vtru = interp2 e₂
... | vfls = interp2 e₃
-- 演習問題２：is0 のケースを追加

-- 型の解釈
interpTy : Ty → Set
interpTy boolty = Bool
interpTy numty  = ℕ

-- プリミティブの値を返すインタプリタ
interp3 : TExp τ → interpTy τ
interp3 tru     = true
interp3 fls     = false
interp3 (num n) = n
interp3 (ifte e₁ e₂ e₃) with interp3 e₁
... | true      = interp3 e₂
... | false     = interp3 e₃
-- 演習問題２：is0 のケースを追加


------------------------------
-- 中級編
------------------------------

-- 昇順に整列された自然数のリスト
data OList (b : ℕ) : Set where
  nil  : OList b
  cons : (n : ℕ) → b ≤ n → OList n → OList b

-- 整列されたリストの例
goodList : OList 0
goodList = cons 1 z≤n (cons 2 (s≤s z≤n) nil)

-- 整列されていないリストの例
-- badList : OList 0
-- badList = cons 2 z≤n (cons 1 {!   !} nil)

-- ≤ の性質
≤-refl : n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-suc+ : m ≤ suc (m + k)
≤-suc+ {zero} = z≤n
≤-suc+ {suc m} = s≤s ≤-suc+

-- 要素の挿入
insert : {b : ℕ} → (n : ℕ) → b ≤ n → OList b → OList b
insert n b≤n nil = cons n b≤n nil
insert m b≤m (cons n b≤n l) with compare m n 
... | less    .m k = cons m b≤m (cons n ≤-suc+ l)
... | equal   .m   = cons m b≤m (cons n ≤-refl l)
... | greater .n k = cons n b≤n (insert m ≤-suc+ l)

-- 挿入ソート
isort : List ℕ → OList 0
isort [] = nil
isort (n ∷ l) = insert n z≤n (isort l)


------------------------------
-- 応用編
------------------------------

-- ピッチ
data Pitch : Set where
  c  : Pitch
  d  : Pitch
  e  : Pitch
  f  : Pitch
  g  : Pitch
  a  : Pitch
  b  : Pitch
  c2 : Pitch

-- ピッチから自然数への変換
pitch→nat : Pitch → ℕ
pitch→nat c  = 1
pitch→nat d  = 2
pitch→nat e  = 3
pitch→nat f  = 4
pitch→nat g  = 5
pitch→nat a  = 6
pitch→nat b  = 7
pitch→nat c2 = 8

-- インターバル
data Interval : Set where
  uni : Interval
  2nd : Interval
  3rd : Interval
  4th : Interval
  5th : Interval
  6th : Interval
  7th : Interval
  oct : Interval

-- インターバルから差分への変換
interval→diff : Interval → ℕ
interval→diff uni = 0
interval→diff 2nd = 1
interval→diff 3rd = 2
interval→diff 4th = 3
interval→diff 5th = 4
interval→diff 6th = 5
interval→diff 7th = 6
interval→diff oct = 7

-- 小節
Bar : Set
Bar = Pitch × Interval

-- ベースの音
cf : Bar → ℕ
cf bar = pitch→nat (proj₁ bar)

-- はもりの音
cp : Bar → ℕ
cp bar = pitch→nat (proj₁ bar) + interval→diff (proj₂ bar)

-- インターバルが協和音であることの証明
data Consonant : Interval → Set where
  uniIsConsonant : Consonant uni
  3rdIsConsonant : Consonant 3rd
  5thIsConsonant : Consonant 5th
  6thIsConsonant : Consonant 6th
  octIsConsonant : Consonant oct

-- インターバルが5度・8度でないことの証明
data Not58 : Interval → Set where
  uniIsNot58 : Not58 uni
  2ndIsNot58 : Not58 2nd
  3rdIsNot58 : Not58 3rd
  4thIsNot58 : Not58 4th
  6thIsNot58 : Not58 6th
  7thIsNot58 : Not58 7th

-- 進行方向
data Direction : Set where
  up   : Direction
  stay : Direction 
  down : Direction

-- 2音間の進行方向
dir : ℕ → ℕ → Direction
dir n1 n2 = 
  if n1 <ᵇ n2 then up
  else if n2 <ᵇ n1 then down
  else stay

-- 2声の進行方向が同じでないことの証明
data NotDirect (bar1 bar2 : Bar) : Set where
  contrary1 : (dir (cf bar1) (cf bar2) ≡ up) ×
              (dir (cp bar1) (cp bar2) ≡ down) → 
              NotDirect bar1 bar2
  contrary2 : (dir (cf bar1) (cf bar2) ≡ down) ×
              (dir (cp bar1) (cp bar2) ≡ up) → 
              NotDirect bar1 bar2
  oblique1  : dir (cf bar1) (cf bar2) ≡ stay →
              NotDirect bar1 bar2
  oblique2  : dir (cp bar1) (cp bar2) ≡ stay →
              NotDirect bar1 bar2

-- 1小節に対する規則
valid1 : Bar → Set
valid1 bar = Consonant (proj₂ bar)

-- 隣接する2小節に対する規則
valid2 : Bar → Bar → Set
valid2 bar1 bar2 = 
  Not58 (proj₂ bar2) ⊎ NotDirect bar1 bar2

-- 対位法に従った音楽
data CP : Set

-- 最後の小節
last : CP → Bar

data CP where
  first  : (bar : Bar) → valid1 bar → CP
  extend : (cp : CP) → (bar : Bar) → 
           valid1 bar → valid2 (last cp) bar →
           CP

last (first bar v) = bar
last (extend cp bar v1 v2) = bar

-- 規則を守った音楽
goodCP : CP
goodCP = 
  extend 
    (extend 
      (extend 
        (extend (first (c , oct) octIsConsonant)
                (e , 3rd) 3rdIsConsonant (inj₁ 3rdIsNot58))
        (f , 3rd) 3rdIsConsonant (inj₁ 3rdIsNot58))
      (d , 6th) 6thIsConsonant (inj₁ 6thIsNot58))
    (c , oct) octIsConsonant (inj₂ (contrary2 (refl , refl)))

-- 規則を破った音楽
-- badCP : CP
-- badCP =
--   extend
--     (extend
--       (extend
--         (extend (first (c , oct) octIsConsonant)
--                 (e , 4th) {!   !} (inj₁ 4thIsNot58))
--         (f , 5th) 5thIsConsonant {!   !})
--       (d , 6th) 6thIsConsonant (inj₁ 6thIsNot58))
--     (c , oct) octIsConsonant (inj₂ (contrary2 (refl , refl)))

-- 演習問題３：自作の音楽
