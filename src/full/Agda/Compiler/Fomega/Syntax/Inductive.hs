-- | Compile Agda to System Fω with data types and constructor.

module Agda.Compiler.Fomega.Syntax.Inductive where


{- extract to Fomega

Examples:
---------

MiniAgda

  data Vec (A : Set) : Nat -> Set
  { vnil  : Vec A zero
  ; vcons : [n : Nat] -> (head : A) -> (tail : Vec A n) -> Vec A (suc n)
  } fields head, tail

  fun length : [A : Set] -> [n : Nat] -> Vec A n -> <n : Nat>
  { length .A .zero    (vnil A)         = zero
  ; length .A .(suc n) (vcons A n a as) = suc (length A n as)
  }

Fomega

  data Vec (A : Set) : Set
  { vnil  : Vec A
  ; vcons : (head : A) -> (tail : Vec A) -> Vec A
  }

  fun head : [A : Set] -> Vec A -> A
  { head (vcons 'head 'tail) = 'head
  }

  fun tail : [A : Set] -> Vec A -> A
  { head (vcons 'head 'tail) = 'tail
  }

  fun length : [A : Set] -> Vec A -> Nat
  { length [A]  vnil             = zero
  ; length [A] (vcons [.A] a as) = suc (length [A] as)
  }


Bidirectional extraction
========================

Types

  Base ::= D As         data type
         | ?            inexpressible type

  A,B ::= Base | A -> B | [x:K] -> B | [] -> B  with erasure markers
  A0, B0 ::= Base | A0 -> B0 | [x:K0] -> B0     without erasure markers

  |.| erase erasure markers

Inference mode:

  Term extraction:  Gamma |- t :> A  --> e    |Gamma| |- e : |A|
  Type extraction:  Gamma |- T :> K  --> A    |Gamma| |- A : |K|
  Kind extraction:  Gamma |- U :> [] --> K    |Gamma| |- K : []

Checking mode:

  Term extraction:  Gamma |- t <: A  --> e    |Gamma| |- e : |A|
  Type extraction:  Gamma |- T <: K  --> A    |Gamma| |- A : |K|
  Kind extraction:  Gamma |- U <: [] --> K    |Gamma| |- K : []

Type and kind extraction keep erasure markers!

Checking abstraction:

  Relevant abstraction:
  Gamma, x:A |- t <: B --> e
  --------------------------------
  Gamma |- \x.t <: A -> B --> \x.e

  Type abstraction:
  Gamma, x:K |- t <: B --> e : B0
  ----------------------------------------
  Gamma |- \[x].t <: [x:K] -> B --> \[x].e
      also \xt

  Irrelevant abstraction:
  Gamma |- t : B --> e
  -------------------------------
  Gamma |- \[x].t : [] -> B --> e
      also \xt

  Relevant abstraction at unknown type:
  Gamma, x:? |- t : ? --> e
  --------------------------
  Gamma |- \x.t : ? --> \x.e

  Irrelevant abstraction at unknown type:
  Gamma |- t : ? --> e
  -------------------------
  Gamma |- \[x].t : ? --> e

Checking by inference:

  Gamma |- t :> A --> e    e : |A| <: |B| --> e'
  ----------------------------------------------
  Gamma |- t <: B --> e' : B0

Casting:

  ------------------ A0 does not contain ?
  e : A0 <: A0 --> e

  ----------------------- A0 != B0 or one does contain ?
  e : A0 <: B0 --> cast e

Inferring variable:

  ----------------------------
  Gamma |- x :> Gamma(x) --> x

Inferring application:

  Relevant application:
  Gamma |- t :> A -> B --> f     Gamma |- u <: A --> e
  ----------------------------------------------------
  Gamma |- t u :> B --> f e

  Type application:
  Gamma |- t :> [x:K] -> B --> f   Gamma |- u <: K --> A
  ------------------------------------------------------
  Gamma |- t [u] :> : B[A/x] --> f [A]
      also  t u

  Irrelevant application:
  Gamma |- t :> [] -> B --> f
  ---------------------------
  Gamma |- t [u] :> B --> f
      also  t u

  Relevant application at unknown type:
  Gamma |- t :> ? --> f     Gamma |- u <: ? --> e
  -----------------------------------------------
  Gamma |- t u :> ? --> f e

  Irrelevant application at unknown type:
  Gamma |- t :> ? --> f
  -------------------------
  Gamma |- t [u] :> ? --> f

-}

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

-- | System F omega kinds.
data Kind
  = KBase
    -- ^ Kind of types ⋆.
  | KArr Kind Kind
    -- ^ Function kind (kind of type constructors) @κ → κ'@.

-- | System F omega types and type constructors.
data Type
  = TVar {-# UNPACK #-} !TVar TyArgs
    -- ^ Type (constructor) variables (applied to types).
  | TCon TCon TyArgs
    -- ^ Type constructor.
  | TLam (I.Abs Type)
    -- ^ Type abstraction @λX.T@.
  | Unknown
    -- ^ A type coming from Agda that is not representable in System Fω.
  | Erased
    -- ^ Type of erased things (proofs etc.)

type TyArgs = [Type]

-- | Type variables are represented by de Bruijn indices.
type TVar = Int

-- | Type constructors
data TCon
  = TArrow
    -- ^ Function space.
  | TForall
    -- ^ Polymorphic type.
  | TData QName
    -- ^ User defined data and record types.

-- | System F expressions.
data Expr
  = Var {-# UNPACK #-} !Var Args
    -- ^ Variables @x es@.
  | Lam ArgInfo (I.Abs Expr)
    -- ^ Term abstraction @λx.e@ or type abstraction @ΛX.e@.
  | Lit Literal
    -- ^ Constant numbers, strings, chars etc.
  | Def QName Args
    -- ^ Defined function @f es@.
  | Con I.ConHead Args
    -- ^ Data constructor @c es@.
  | Coerce Expr
    -- ^ Type cast (used for expressions that are well-typed in Agda,
    --   but ill-typed in Fω).

-- | Term variables are de Bruijn indices.
type Var = Int

-- | Classification of arguments in expression application
data ArgInfo
  = TypeArg
    -- ^ Type argument.
  | TermArg
    -- ^ Term argument.

-- | Decorated arguments.
data Arg a = Arg
  { argInfo :: ArgInfo
    -- ^ Argument decoration.
  , arg     :: a
    -- ^ The argument.
  }

-- | List of arguments.
type Args = [Arg Expr]
