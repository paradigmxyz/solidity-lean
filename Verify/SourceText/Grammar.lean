import SolidCore.Solidity.Checked
import Verify.Spec.Contract
import SolidCore.Refinement.Abi

/-!
# G0: a reference reader of Solidity source bytes into SolidCore's AST and a spec

`read` is the meaning this repository gives to the text of a source file in a small envelope,
written in Lean and evaluated by the kernel: it lexes the bytes, parses one contract, and returns
SolidCore's `SourceUnit` (what solc's AST importer produces), the contract's ABI functions with
their selectors (sorted by signature, as solc's ABI lists them), the solar-verify spec bundle of
its `@custom:succeeds-if` and `@custom:ensures` tags (what `solar-verify --emit-lean-spec`
exports), and the storage its constructor leaves.

The envelope, and nothing else (any other input reads as `none`):

* `//` comments, and `///` lines, whose text is NatSpec;
* `pragma <name> <value>;` at file level;
* one `contract <Name> { ... }` with no bases;
* state variables `uint256 public <name>;`, with no initializer;
* functions `function <name>(uint256 <p>, ...) external { <x> = <y>; ... }`, where each
  `<y>` is an identifier or a decimal literal;
* on a function, NatSpec lines that are free text or one of
  `@custom:succeeds-if <e>` and `@custom:ensures <e>`, where `<e>` is built from decimal
  literals, parameters, state variables, `msg.value`, `old(<e>)`, `==`, `&&` and
  parentheses (`&&` binds looser than `==` and groups to the left).

A state variable `x` read in a spec is the 32-byte word at its slot (the `k`-th declared
variable is at slot `k`); the `i`-th parameter is argument `i`.
-/

namespace SolidCore.Verify.SourceText

open SolidCore.Solidity

/-- `pragma` -/
def kwPragma : List Nat := [112, 114, 97, 103, 109, 97]

/-- `contract` -/
def kwContract : List Nat := [99, 111, 110, 116, 114, 97, 99, 116]

/-- `uint256` -/
def kwUint256 : List Nat := [117, 105, 110, 116, 50, 53, 54]

/-- `public` -/
def kwPublic : List Nat := [112, 117, 98, 108, 105, 99]

/-- `function` -/
def kwFunction : List Nat := [102, 117, 110, 99, 116, 105, 111, 110]

/-- `external` -/
def kwExternal : List Nat := [101, 120, 116, 101, 114, 110, 97, 108]

/-- `msg` -/
def kwMsg : List Nat := [109, 115, 103]

/-- `value` -/
def kwValue : List Nat := [118, 97, 108, 117, 101]

/-- `old` -/
def kwOld : List Nat := [111, 108, 100]

/-- `@custom:succeeds-if` -/
def tagSucceedsIf : List Nat := [64, 99, 117, 115, 116, 111, 109, 58, 115, 117, 99, 99, 101, 101, 100, 115, 45, 105, 102]

/-- `@custom:ensures` -/
def tagEnsures : List Nat := [64, 99, 117, 115, 116, 111, 109, 58, 101, 110, 115, 117, 114, 101, 115]

/-! ## Bytes -/

def isSpace (c : Nat) : Bool := c == 32 || c == 10 || c == 13 || c == 9
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isAlpha (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || c == 36
def isAlnum (c : Nat) : Bool := isAlpha c || isDigit c

/-- The string of ASCII bytes. -/
def str (l : List Nat) : String := String.ofList (l.map Char.ofNat)

/-- The value of decimal digits. -/
def digitsVal (l : List Nat) : Nat := l.foldl (fun n c => 10 * n + (c - 48)) 0

def dropSpaces (l : List Nat) : List Nat := l.dropWhile isSpace

def trimRight (l : List Nat) : List Nat := (dropSpaces l.reverse).reverse

/-- `p` is a prefix of `l`: the rest. -/
def stripPrefix : List Nat → List Nat → Option (List Nat)
  | [], l => some l
  | _ :: _, [] => none
  | a :: p, b :: l => if a == b then stripPrefix p l else none

/-- Lexicographic order on byte strings. -/
def ltBytes : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && ltBytes as bs)

/-! ## Tokens -/

inductive Tok where
  | ident (s : List Nat)
  | num (s : List Nat)
  | sym (s : List Nat)
  /-- The text of one `///` line. -/
  | doc (s : List Nat)
  /-- `pragma name value;`, the value with its spaces trimmed. -/
  | pragma (name value : List Nat)
  deriving Repr, DecidableEq

/-- The single-byte symbols: `{ } ( ) ; = . ,`. -/
def singleSyms : List Nat := [123, 125, 40, 41, 59, 61, 46, 44]

/-- The tokens of the bytes, with fuel (each step consumes a byte; `lex` gives enough). -/
def lexF : Nat → List Nat → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: cs =>
    if isSpace c then lexF n cs
    else if c == 47 then
      match cs with
      | 47 :: 47 :: rest =>
        let (line, rest') := rest.span (· != 10)
        (Tok.doc line :: ·) <$> lexF n rest'
      | 47 :: rest => lexF n (rest.dropWhile (· != 10))
      | _ => none
    else if isAlpha c then
      let (w, rest) := cs.span isAlnum
      if c :: w == kwPragma then
        let (name, rest) := (dropSpaces rest).span isAlnum
        let (val, rest) := (dropSpaces rest).span (· != 59)
        match rest with
        | 59 :: rest => (Tok.pragma name (trimRight val) :: ·) <$> lexF n rest
        | _ => none
      else (Tok.ident (c :: w) :: ·) <$> lexF n rest
    else if isDigit c then
      let (w, rest) := cs.span isDigit
      if rest.head?.any isAlpha then none else (Tok.num (c :: w) :: ·) <$> lexF n rest
    else if c == 61 && cs.head? == some 61 then (Tok.sym [61, 61] :: ·) <$> lexF n cs.tail
    else if c == 38 && cs.head? == some 38 then (Tok.sym [38, 38] :: ·) <$> lexF n cs.tail
    else if singleSyms.contains c then (Tok.sym [c] :: ·) <$> lexF n cs
    else none

def lex (l : List Nat) : Option (List Tok) := lexF (l.length + 1) l

/-! ## Specs -/

/-- What a spec's names mean: parameters by index, state variables by slot. -/
structure Scope where
  params : List (List Nat)
  vars : List (List Nat)

def indexOf? (x : List Nat) : List (List Nat) → Option Nat
  | [] => none
  | y :: ys => if x == y then some 0 else (· + 1) <$> indexOf? x ys

/-- The word of a state variable at slot `k`. -/
def slotWord (k : Nat) : SolidCore.Spec.Term := .load (.slot k) (.lit 0) 32 (.uint 256)

def nameTerm (sc : Scope) (x : List Nat) : Option SolidCore.Spec.Term :=
  match indexOf? x sc.params with
  | some i => some (.arg i)
  | none => slotWord <$> indexOf? x sc.vars

mutual
/-- `e := c ('&&' c)*`, grouped to the left. -/
def pExpr (sc : Scope) : Nat → List Tok → Option (SolidCore.Spec.Term × List Tok)
  | 0, _ => none
  | n + 1, ts => do
    let (a, ts) ← pCmp sc n ts
    pAnd sc n a ts
def pAnd (sc : Scope) : Nat → SolidCore.Spec.Term → List Tok → Option (SolidCore.Spec.Term × List Tok)
  | 0, _, _ => none
  | n + 1, a, .sym [38, 38] :: ts => do
    let (b, ts) ← pCmp sc n ts
    pAnd sc n (.bin .and a b) ts
  | _ + 1, a, ts => some (a, ts)
/-- `c := p ('==' p)?`. -/
def pCmp (sc : Scope) : Nat → List Tok → Option (SolidCore.Spec.Term × List Tok)
  | 0, _ => none
  | n + 1, ts => do
    let (a, ts) ← pPrim sc n ts
    match ts with
    | .sym [61, 61] :: ts => do
      let (b, ts) ← pPrim sc n ts
      some (.bin .eq a b, ts)
    | _ => some (a, ts)
def pPrim (sc : Scope) : Nat → List Tok → Option (SolidCore.Spec.Term × List Tok)
  | 0, _ => none
  | _ + 1, .num s :: ts => some (.lit (Int.ofNat (digitsVal s)), ts)
  | n + 1, .ident x :: ts =>
    if x == kwMsg then
      match ts with
      | .sym [46] :: .ident v :: ts => if v == kwValue then some (.env .value, ts) else none
      | _ => none
    else if x == kwOld then
      match ts with
      | .sym [40] :: ts => do
        let (e, ts) ← pExpr sc n ts
        match ts with
        | .sym [41] :: ts => some (.old e, ts)
        | _ => none
      | _ => none
    else (fun t => (t, ts)) <$> nameTerm sc x
  | n + 1, .sym [40] :: ts => do
    let (e, ts) ← pExpr sc n ts
    match ts with
    | .sym [41] :: ts => some (e, ts)
    | _ => none
  | _ + 1, _ => none
end

/-- A whole spec expression. -/
def specExpr (sc : Scope) (text : List Nat) : Option SolidCore.Spec.Term := do
  let ts ← lex text
  let (e, rest) ← pExpr sc (ts.length + 1) ts
  if rest.isEmpty then some e else none

/-- The succeeds-if and ensures conditions of a function's NatSpec lines, in order. A line that
does not start with `@` is free text; any other tag is outside the envelope. -/
def natspec (sc : Scope) : List (List Nat) → Option (List SolidCore.Spec.Term × List SolidCore.Spec.Term)
  | [] => some ([], [])
  | line :: lines => do
    let (s, e) ← natspec sc lines
    let line := dropSpaces line
    if line.head? != some 64 then some (s, e)
    else match stripPrefix tagSucceedsIf line with
      | some (c :: rest) => if isSpace c then (fun t => (t :: s, e)) <$> specExpr sc rest else none
      | _ => match stripPrefix tagEnsures line with
        | some (c :: rest) => if isSpace c then (fun t => (s, t :: e)) <$> specExpr sc rest else none
        | _ => none

/-! ## The contract -/

/-- A function as read: name, parameter names, body assignments, NatSpec lines. -/
structure FnRead where
  name : List Nat
  params : List (List Nat)
  body : List (List Nat × Tok)
  docs : List (List Nat)

/-- What a contract's members read as. -/
inductive Member where
  | var (name : List Nat)
  | fn (f : FnRead)

def takeDocs : List Tok → List (List Nat) × List Tok
  | .doc s :: ts => let (d, ts) := takeDocs ts; (s :: d, ts)
  | ts => ([], ts)

/-- `uint256 p (, uint256 p)*` up to `)`. -/
def pParams : Nat → List Tok → Option (List (List Nat) × List Tok)
  | 0, _ => none
  | _ + 1, .sym [41] :: ts => some ([], ts)
  | n + 1, .ident t :: .ident p :: ts =>
    if t != kwUint256 then none else
    match ts with
    | .sym [41] :: ts => some ([p], ts)
    | .sym [44] :: ts@(.ident _ :: _) => (fun (ps, ts) => (p :: ps, ts)) <$> pParams n ts
    | _ => none
  | _ + 1, _ => none

/-- `x = y;` statements up to `}`. -/
def pBody : Nat → List Tok → Option (List (List Nat × Tok) × List Tok)
  | 0, _ => none
  | _ + 1, .sym [125] :: ts => some ([], ts)
  | n + 1, .ident x :: .sym [61] :: y :: .sym [59] :: ts =>
    match y with
    | .ident _ | .num _ => (fun (ss, ts) => ((x, y) :: ss, ts)) <$> pBody n ts
    | _ => none
  | _ + 1, _ => none

/-- Members up to `}`. -/
def pMembers : Nat → List Tok → Option (List Member × List Tok)
  | 0, _ => none
  | n + 1, ts =>
    let (docs, ts) := takeDocs ts
    match ts with
    | .sym [125] :: ts => if docs.isEmpty then some ([], ts) else none
    | .ident t :: .ident v :: .ident x :: .sym [59] :: ts =>
      if t == kwUint256 && v == kwPublic && docs.isEmpty then
        (fun (ms, ts) => (Member.var x :: ms, ts)) <$> pMembers n ts
      else none
    | .ident f :: .ident name :: .sym [40] :: ts =>
      if f != kwFunction then none else do
      let (ps, ts) ← pParams n ts
      match ts with
      | .ident e :: .sym [123] :: ts =>
        if e != kwExternal then none else do
        let (body, ts) ← pBody n ts
        let (ms, ts) ← pMembers n ts
        some (Member.fn ⟨name, ps, body, docs⟩ :: ms, ts)
      | _ => none
    | _ => none

/-- The file: pragmas, then one contract (a NatSpec comment before it is free text). -/
def pUnit (ts : List Tok) : Option (List (List Nat × List Nat) × List Nat × List Member) :=
  let pragmas := ts.filterMap fun | .pragma n v => some (n, v) | _ => none
  let ts := ts.dropWhile fun | .pragma _ _ => true | _ => false
  let (_, ts) := takeDocs ts
  match ts with
  | .ident c :: .ident name :: .sym [123] :: ts =>
    if c != kwContract then none else do
    let (ms, rest) ← pMembers (ts.length + 1) ts
    if rest.isEmpty then some (pragmas, name, ms) else none
  | _ => none

/-! ## SolidCore's AST, the ABI and the spec -/

def uintTy : Ty := Ty.uint 256

def atomExpr : Tok → Expr
  | .num s => Expr.literal (Literal.number (str s))
  | .ident s => Expr.ident (str s)
  | _ => Expr.ident ""

def stateVarItem (x : List Nat) : ContractItem :=
  ContractItem.stateVar
    { name := str x, ty := uintTy, visibility := some Visibility.public_,
      mutability := VarMutability.mutable, override? := none, init := none }

def functionItem (f : FnRead) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some (str f.name),
      visibility := some Visibility.external_, mutability := StateMutability.nonpayable,
      params := f.params.map fun p => { name := some (str p), ty := uintTy, location := none },
      returns := [], virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block (f.body.map fun (x, y) =>
        Stmt.expr (Expr.assign (Expr.ident (str x)) AssignOp.assign (atomExpr y)))) }

def memberItem : Member → ContractItem
  | .var x => stateVarItem x
  | .fn f => functionItem f

/-- A function's ABI signature, as bytes. -/
def signature (name : List Nat) (arity : Nat) : List Nat :=
  name ++ [40] ++ (List.intercalate [44] (List.replicate arity kwUint256)) ++ [41]

def selector (sig : List Nat) : Nat := SolidCore.Solidity.Source.ABI.selectorFromSignature (str sig)

/-- The ABI entries of a member: a function, or a public variable's getter. -/
def memberAbi : Member → List Nat × Nat
  | .var x => (signature x 0, 0)
  | .fn f => (signature f.name f.params.length, f.params.length)

def insertBy (e : List Nat × Nat) : List (List Nat × Nat) → List (List Nat × Nat)
  | [] => [e]
  | x :: xs => if ltBytes e.1 x.1 then e :: x :: xs else x :: insertBy e xs

def sortAbi (l : List (List Nat × Nat)) : List (List Nat × Nat) := l.foldr insertBy []

def abiFn (e : List Nat × Nat) : String × SolidCore.Refinement.Abi.Fn :=
  (str e.1, ⟨selector e.1, List.replicate e.2 (.uint 256)⟩)

def fnSpec (cname : List Nat) (vars : List (List Nat)) (f : FnRead) : Option SolidCore.Spec.FnSpec := do
  let (succ, ens) ← natspec ⟨f.params, vars⟩ f.docs
  some { name := str (cname ++ [46] ++ f.name),
         selector := selector (signature f.name f.params.length),
         params := List.replicate f.params.length (.uint 256), rets := [], payable := false,
         requires := [], ensures := ens, succeedsIf := succ }

/-- What the text means. -/
structure Reading where
  unit : SourceUnit
  contract : String
  /-- The ABI functions, signature and selector with parameters, sorted by signature. -/
  abi : List (String × SolidCore.Refinement.Abi.Fn)
  bundle : SolidCore.Spec.Bundle
  /-- What the constructor leaves in storage. -/
  storage : List (Nat × Nat)

/-- **The frontend**: the reading of a source file's bytes, or `none` outside the envelope. -/
def read (bytes : List Nat) : Option Reading := do
  let ts ← lex bytes
  let (pragmas, cname, ms) ← pUnit ts
  let vars := ms.filterMap fun | .var x => some x | _ => none
  let fns := ms.filterMap fun | .fn f => some f | _ => none
  let specs ← fns.mapM (fnSpec cname vars)
  let decl : ContractDecl :=
    { kind := ContractKind.contract, name := str cname, abstract := false, bases := [],
      items := ms.map memberItem }
  some { unit := { items := pragmas.map (fun (n, v) => SourceItem.pragma (str n) (str v)) ++
                    [SourceItem.contract decl] },
         contract := str cname,
         abi := (sortAbi (ms.map memberAbi)).map abiFn,
         bundle := { fuel := 0,
                     spec := { name := str cname, fns := [], invariants := [], ghosts := [],
                               specs := specs } },
         storage := [] }

end SolidCore.Verify.SourceText
