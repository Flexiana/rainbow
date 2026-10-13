import Lean

open Lean Elab Command

namespace RainbowFixture

def polymorphicIdentity.{u} (A : Sort u) (x : A) : A := x

def constantFunction.{u, v} (A : Sort u) (B : Sort v) (x : A) (_ : B) : A := x

def applyFunction.{u, v} (A : Sort u) (B : Sort v) (f : A → B) (x : A) : B := f x

theorem implicationIdentity (P : Prop) : P → P := fun h => h

theorem implicationTransitivity (P Q R : Prop) : (P → Q) → (Q → R) → P → R :=
  fun f g p => g (f p)

def natIdentity (n : Nat) : Nat := n

def natZero : Nat := Nat.zero

def natSuccessor (n : Nat) : Nat := Nat.succ n

private def quoteString (value : String) : String := toString (repr value)

private partial def levelEDN : Level → String
  | .zero => "[:zero]"
  | .succ level => s!"[:succ {levelEDN level}]"
  | .max left right => s!"[:max {levelEDN left} {levelEDN right}]"
  | .imax left right => s!"[:imax {levelEDN left} {levelEDN right}]"
  | .param name => s!"[:param {quoteString name.toString}]"
  | .mvar id => s!"[:unsupported-level :mvar {quoteString (toString (repr id))}]"

private def binderEDN : BinderInfo → String
  | .default => ":explicit"
  | .implicit => ":implicit"
  | .strictImplicit => ":strict-implicit"
  | .instImplicit => ":instance-implicit"

private partial def exprEDN : Expr → String
  | .bvar index => s!"[:bound {index}]"
  | .sort level => s!"[:sort {levelEDN level}]"
  | .const name levels =>
      s!"[:const {quoteString name.toString} [{String.intercalate " " (levels.map levelEDN)}]]"
  | .app function argument => s!"[:app {exprEDN function} {exprEDN argument}]"
  | .lam _ type body binder =>
      s!"[:lam {exprEDN type} {exprEDN body} {binderEDN binder}]"
  | .forallE _ type body binder =>
      s!"[:pi {exprEDN type} {exprEDN body} {binderEDN binder}]"
  | .letE _ type value body _ =>
      s!"[:let {exprEDN type} {exprEDN value} {exprEDN body}]"
  | .lit literal => s!"[:unsupported :literal {quoteString (toString (repr literal))}]"
  | .mdata _ expression => exprEDN expression
  | .mvar id => s!"[:unsupported :mvar {quoteString (toString (repr id))}]"
  | .fvar id => s!"[:unsupported :fvar {quoteString (toString (repr id))}]"
  | .proj typeName index structExpr =>
      s!"[:unsupported :projection {quoteString typeName.toString} {index} {exprEDN structExpr}]"

private def kindEDN : ConstantInfo → String
  | .axiomInfo _ => ":axiom"
  | .thmInfo _ => ":theorem"
  | .defnInfo _ => ":definition"
  | .opaqueInfo _ => ":definition"
  | .quotInfo _ => ":unsupported-quotient"
  | .inductInfo _ => ":unsupported-inductive"
  | .ctorInfo _ => ":unsupported-constructor"
  | .recInfo _ => ":unsupported-recursor"

private def declarationEDN (environment : Environment) (name : Name) : String :=
  match environment.find? name with
  | none => "{" ++ s!":foreign/name {quoteString name.toString} :foreign/error :missing" ++ "}"
  | some info =>
      let levels := info.levelParams.map (fun level => quoteString level.toString)
      let value := match info.value? true with | some body => exprEDN body | none => "nil"
      "{" ++ s!":foreign/name {quoteString name.toString} :foreign/kind {kindEDN info} " ++
      s!":foreign/universes [{String.intercalate " " levels}] " ++
      s!":foreign/type {exprEDN info.type} :foreign/value {value} " ++
      s!":foreign/unsafe? {if info.isUnsafe then "true" else "false"}" ++ "}"

private def exportedNames : List Name :=
  [`RainbowFixture.polymorphicIdentity, `RainbowFixture.constantFunction,
   `RainbowFixture.applyFunction, `RainbowFixture.implicationIdentity,
   `RainbowFixture.implicationTransitivity, `RainbowFixture.natIdentity,
   `RainbowFixture.natZero, `RainbowFixture.natSuccessor]

run_cmd do
  let environment ← getEnv
  let declarations := exportedNames.map (declarationEDN environment)
  let output :=
    "{:foreign/schema-version 1 :foreign/system :lean " ++
    ":foreign/version \"4.30.0\" " ++
    ":foreign/commit \"d024af099ca4bf2c86f649261ebf59565dc8c622\" " ++
    s!":foreign/declarations [{String.intercalate " " declarations}]}\n"
  IO.FS.writeFile "artifacts/day12/lean-neutral.edn" output

end RainbowFixture
