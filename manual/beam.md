---
title: Beam images
slug: beam
order: 27
summary: muro emit --backend beam writes exactly one exported run, with its binder grades, as a text image. Writing the file is not acceptance. muro-beam Boundary v1 checks the image again.
---

# Beam images

In brief: `--backend beam` writes `<stem>.mbi` beside the book when the book has exactly one exported `run`. The binder grades stay. A definition, data, a pair, a word, or a stream is refused. Writing the file is not acceptance. muro-beam Boundary v1 checks the image again. This backend is not a manifest target.

```
mix muro.emit path.muro --backend beam
muro emit path.muro --backend beam
```

```
{:ok, files} = Muro.emit_beam("path.muro")
```

`files` is a list of one path, the `.mbi`. That result is exactly one exported run whose body erased. A book that does not check writes nothing. A book with no exported run writes nothing and returns `beam:entry`. A book with more than one exported run returns an error.

## The file

The file is one line and a trailing newline. Version 1 is the image. Boundary version 1 is the boundary the runtime checks the term against.

```
image    ::= (muro-beam-image 1 (boundary 1) (entry <prog>))
prog     ::= (seq <gtm> (done))
gtm      ::= (gvar <nat>)
           | (gtyp <nat>)
           | (glam <pair> <gtm>)
           | (gpi <pair> <gtm>)
           | (gapp <gtm> <gtm>)
           | gze
           | (gsu <gtm>)
           | (gmatch <gtm> <gtm> <gtm>)
pair     ::= (<grade> <grade>)
grade    ::= <point> | (iv <point> <point>)
point    ::= <nat> | w
nat      ::= 0 | 1 | 2 | …
```

Tokens are separated by one space. There is no other whitespace. A natural is decimal, with no leading zero except `0`. `w` is ω. `(iv a b)` is the inclusive interval from `a` to `b`. A pair is the computational grade, then the type grade.

A variable is a de Bruijn index. `0` is the nearest binder. `(gvar 0)` is that variable. `(gtyp 0)` is a use of it as a type. This emitter does not write `gtyp`. The grammar names it because the runtime's term has it.

`(glam (c t) e)` is a function. It opens one binder. `e` is under that binder, and `(gvar 0)` is the variable. The domain type is not in the image. `(gpi (c t) e)` is a Π. It opens one binder the same way. The type grade is not a second binder, and the domain type is not in the image. A Π erases as `gpi`. `(gapp f a)` is an application. `gze` is zero. `(gsu e)` is successor. A closed numeral `n` is `n` successors of `gze`, the same term as `suc` written out. `(gmatch e z s)` is a match on Nat. The motive is not in the image. `s` binds the predecessor at `(gvar 0)`, one binder.

The domain of `glam` and of `gpi` is dropped. An annotation is dropped. The motive of `gmatch` is dropped. The loader does not recover them. They stay in the book, and they are not part of the image the boundary accepts.

`(seq e (done))` is the whole program. `e` is the run. `(done)` does not use the value `e` returns. The binding that `seq` gives that value is the pair `(w 0)`.

`examples/images/once.mbi` is:

```
(muro-beam-image 1 (boundary 1) (entry (seq (glam (1 0) (gvar 0)) (done))))
```

That is `λ (n : (1, 0) Nat) → n`. An unmarked identity is `((iv 0 1) 0)`. A reusable identity is `(w 0)`. An erased binder whose body is `0` is `(0 0)`. `examples/images/pi.mbi` is the image of `Π (n : Nat) → n`. `examples/images/iv.mbi` is the image of `λ (n : ([0, 2], 0) Nat) → n`.

## Which definition

Success is exactly one exported `run`, and that body erases. `{:ok, files}` is that image. The command exits 0 only in this case. `run internal` is not exported. Spec, evidence, data, and sessions are omitted, and omitting them is not a refusal.

Zero exported runs is `beam:entry`. No file is written. A previous image at that path is removed. A book that does not check writes nothing and leaves a previous image where it is.

More than one exported run is a refusal, including when one of them erases. The image, when a body erases, is the first such body in book order. That file is written, the command prints the path, and the command fails. A run that also erases is `beam:entry in <name>`. A run that does not erase is `beam:<reason> in <name>`. An earlier failure is named the same way. The reasons are joined by newlines, in book order, and the chosen body is not among them.

When every exported run fails, no file is written. The message is those reasons. It is not `beam:entry`.

## Grades

The computational grade and the type grade are read off the binder.

| Binder | Computational | Type |
| --- | --- | --- |
| unmarked, `%0` | `(iv 0 1)` | `0` |
| `+` | `w` | `0` |
| `-` | `0` | `0` |
| `%1` | `1` | `0` |
| `(c, t)` | `c`, as written | `t`, as written |

An unknown quantity is `beam:grade`. A pair whose component is not a point or an interval is `beam:grade`.

The type grade of a quantity atom is `0` because a run use charges one computational use and no type use, so an identity checks. A binder mentioned only as a type, under a Π, still erases. The runtime's check refuses it: `type grade 0 does not allow 1 uses`. The kernel accepts that term. This emitter does not run that check.

`%1` and `(1, 0)` are the same image. The other emitters still replace a grade pair with the affine quantity. This one keeps the pair.

## Refusals

The message is `beam:<reason> in <name>`. The reason is the first constructor, not a walk into it.

| Reason | Term |
| --- | --- |
| `def` | a reference to a definition |
| `data` | a data type, a constructor, or a match on declared data, on `WBool`, or on `Opt` |
| `pair` | a product, a pair, or `let` of a pair |
| `stream` | `ν`, `unfold`, `uncons`, `Stream`, `Always`, `~` |
| `machine` | `I64`, `F32`, `Tensor`, and their operations |
| `word` | `U8`, `U32`, `U64`, and a word operation |
| `string` | `String` and a string operation |
| `bytes` | `Bytes`, `Slice`, and an octet operation |
| `atom` | `Atom` and a match on an atom |
| `hole` | `?` |
| `typ` | `Type` |
| `nat` | the type `Nat` |
| `unit` | `Unit`, `one`, and a match on `Unit` |
| `empty` | `Empty` and a match on it |
| `id` | an equation, `refl`, or `rewrite` |
| `numeral` | a numeral that is not a natural |
| `grade` | an unknown quantity, or a grade component that is not a point or an interval |
| `term` | a term this erasure does not know |

`beam:entry` is the book-level refusal, with no definition name.

## What the runtime checks

Writing the file is not acceptance. A successful emit means the book had exactly one exported run and that body erased. Acceptance is `InBoundary` on the closed term, in [muro-beam Boundary v1](https://github.com/doctorcorral/muro-beam/blob/main/agda/MuroBeam/Boundary.agda) (`MuroBeam.Boundary`, `boundary-version` is 1). That module is the authority. This emitter does not call it. A term in the file can fail `InBoundary`.

`seq` asks the term to lie inside the boundary, then runs the grade check in `run`, then checks `(done)` at grade `(w 0)`. `(done)` uses nothing. `w` and `0` accept zero uses, so `(seq e (done))` checks when `e` checks and lies inside the boundary.

A function under a live grade `1` is outside that boundary, including a function the grade check would accept. `glam` opens one binder, and a second `glam` under a grade `1` already in scope is outside the boundary. An interval is not a fourth runtime grade: the boundary reads it as ω.

Stepping the loaded program is not a single evaluation of the term. `seq` has to be stepped first. The value is the result of evaluating `e`, read before `(done)` clears it. Evaluating the loaded program as a whole does not return that value.
