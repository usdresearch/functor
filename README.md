# The Up-Side-Down Functor: A Reference Implementation of Smart Functors with Boundary-Visible Stance

**Author:** Shuhei Ihara

**Date:** June 22, 2026

## Abstract

The Up-Side-Down functor is not a new equality, a new physical law, or a new proof principle. It is a structured functor: a pure functor equipped with an adoptive face, a non-adoptive face, a boundary witness, and a coherence contract. The purpose of this paper is to give a reference implementation of such structured functors and of their safe composition operations. The construction treats the adoptive and non-adoptive regions not as two arbitrary pre-existing categories, but as fibers of a single USD record fibration realized over both a carrier category and a two-sided stance category. In this sense a USD functor is a categorical analogue of a smart pointer: after forgetting the additional fields it is an ordinary functor, while before forgetting it carries explicit bookkeeping for observation, non-adoption, boundary visibility, and typed composition. Six API-level compositions are specified: compression, downward restriction, extension, sideways stabilization, temporal turnover, and upward image. Each operation is presented with its type, existence conditions, mathematical implementation, and philosophical reading. The conservative intent is made explicit: USD records may organize proof search or interpretation, but USD-free conclusions must be justified in the base theory.

## Contents

- [Scope and non-claims](#scope-and-non-claims)
- [Base data](#base-data)
- [The USD record fibration](#the-usd-record-fibration)
- [USD functors as smart functors](#usd-functors-as-smart-functors)
- [Morphisms and the category of USD functors](#morphisms-and-the-category-of-usd-functors)
- [The six composition APIs](#the-six-composition-apis)
  - [C-composition: compression](#c-composition-compression)
  - [D-composition: downward restriction](#d-composition-downward-restriction)
  - [E-composition: extension by a cut vertex](#e-composition-extension-by-a-cut-vertex)
  - [S-composition: sideways shared stabilization](#s-composition-sideways-shared-stabilization)
  - [T-composition: temporal turnover](#t-composition-temporal-turnover)
  - [U-composition: upward image](#u-composition-upward-image)
  - [C-D-E and S-T-U reading order](#c-d-e-and-s-t-u-reading-order)
- [S-molecules and residue-stable sideways composites](#s-molecules-and-residue-stable-sideways-composites)
- [A syntactic reference implementation](#a-syntactic-reference-implementation)
- [Worked toy model](#worked-toy-model)
- [Relativistic test model](#relativistic-test-model)
- [Reviewer-facing checklist](#reviewer-facing-checklist)
- [Open problems](#open-problems)
- [Conclusion](#conclusion)

## Scope and non-claims

This draft responds to a common failure mode in early USD notation: terms such as relation, boundary, observation, adoption, refusal, gap, and turn can sound like explanatory prose rather than mathematical data. The present version therefore treats USD theory as a typed reference implementation. The reader should not be asked to infer the missing interfaces. They are made explicit.

This paper does not claim that USD notation proves a new equality, a new inequality, a physical theorem, or a computational separation. It does not identify boundary-visible connection with equality. It does not identify non-adoption with ordinary negation. It does not claim that the relativistic discussion below proves anything about special or general relativity. The relativistic section is a test model for the vocabulary of observers, frames, local restrictions, and temporal records.

This paper claims that one can specify a category of smart functors whose objects are ordinary functors equipped with additional USD structure, and that the main USD composition operations can be given as typed operations using standard categorical vocabulary: pushouts or gluing for compression, pullback or reindexing for downward composition, factorization for extension, fixed points for sideways stabilization, involution plus sequence reversal for temporal turnover, and Kan-style images for upward composition.

The intended comparison is with a smart pointer in programming. A raw pointer stores an address. A smart pointer stores an address together with ownership, lifetime, and release discipline. Likewise, a raw functor stores functorial action. A USD functor stores functorial action together with an adoptive face and a non-adoptive face that are stance-lifts of the same carrier, together with a boundary witness and a coherence contract. Forgetting these fields returns the raw functor. Keeping them enables safe composition of records without silently turning records into proof steps.

## Base data

This section fixes the data that later sections use. The goal is to avoid introducing objects such as $`\mathsf{Rel}`$, $`\mathsf{BVis}`$, $`\mathsf{Obs}`$, or $`\mathsf{NonAdopt}`$ as undefined prose.

Let $`\mathcal P`$ be a small category. Its objects are positions, contexts, observers, stages, regions, or local situations. A morphism $`\phi:p\to q`$ is an admissible transition of context. In concrete models $`\mathcal P`$ may be a poset, a site, or a category of local charts.

Let

```math
E:\mathcal P^{\mathrm{op}}\to \mathbf{Cat}
```

be an indexed category. For each context $`p`$ the category $`E(p)`$ contains the entities, expressions, records, or local objects available at $`p`$. For each transition $`\phi:p\to q`$, the reindexing functor $`E(\phi):E(q)\to E(p)`$ gives the local view of a $`q`$-object at $`p`$.

The category of situated occurrences is the Grothendieck construction

```math
\mathsf{Occ}(E)\mathrel{:=}\int_{\mathcal P}E.
```

An object is a pair $`(p,x)`$ with $`x\in E(p)`$. A morphism $`(p,x)\to(q,y)`$ is a pair $`(\phi,\alpha)`$ where $`\phi:p\to q`$ in $`\mathcal P`$ and

```math
\alpha:x\to E(\phi)(y)
```

in $`E(p)`$. Composition is the usual composition in the Grothendieck construction.

This definition repairs the ambiguity that appears when a set of positions is used while morphisms $`p\to q`$ are also required. From this point on, context transitions are morphisms in $`\mathcal P`$.

Let $`\mathcal C`$ be a category. A relation witness structure on $`\mathcal C`$ is a profunctor valued in posets,

```math
\mathsf{Rel}_{\mathcal C}:\mathcal C^{\mathrm{op}}\times\mathcal C\to \mathbf{Pos}.
```

An element $`r\in \mathsf{Rel}_{\mathcal C}(a,b)`$ is a witness that $`a`$ and $`b`$ are related in the specified sense. Functoriality gives transport of relation witnesses along morphisms of $`\mathcal C`$.

Boundary visibility is a substructure of relation witnesses. We write

```math
\mathsf{BVis}_{\mathcal C}\hookrightarrow \mathsf{Rel}_{\mathcal C}
```

for a subfunctor or indexed subposet. A boundary witness over $`r\in\mathsf{Rel}_{\mathcal C}(a,b)`$ is denoted

```math
\beta\in \mathsf{BVis}_{\mathcal C}(r).
```

Thus $`\mathsf{BVis}`$ is not a metaphor; it is a typed predicate over relation witnesses.

Nothing in the formal development requires $`\mathsf{Rel}`$ to be equality, isomorphism, equivalence, metric proximity, causal accessibility, or logical entailment. Those are model choices. The USD reference implementation only assumes relation witnesses and boundary witnesses.

## The USD record fibration

The adoptive and non-adoptive sides are not introduced as two unrelated categories. They arise as fibers of a single record fibration.

The stance category $`\mathsf{St}`$ has two distinguished objects

```math
U,\quad D,
```

called the adoptive stance and the non-adoptive stance. We assume an involutive equivalence

```math
\tau:\mathsf{St}\to\mathsf{St},
  \qquad \tau(U)=D,
  \qquad \tau(D)=U,
  \qquad \tau^2\cong 1_{\mathsf{St}}.
```

The category $`\mathsf{St}`$ may be taken discrete in the minimal model. In richer models it may contain comparison morphisms between stances.

A USD record fibration is a functor

```math
\pi:\mathsf{Rec}_{\mathsf{USD}}\to \mathsf{St}.
```

The fiber over $`U`$ is the adoptive record category

```math
\mathcal U\mathrel{:=}\pi^{-1}(U),
```

and the fiber over $`D`$ is the non-adoptive record category

```math
\mathcal D\mathrel{:=}\pi^{-1}(D).
```

The notation $`\mathcal U`$ and $`\mathcal D`$ therefore denotes fibers of one record fibration, not two arbitrary background categories.

Fix a carrier category $`\mathcal C`$. A carrier-realized USD record fibration over $`\mathcal C`$ is a USD record fibration together with a realization functor

```math
r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C
```

and hence a combined projection

```math
q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}.
```

We require

```math
\operatorname{pr}_{\mathsf{St}}\circ q=\pi,
  \qquad
  \operatorname{pr}_{\mathcal C}\circ q=r.
```

Thus every USD record has both a stance and a realized carrier. For $`c\in\mathcal C`$ and $`s\in\mathsf{St}`$, the notation

```math
(\mathsf{Rec}_{\mathsf{USD}})_{(c,s)}\mathrel{:=}q^{-1}(c,s)
```

denotes the category of stance-$`s`$ records realizing the carrier datum $`c`$. The notation suppresses the dependence of $`\mathsf{Rec}_{\mathsf{USD}}`$ on $`\mathcal C`$ when no confusion is possible.

The projection $`\pi:\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{St}`$ separates adoptive from non-adoptive records, but by itself it does not say which ordinary carrier object a record is about. The realization functor $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$ fills this gap. It prevents the pure carrier, the adoptive face, and the non-adoptive face of a USD functor from becoming three unrelated functors.

The record category contains typed constructors

```math
\mathsf{Obs},
  \qquad \mathsf{Adopt},
  \qquad \mathsf{NonAdopt},
  \qquad \mathsf{Bnd},
  \qquad \mathsf{Collapse},
```

with the following intended types:

```math
\begin{aligned}
  \mathsf{Obs}&: \text{raw datum}\to \mathsf{Rec}_{\mathsf{USD}},\\
  \mathsf{Adopt}&: \mathsf{Rel}_{\mathcal C}(a,b)\to \mathcal U,\\
  \mathsf{NonAdopt}&: \mathsf{Rel}_{\mathcal C}(a,b)\to \mathcal D,\\
  \mathsf{Bnd}&: \mathsf{BVis}_{\mathcal C}(r)\to \mathsf{Rec}_{\mathsf{USD}},\\
  \mathsf{Collapse}&: \mathsf{Rel}_{\mathcal C}(a,b)\to \mathsf{Rec}_{\mathsf{USD}}.\end{aligned}
```

These constructors are part of the syntax of records. A model may interpret them as evidence, annotations, proof-search traces, logs, or semantic states. The realization functor $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$ records which carrier datum such a constructed record is about; two records may have different stances while realizing the same carrier.

Given $`x,y`$ in a common context, the notation

```math
x\mathrel{\leadsto_{\mathsf{USD}}}y
```

means that a boundary-visible connection record from $`x`$ to $`y`$ has been constructed. The notation

```math
x\mathrel{\dashrightarrow_{\mathsf{USD}}}y
```

means that a proposed connection from $`x`$ to $`y`$ has been observed but is recorded on the non-adoptive side. Neither notation is equality or ordinary inequality.

## USD functors as smart functors

We now define the main object. The definition is deliberately close to a reference implementation: a USD functor is a record with fields.

Let $`\mathcal X`$ and $`\mathcal C`$ be categories. A pure carrier is an ordinary functor

```math
F:\mathcal X\to\mathcal C.
```

It is the raw functor that remains after forgetting all USD metadata.

Let $`q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}`$ be a carrier-realized USD record fibration and let $`F:\mathcal X\to\mathcal C`$ be a pure carrier. Write

```math
\underline U,\underline D:\mathcal X\to\mathsf{St}
```

for the constant functors at the two stances. A strict adoptive stance-lift of $`F`$ is a functor

```math
U_F:\mathcal X\to\mathsf{Rec}_{\mathsf{USD}}
```

such that

```math
q\circ U_F=(F,\underline U),
```

and a strict non-adoptive stance-lift of $`F`$ is a functor

```math
D_F:\mathcal X\to\mathsf{Rec}_{\mathsf{USD}}
```

such that

```math
q\circ D_F=(F,\underline D).
```

Equivalently, $`\pi U_F=\underline U`$, $`\pi D_F=\underline D`$, and $`rU_F=F=rD_F`$. In a lax model, these equalities may be replaced by specified comparison 2-cells, but the strict form is the reference implementation used in the main text.

A USD functor from $`\mathcal X`$ to $`\mathcal C`$ is a tuple

```math
\mathbb H=(F,U_F,D_F,\partial_F,\kappa_F)
```

where:

1.  $`F:\mathcal X\to\mathcal C`$ is a pure carrier functor.

2.  $`U_F:\mathcal X\to\mathsf{Rec}_{\mathsf{USD}}`$ is a strict adoptive stance-lift of $`F`$, so $`q\circ U_F=(F,\underline U)`$.

3.  $`D_F:\mathcal X\to\mathsf{Rec}_{\mathsf{USD}}`$ is a strict non-adoptive stance-lift of $`F`$, so $`q\circ D_F=(F,\underline D)`$.

4.  $`\partial_F`$ is boundary data over the common carrier $`F`$, relating the two stance-lifts. A minimal implementation treats $`\partial_F`$ as a family of witnesses

```math
\partial_F(x)\in \mathsf{Bnd}_F(U_F(x),D_F(x))
```

natural in $`x\in\mathcal X`$.

5.  $`\kappa_F`$ is a coherence contract governing lifts, boundary data, morphisms, compositions, erasure, and descent.

The critical point is that $`U_F`$ and $`D_F`$ do not merely accompany $`F`$: they are records over the same realized carrier $`F`$.

For a USD functor $`\mathbb H=(F,U_F,D_F,\partial_F,\kappa_F)`$, the coherence contract is a tuple of obligations

```math
\kappa_F=(\kappa_F^{\mathrm{lift}},
            \kappa_F^{\partial},
            \kappa_F^{\mathrm{mor}},
            \kappa_F^{\mathrm{comp}},
            \kappa_F^{\mathrm{erase}},
            \kappa_F^{\mathrm{desc}}).
```

Here:

1.  $`\kappa_F^{\mathrm{lift}}`$ asserts the stance-lift equations $`q\circ U_F=(F,\underline U)`$ and $`q\circ D_F=(F,\underline D)`$.

2.  $`\kappa_F^{\partial}`$ asserts that $`\partial_F`$ is defined over the common realized carrier $`F`$ and is natural in $`\mathcal X`$.

3.  $`\kappa_F^{\mathrm{mor}}`$ specifies what a USD morphism must preserve: carrier, U-face, D-face, boundary witness, and contract data.

4.  $`\kappa_F^{\mathrm{comp}}`$ states the closure obligations for $`\mathsf{CComp}`$, $`\mathsf{DComp}`$, $`\mathsf{EComp}`$, $`\mathsf{SComp}`$, $`\mathsf{TComp}`$, and $`\mathsf{UComp}`$.

5.  $`\kappa_F^{\mathrm{erase}}`$ prevents unlicensed USD records from yielding USD-free conclusions after erasure.

6.  $`\kappa_F^{\mathrm{desc}}`$ records which descent licenses, if any, are available for translating records into base assertions.

Thus $`\kappa_F`$ is not auxiliary prose; it is the contract that makes the smart functor safe to reference, transform, compose, erase, and descend.

There is a forgetful functor

```math
|-|:\mathsf{Smart}_{\mathsf{USD}}(\mathcal X,\mathcal C)\to [\mathcal X,\mathcal C]
```

which sends

```math
(F,U_F,D_F,\partial_F,\kappa_F)\mapsto F.
```

This is the categorical version of dereferencing the smart functor to its pure carrier.

The data $`\mathcal U`$ and $`\mathcal D`$ are not assumed independently and then attached to $`F`$. They are stance fibers of the single record fibration $`\pi:\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{St}`$, and the same records are realized in the carrier category by $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$. Consequently the adoptive and non-adoptive faces of a USD functor are stance-lifts over the same pure carrier:

```math
q\circ U_F=(F,\underline U),
  \qquad
  q\circ D_F=(F,\underline D).
```

The boundary witness $`\partial_F`$ and coherence contract $`\kappa_F`$ therefore relate two readings of one carrier, not two unrelated functors.

A free USD functor is a USD functor considered before anchoring it to particular entities. An anchored USD functor is a free USD functor equipped with endpoints or a local occurrence context. We write

```math
\mathsf{Anch}_{a,b}(\mathbb H)=\mathbb H_{a,b}:a\Rightarrow_{\mathsf{USD}}b
```

for anchoring $`\mathbb H`$ between $`a`$ and $`b`$ when the required endpoint and boundary data exist.

The distinction is essential. Functions, expressions, programs, formulas, and hypotheses may be free USD functors before they touch any particular pair of entities. Entity-to-entity contact is an anchoring of an already typed USD functor.

## Morphisms and the category of USD functors

Let

```math
\mathbb H=(F,U_F,D_F,\partial_F,\kappa_F),\qquad
  \mathbb K=(G,U_G,D_G,\partial_G,\kappa_G)
```

be USD functors from $`\mathcal X`$ to $`\mathcal C`$. A morphism $`\eta:\mathbb H\to\mathbb K`$ consists of:

1.  a natural transformation $`\eta^0:F\Rightarrow G`$ of pure carriers;

2.  a natural transformation $`\eta^U:U_F\Rightarrow U_G`$ in $`[\mathcal X,\mathsf{Rec}_{\mathsf{USD}}]`$ whose realization is the carrier transformation and whose stance component is fixed:

```math
q\eta^U=(\eta^0,\mathrm{id}_{\underline U});
```



3.  a natural transformation $`\eta^D:D_F\Rightarrow D_G`$ in $`[\mathcal X,\mathsf{Rec}_{\mathsf{USD}}]`$ whose realization is the carrier transformation and whose stance component is fixed:

```math
q\eta^D=(\eta^0,\mathrm{id}_{\underline D});
```



4.  compatibility squares showing that $`\eta^U`$ and $`\eta^D`$ preserve the boundary data $`\partial_F`$ and $`\partial_G`$ over $`\eta^0`$;

5.  preservation of the coherence contracts, in particular $`\kappa^{\mathrm{lift}}`$, $`\kappa^{\partial}`$, and $`\kappa^{\mathrm{erase}}`$.

For fixed $`\mathcal X`$ and $`\mathcal C`$, USD functors and their morphisms form a category, denoted

```math
\mathsf{Smart}_{\mathsf{USD}}(\mathcal X,\mathcal C),
```

provided the total record category admits vertical composition of $`q`$-compatible natural transformations and the coherence contracts are closed under identity and composition.

Identities are inherited componentwise from the functor category and the record category. Composition is componentwise and remains compatible with $`q`$ because carrier and stance components compose in $`\mathcal C\times\mathsf{St}`$. The boundary compatibility and contract preservation conditions are stable by the assumed closure of contracts. The forgetful projection to $`[\mathcal X,\mathcal C]`$ is functorial by construction.

This proposition is intentionally modest. It is not advertised as a deep category-theoretic theorem. It is the sanity check that the reference implementation has the shape of a category.

## The six composition APIs

The following six operations are specified as APIs. Each operation has a mathematical implementation and a natural-language reading. None is an ordinary proof rule for equality, inequality, or physical truth.

Every composition API below is required to preserve carrier-realized stance-lifts. If the output has carrier $`F':\mathcal X'\to\mathcal C`$, then its output faces must satisfy

```math
q\circ U_{F'}=(F',\underline U),
  \qquad
  q\circ D_{F'}=(F',\underline D).
```

This is the operational content of $`\kappa^{\mathrm{comp}}`$: composition may change the carrier, boundary, or indexing shape, but it may not detach U-face or D-face records from their carrier realization.

### C-composition: compression

**Input.** Two free USD functors

```math
\mathbb H:\mathcal X\to\mathcal C,
  \qquad
  \mathbb K:\mathcal Y\to\mathcal C,
```

together with an interface span

```math
\mathcal X\xleftarrow{i}\mathcal I\xrightarrow{j}\mathcal Y
```

and interface compatibility data between $`i^*\mathbb H`$ and $`j^*\mathbb K`$.

**Existence condition.** The pushout

```math
\mathcal X\sqcup_{\mathcal I}\mathcal Y
```

exists in $`\mathbf{Cat}`$, and the carrier and record data glue along the interface in a way compatible with $`q`$. In particular, the glued U-face and D-face must be stance-lifts of the glued carrier.

**Output.** A free USD functor

```math
\mathsf{CComp}_{\mathcal I}(\mathbb H,\mathbb K):
  \mathcal X\sqcup_{\mathcal I}\mathcal Y\to\mathcal C.
```



Mathematically, C-composition is gluing or compression by a pushout of domains plus compatible gluing of the carrier, adoptive face, non-adoptive face, and boundary witness. It compresses two freely available USD functors into one referenceable USD functor. It does not assert that the two inputs were identical; the joint boundary record retains the old boundary data and the new interface discrepancy.

A minimal boundary policy is

```math
\partial_{\mathsf{CComp}(\mathbb H,\mathbb K)}
  =
  \partial_{\mathbb H}\oplus
  \partial_{\mathbb K}\oplus
  \Delta_{\mathcal I}(\mathbb H,\mathbb K),
```

where $`\Delta_{\mathcal I}`$ is the interface discrepancy supplied by the model.

### D-composition: downward restriction

**Input.** A context morphism

```math
\rho:\mathcal L\to\mathcal G
```

and a USD functor over the global context $`\mathcal G`$.

**Mathematical implementation.** D-composition is reindexing or pullback:

```math
\mathsf{DComp}_{\rho}=\rho^*:
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal G,\mathcal C)\to
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal L,\mathcal C).
```



**Output.** A local USD functor $`\rho^*\mathbb H`$.

**Lift condition.** If $`\mathbb H`$ has carrier $`F`$, then the output has carrier $`\rho^*F`$, and its faces are the reindexed stance-lifts satisfying

```math
q(\rho^*U_F)=(\rho^*F,\underline U),
  \qquad
  q(\rho^*D_F)=(\rho^*F,\underline D).
```



The natural-language reading is: a large observed USD functor is lowered to a local context. The operation is not a proof that the local context satisfies the global claim. It is the typed act of reading the global record through a local index.

### E-composition: extension by a cut vertex

**Input.** An anchored USD functor

```math
\mathbb H_{a,b}:a\Rightarrow_{\mathsf{USD}}b
```

and a proposed cut vertex $`m`$.

**Existence condition.** There is factorization data in the relevant arrow category, together with a comparison 2-cell

```math
\varepsilon_m:
  \mathbb H_{a,m}\circ \mathbb H_{m,b}
  \Rightarrow
  \mathbb H_{a,b}
```

or the reverse comparison, depending on the model.

**Output.** A subdivided anchored record

```math
\mathsf{EComp}_m(\mathbb H_{a,b})
  =
  (\mathbb H_{a,m},\mathbb H_{m,b};\varepsilon_m).
```



E-composition extends one anchored USD functor by adding an internal observation point. It should be read as subdivision or refinement, not as a proof that the original record is strictly equal to the composite.

### S-composition: sideways shared stabilization

S-composition is the operation most in need of explicit existence conditions. We therefore specify the gap space before defining the operation.

For a pair of compatible USD functors $`\mathbb H,\mathbb K`$, assume a complete lattice

```math
\Lambda_{\mathbb H,\mathbb K}
```

of possible gap values. The order $`\leq`$ means “no more discrepant than” or any chosen model-specific refinement order.

A sideways interaction supplies a monotone update map

```math
\Phi_{\mathbb H,\mathbb K}:
  \Lambda_{\mathbb H,\mathbb K}\to
  \Lambda_{\mathbb H,\mathbb K}.
```

The value $`\Phi(\Delta)`$ is the new discrepancy after both sides have incorporated the current discrepancy into their non-adoptive records.

**Input.** A pair of compatible USD functors $`\mathbb H,\mathbb K`$ and a monotone gap update map $`\Phi_{\mathbb H,\mathbb K}`$ on a complete lattice of gaps.

**Existence condition.** A fixed point

```math
\Delta^*=\Phi_{\mathbb H,\mathbb K}(\Delta^*)
```

is selected. Existence follows, for example, from the Knaster-Tarski fixed point theorem when the stated monotonicity and completeness conditions hold.

**Output.** A sideways stabilized USD record

```math
\mathsf{SComp}(\mathbb H,\mathbb K;\Delta^*).
```



Natural-language reading: two USD functors do not eliminate their gap. They update their non-adoptive faces until the same gap is shared as a stable discrepancy. The completion condition is not $`\Delta^*=0`$ but shared stability.

### T-composition: temporal turnover

Let $`\mathsf{Seq}(\mathsf{Smart}_{\mathsf{USD}})`$ be the category of finite composable sequences of USD functors. An object is a finite chain

```math
\mathcal H=(\mathbb H_1,\ldots,\mathbb H_n).
```



Assume that the stance involution $`\tau:\mathsf{St}\to\mathsf{St}`$ lifts to a carrier-preserving record involution

```math
\bar\tau:\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{Rec}_{\mathsf{USD}},
  \qquad
  r\bar\tau=r,
  \qquad
  \pi\bar\tau=\tau\pi.
```

The induced operation

```math
\mathsf{Flip}_{U,D}:\mathsf{Smart}_{\mathsf{USD}}\to\mathsf{Smart}_{\mathsf{USD}}
```

sends

```math
(F,U_F,D_F,\partial_F,\kappa_F)
  \mapsto
  (F,\bar\tau D_F,\bar\tau U_F,\partial_F^\tau,\kappa_F^\tau).
```

The pure carrier is not altered. The lifted faces satisfy

```math
q(\bar\tau D_F)=(F,\underline U),
  \qquad
  q(\bar\tau U_F)=(F,\underline D),
```

so T-composition turns the record upside down without touching the realized carrier.

**Input.** A finite USD functor chain

```math
\mathcal H=(\mathbb H_1,\ldots,\mathbb H_n).
```



**Mathematical implementation.**

```math
\mathsf{TComp}(\mathcal H)
  \mathrel{:=}
  \mathsf{Rev}\bigl(\mathsf{Flip}_{U,D}(\mathbb H_1),\ldots,
             \mathsf{Flip}_{U,D}(\mathbb H_n)\bigr),
```

so that

```math
\mathsf{TComp}(\mathcal H)
  =
  (\mathbb H_n^\tau,\ldots,\mathbb H_1^\tau).
```



**Output.** A temporally turned-over USD record chain.

T-composition touches no entity. It reverses the order of the record chain and applies the carrier-preserving stance turnover to every adoptive and non-adoptive face. A chain that was read forward as an identification proposal may be re-read backward as a non-adoption record, but this is a transformation of records, not a proof of ordinary inequality.

If no information is lost, $`\mathsf{TComp}`$ is involutive up to record equivalence:

```math
\mathsf{TComp}^2\cong 1.
```

If compression, stabilization, or descent has discarded information, the weaker USD-level comparison

```math
\mathsf{TComp}^2(\mathcal H)\mathrel{\leadsto_{\mathsf{USD}}}\mathcal H
```

may be all that remains.

### U-composition: upward image

D-composition has two common adjoints when the relevant Kan extensions exist. We keep the existential and universal readings separate.

Let $`\rho:\mathcal L\to\mathcal G`$ be a context morphism.

**Existential upward composition.** When the left Kan extension exists, define

```math
\mathsf{UComp}^{\exists}_{\rho}
  \mathrel{:=}
  \Sigma_\rho
  \mathrel{:=}
  \operatorname{Lan}_{\rho}:
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal L,\mathcal C)\to
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal G,\mathcal C).
```

Then

```math
\Sigma_\rho\dashv \rho^*.
```



**Universal upward composition.** When the right Kan extension exists, define

```math
\mathsf{UComp}^{\forall}_{\rho}
  \mathrel{:=}
  \Pi_\rho
  \mathrel{:=}
  \operatorname{Ran}_{\rho}:
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal L,\mathcal C)\to
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal G,\mathcal C).
```

Then

```math
\rho^*\dashv \Pi_\rho.
```



**Smart-lift condition.** These Kan extensions are admitted as U-compositions only when they lift from the pure carrier category to $`\mathsf{Smart}_{\mathsf{USD}}`$. For example, if $`\Sigma_\rho\mathbb H`$ has carrier $`\operatorname{Lan}_\rho F`$, then its faces must be records over that carrier:

```math
q\circ U_{\operatorname{Lan}_\rho F}=(\operatorname{Lan}_\rho F,\underline U),
  \qquad
  q\circ D_{\operatorname{Lan}_\rho F}=(\operatorname{Lan}_\rho F,\underline D),
```

and similarly for $`\Pi_\rho`$ and $`\operatorname{Ran}_\rho F`$. The existence of the ordinary Kan extension of $`F`$ is therefore not enough; the USD record and contract data must lift with it.

If these lifted Kan extensions do not exist, the relevant U-composition is undefined in the smart category even when the carrier Kan extension exists.

The natural-language reading is that a local USD functor is pushed upward as a global candidate record. The existential version says that some local contribution is imaged globally; the universal version says that a local condition is extended as a global constraint when possible.

### C-D-E and S-T-U reading order

The six operations have two useful reading sequences:

```math
\mathsf{CComp}\longrightarrow\mathsf{DComp}\longrightarrow\mathsf{EComp}
```

and

```math
\mathsf{SComp}\longrightarrow\mathsf{TComp}\longrightarrow\mathsf{UComp}.
```

The first sequence compresses free records, lowers them, and subdivides anchored local records. The second stabilizes a shared gap, turns the record chain upside down, and then images the result upward.

## S-molecules and residue-stable sideways composites

The preceding APIs define how USD records may be composed. We now record one derived notion that will be useful in examples: an $`S`$-molecule. The term is intentionally internal to USD theory. It does not mean a chemical molecule unless a separate physical realization or descent license is supplied.

Let $`A`$ and $`B`$ be compatible USD records or USD functors. A U/D interlock between $`A`$ and $`B`$ is boundary-visible data witnessing that the adoptive face of each side can be read against the non-adoptive face of the other side. In notation, this is recorded as

```math
U_A \mathrel{\leadsto_{\mathsf{USD}}}D_B,
  \qquad
  U_B \mathrel{\leadsto_{\mathsf{USD}}}D_A,
```

together with the relevant boundary witnesses and coherence data. The symbol $`\mathrel{\leadsto_{\mathsf{USD}}}`$ is not equality. It records a boundary-visible connection between stance-lifted records over their realized carriers.

Let $`A`$ and $`B`$ be compatible USD records or USD functors. Assume a complete gap lattice

```math
\Lambda_{A,B}
```

and a monotone sideways update map

```math
\Phi_{A,B}:\Lambda_{A,B}\to\Lambda_{A,B}.
```

An $`S`$-molecule between $`A`$ and $`B`$ is a sideways-stabilized record

```math
\operatorname{SMol}(A,B;\Delta^*)
```

consisting of a fixed point

```math
\Delta^*=\Phi_{A,B}(\Delta^*)
```

together with a U/D interlock between $`A`$ and $`B`$, such that the fixed gap $`\Delta^*`$ is preserved by the U-face, D-face, boundary witness, and coherence contract of the resulting sideways composite.

Thus an $`S`$-molecule is not the collapse of $`A`$ and $`B`$ into one identity. It is a USD composite in which two distinguishable sides keep a shared stable discrepancy and become observable as one composite record.

The word “molecule” is used here by analogy with stable composite entities. A physical covalent molecule, a polymer, a software package dependency cluster, or a social institution may be modeled as an $`S`$-molecule only after specifying an interpretation of $`A`$, $`B`$, the gap lattice, the update map, and the relevant boundary witnesses. Without such an interpretation, $`\operatorname{SMol}(A,B;\Delta^*)`$ is only a USD record.

Let $`\star`$ be one of the USD composition APIs, whenever its input data are compatible. A positive-negative exchange datum, or PN-exchange datum, for a composition instance consists of an estimated gain

```math
\widehat G_{\star}
```

and an estimated loss

```math
\widehat L_{\star}.
```

The estimated gain is the portion of the composition adopted by the main output record. The estimated loss is not erased. It is recorded as non-adopted residue attached to the output.

Accordingly, a residue-aware USD composition returns not only a main composite $`\mathbb M_{\star}`$, but also a second USD functor

```math
\mathbb W_{\star}:\mathbb M_{\star}\Rightarrow_{\mathsf{USD}}\mathbb M_{\star},
```

called the self-anchored residue functor. Thus the output shape is

```math
\star(\text{input data})
  =
  \bigl(\mathbb M_{\star},\mathbb W_{\star}\bigr).
```

The residue functor stores the loss, discrepancy, non-adoption, delay, and boundary-visible waste that the main composite does not adopt.

Let

```math
\mathsf{Qty}:\mathsf{Smart}_{\mathsf{USD}}(\mathcal X,\mathcal C)\to\mathcal R
```

be a USD quantity valuation into an ordered commutative monoid $`\mathcal R`$. A PN-exchange datum is conservative when

```math
\mathsf{Qty}(\text{input records})
  =
  \mathsf{Qty}(\mathbb M_{\star})
  +
  \mathsf{Qty}(\mathbb W_{\star}).
```

Thus USD quantity is not destroyed by composition. What is not adopted by the main composite remains as a self-anchored residue functor.

Without the residue functor, a USD composition may look as if the unadopted part of the interaction has disappeared. The PN-exchange policy prevents this. It makes every loss or mismatch accountable either inside the main composite or inside its self-anchored residue. This is consistent with the conservative design of USD theory: unadopted records are not silently converted into USD-free conclusions.

Let

```math
\mathbb M=\operatorname{SMol}(A,B;\Delta^*)
```

be an $`S`$-molecule, and let $`\xi`$ be an external perturbation, force, load, attack, or environmental input applied to $`\mathbb M`$. A UD-spin generated by $`\xi`$ is a finite or eventually stationary internal update sequence

```math
S_0\to S_1\to\cdots\to S_n
```

in which the perturbation circulates between the U-face and D-face of $`\mathbb M`$ before being absorbed, recorded as residue, or ejected through a boundary-visible residue functor.

UD-spin is a USD bookkeeping operation. It is not physical spin unless a separate physical model identifies it with a physical spin-like quantity.

Let $`\omega`$ denote a UD-spin speed for an $`S`$-molecule $`\mathbb M`$. Let

```math
\mathsf{Div}_{\mathbb M}(\omega)
```

be the amount of perturbation that $`\mathbb M`$ can internally dissipate or diverge at spin speed $`\omega`$, and let

```math
\mathsf{Eject}_{\mathbb M}(\omega)
```

be the amount that can be ejected through boundary-visible residue at that speed. If $`\lambda_\xi`$ denotes the incoming perturbation rate, then the basic stability condition is

```math
\lambda_\xi
  \leq
  \mathsf{Div}_{\mathbb M}(\omega)
  +
  \mathsf{Eject}_{\mathbb M}(\omega).
```

When this condition holds and the induced UD-spin terminates, the $`S`$-molecule returns to a state that is observationally equivalent, at the chosen boundary resolution, to the original composite record.

The critical spin speed of an $`S`$-molecule $`\mathbb M`$ is the boundary spin speed at which the incoming perturbation rate begins to exceed the sum of the divergence capacity and ejection capacity:

```math
\lambda_\xi
  >
  \mathsf{Div}_{\mathbb M}(\omega)
  +
  \mathsf{Eject}_{\mathbb M}(\omega).
```

Beyond this boundary, residue accumulates faster than it can be processed. If $`R_t`$ denotes accumulated residue, one may record the update schematically as

```math
R_{t+1}
  =
  R_t
  +
  \lambda_\xi
  -
  \bigl(
    \mathsf{Div}_{\mathbb M}(\omega)
    +
    \mathsf{Eject}_{\mathbb M}(\omega)
  \bigr).
```

When the residue exceeds the tolerance allowed by the coherence contract, the $`S`$-molecule may break, dissociate, reconfigure, or cease to be observable as one composite record.

The internal UD-spin speed of an $`S`$-molecule and the externally observed UD-spin speed need not coincide. We write

```math
\omega^{\mathrm{int}}_{\mathbb M}
```

for the internal spin speed and

```math
\omega^{\mathsf{Obs}}_{\mathbb M}
```

for the boundary-visible observed spin speed. If $`\alpha_{\mathbb M}`$ denotes observational resolution or accuracy, then one may model the observed speed as

```math
\omega^{\mathsf{Obs}}_{\mathbb M}
  =
  \alpha_{\mathbb M}\cdot \omega^{\mathrm{eff}}_{\mathbb M}.
```

For a long serial chain of $`S`$-molecules, observational resolution may decrease as the chain length increases. In such models the observed UD-spin speed is allowed to remain constant or decrease, even if local internal spin speeds do not decrease.

During the formation or perturbation of an $`S`$-molecule, internal non-equivalent exchanges need not be externally observable. Let $`\sigma_A`$ be the time at which an internal accumulation begins in $`A`$, let $`\theta_A`$ be the time at which that accumulation becomes boundary-visible, and let $`\tau_{A\to B}`$ be the time at which the corresponding exchange is implemented toward $`B`$. The non-observable pending wait from $`A`$ to $`B`$ is

```math
T^{\mathrm{NP}}_{A\to B}
  =
  \tau_{A\to B}-\theta_A.
```

Here NP means “non-observable pending” and is unrelated to the complexity class NP.

An $`S`$-polymer is a finite or indexed composite of $`S`$-molecules

```math
\operatorname{SMol}_1
  \mathsf{SComp}
  \operatorname{SMol}_2
  \mathsf{SComp}
  \cdots
  \mathsf{SComp}
  \operatorname{SMol}_n
```

which is externally observable as one higher-order USD entity at a chosen boundary resolution. An $`S`$-polymer may model a physical material, a software dependency cluster, an institution, or another composite system, provided that a suitable realization of the USD records is supplied.

A covalent bond may be used as an intuitive model of an $`S`$-molecule: two atoms remain distinguishable while forming a stable shared state through electron-density-mediated interaction. This comparison is only a model reading. USD theory does not redefine covalent bonding, molecular physics, software dependency, or any other base-domain concept. To obtain a USD-free physical conclusion, the relevant descent license must still be supplied in the base theory.

## A syntactic reference implementation

This section records the minimum syntax needed for a conservative USD calculus. It is intentionally austere.

Let $`\mathcal L_0`$ be a base formal language with judgments

```math
\Gamma\vdash_0 A.
```

The base language may be first-order logic, type theory, an internal language of a category, or another fixed formal system.

The USD calculus $`\mathsf{USDCalc}`$ extends $`\mathcal L_0`$ with record terms:

```math
\mathrm{conn}(x,y;r,\beta),
  \qquad
  \mathrm{nonadopt}(x,y;r,\beta),
  \qquad
  \mathrm{hand}(F,U,D,\partial,\kappa),
```

and with record-forming operations

```math
\mathsf{CComp},
  \mathsf{DComp},
  \mathsf{EComp},
  \mathsf{SComp},
  \mathsf{TComp},
  \mathsf{UComp}.
```

The USD extension does not add a base rule allowing a record term alone to prove a USD-free formula.

A descent license is an explicit rule instance

```math
\mathsf{IdLic}(R,A)
```

that permits a USD record $`R`$ to be translated into a base assertion $`A`$ in $`\mathcal L_0`$. Examples include a definition, an isomorphism, a proved equivalence, a semantic interpretation, or a verified coercion.

The erasure translation

```math
|-|:\mathsf{USDCalc}\to\mathcal L_0
```

acts as identity on base terms and formulas and removes pure USD records unless a descent license supplies a base formula.

Assume that every USD inference rule is record-forming, record-transforming, or explicitly licensed by a descent rule. If

```math
\Gamma\vdash_{\mathsf{USDCalc}} A
```

and $`A`$ is USD-free, then the derivation of $`A`$ uses only base rules and licensed descents. Consequently

```math
|\Gamma|\vdash_0 A
```

provided each used descent license is valid in the base system.

By induction on the given derivation. Base rules translate to base rules. Record-forming and record-transforming USD rules have USD-record conclusions and therefore cannot be the final step of a USD-free formula. If a USD record is used to produce a USD-free conclusion, the rule must be a licensed descent by hypothesis; replacing that step with its base license yields a derivation in $`\mathcal L_0`$. The induction removes all unlicensed USD bookkeeping from the derivation of $`A`$.

This theorem is deliberately conditional. It states the safety contract of the reference implementation. A stronger metatheorem for a particular formal calculus would require a fully specified proof system, but this condition is already enough to prevent USD records from acting as hidden proof rules.

## Worked toy model

Let $`\mathcal C`$ be a poset regarded as a category. Let

```math
\mathsf{Rel}_{\mathcal C}(a,b)
```

be the truth value of $`a\leq b`$. Let $`\mathsf{BVis}`$ select those comparable pairs for which a chosen boundary label is present. Let $`\mathsf{Rec}_{\mathsf{USD}}`$ be the product category

```math
\mathcal C\times\mathsf{St}
```

with projection to $`\mathsf{St}`$. The realization projection is

```math
r=\operatorname{pr}_{\mathcal C}:\mathcal C\times\mathsf{St}\to\mathcal C,
```

so the combined projection is

```math
q=(r,\pi):\mathcal C\times\mathsf{St}\to\mathcal C\times\mathsf{St},
```

the identity in this minimal model. Then $`\mathcal U\cong\mathcal C\cong\mathcal D`$, but the two copies are distinguished as fibers. A USD functor is a functor $`F`$ together with two stance-lifted copies $`U_F,D_F`$ over the same $`F`$ and a boundary label. In this model D-composition is ordinary reindexing of monotone maps, C-composition is pushout of indexing posets when it exists, and T-composition swaps the two copies and reverses a finite chain while preserving realization.

Let the gap lattice be a complete lattice $`\Lambda`$. If a sideways interaction gives a monotone map $`\Phi:\Lambda\to\Lambda`$, then the set of fixed points is nonempty by the Knaster-Tarski theorem. Choosing the least fixed point gives a canonical minimal shared discrepancy. Choosing the greatest fixed point gives a maximal conservative discrepancy. The choice is part of the model policy.

## Relativistic test model

The relativistic material is not an application claiming new physics. It is a test model for the USD vocabulary because relativity naturally involves observers, frames, local restrictions, and time-oriented records. The historical sources are Einstein’s 1905 paper on special relativity and his 1916 paper on general relativity .

Let $`(M,g)`$ be a Lorentzian manifold. Let $`\mathcal O(M,g)`$ be a chosen category of local observers or frames. A morphism in $`\mathcal O(M,g)`$ may be a change of frame, inclusion of a local chart, or another chosen admissible comparison of observations.

A global geometric record, such as a metric-dependent record on $`(M,g)`$, may be lowered along a local frame map

```math
\rho:O\to M
```

by pullback:

```math
\mathsf{DComp}_{\rho}(\mathbb H)=\rho^*\mathbb H.
```

This is the familiar mathematical shape of restricting global data to a local observer or frame. The USD interpretation only adds adoptive and non-adoptive record faces and boundary witnesses.

A time-oriented chain of observation records may be transformed by $`\mathsf{TComp}`$ into the reverse-order chain with U and D faces exchanged. This is not asserted to be physical time reversal symmetry. It is a record operation that leaves the entities and geometric carrier untouched while turning the USD bookkeeping upside down.

If a model uses Lorentz transformations, connections, curvature, or field equations, those structures must be explicitly included in the base category or in the relation witness profunctor. USD functors do not supply them automatically.

## Reviewer-facing checklist

For reference, the implementation satisfies the following design checks.

1.  The context parameter is a category $`\mathcal P`$, not a bare set.

2.  Situated occurrences are defined by a Grothendieck construction.

3.  $`\mathsf{Rel}`$ is a poset-valued profunctor or indexed predicate.

4.  $`\mathsf{BVis}`$ is a typed substructure of $`\mathsf{Rel}`$.

5.  $`\mathcal U`$ and $`\mathcal D`$ are fibers of one fibration $`\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{St}`$, and every record is also realized by $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$.

6.  The combined projection $`q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}`$ makes U- and D-faces stance-lifts over one carrier.

7.  A USD functor is a tuple $`(F,U_F,D_F,\partial_F,\kappa_F)`$ where $`U_F`$ and $`D_F`$ satisfy $`q\circ U_F=(F,\underline U)`$ and $`q\circ D_F=(F,\underline D)`$.

8.  The coherence contract $`\kappa_F`$ is an explicit bundle of lift, boundary, morphism, composition, erasure, and descent obligations.

9.  C/D/E/S/T/U operations have stated input types, outputs, and existence conditions.

10. S-composition depends on a complete lattice and a monotone update map, so fixed-point existence is not merely asserted.

11. T-composition is sequence reversal plus a carrier-preserving U/D involution and does not touch entities or carrier realization.

12. USD-free conclusions require base reasoning or an explicit descent license.

## Open problems

The present draft is a reference implementation rather than a final metatheory. The main open problems are:

1.  Refine preferred subclasses of coherence contracts $`\kappa_F`$ and prove closure under all six composition APIs in nontrivial models.

2.  Compare the carrier-realized USD record fibration with displayed categories, double categories, fibrations of proofs, and decorated functors.

3.  Give a fully formal sequent calculus or type theory for $`\mathsf{USDCalc}`$ and prove a cut-elimination or model-theoretic conservativity theorem.

4.  Identify useful model policies for selecting fixed points in S-composition.

5.  Develop lax stance-lift variants where $`q\circ U_F`$ and $`q\circ D_F`$ compare to $`(F,\underline U)`$ and $`(F,\underline D)`$ rather than strictly equal them.

6.  Develop nontrivial test models beyond the poset and relativistic sketches.

## Conclusion

The central correction in this draft is that USD Functor Theory should be read as a specification of smart functors, not as a metaphorical use of category theory. A USD functor is an ordinary functor with additional record fields: adoptive face, non-adoptive face, boundary witness, and coherence contract. The U and D regions are fibers of one stance-indexed record fibration, and the faces are stance-lifts realized over the same carrier by

```math
q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}.
```

The six composition operations are typed APIs backed by ordinary categorical constructions or explicit existence assumptions, and each operation is defined only when it preserves the stance-lift invariant through $`q`$. The resulting system can guide interpretation and proof search while remaining conservative over the base language for USD-free conclusions.

<span>9</span>

Saunders Mac Lane. *Categories for the Working Mathematician*. Springer, 1971.

Francis Borceux. *Handbook of Categorical Algebra, Volumes 1–3*. Cambridge University Press, 1994.

Peter T. Johnstone. *Sketches of an Elephant: A Topos Theory Compendium*. Oxford University Press, 2002.

Alexander Grothendieck. Revêtements ètales et groupe fondamental. In *SGA 1*, Lecture Notes in Mathematics 224, Springer, 1971.

Alfred Tarski. A lattice-theoretical fixpoint theorem and its applications. *Pacific Journal of Mathematics*, 5(2):285–309, 1955.

Albert Einstein. Zur Elektrodynamik bewegter Körper. *Annalen der Physik*, 322(10):891–921, 1905.

Albert Einstein. Die Grundlage der allgemeinen Relativitätstheorie. *Annalen der Physik*, 354(7):769–822, 1916.
