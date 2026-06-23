# The Up-Side-Down Functor: A Reference Implementation of Smart Functors with Boundary-Visible Stance

**Author:** Shuhei Ihara

**Date:** June 23, 2026

## Abstract

The Up-Side-Down functor is not a new equality, a new physical law, or a new proof principle. It is a structured functor: a pure functor equipped with an adoptive face, a non-adoptive face, a boundary witness, and a coherence contract. The purpose of this paper is to give a reference implementation of such structured functors and of their safe composition operations. The construction treats the adoptive and non-adoptive regions not as two arbitrary pre-existing categories, but as fibers of a single USD record fibration realized over both a carrier category and a two-sided stance category. In this sense a USD functor is a categorical analogue of a smart pointer: after forgetting the additional fields it is an ordinary functor, while before forgetting it carries explicit bookkeeping for observation, non-adoption, boundary visibility, and typed composition. Six causeton types are specified: compression, downward restriction, extension, sideways stabilization, temporal turnover, and upward image. Each causeton is presented as a composition–decomposition pair with type conditions, existence conditions, residue accounting, and philosophical reading. The conservative intent is made explicit: USD records may organize proof search or interpretation, but USD-free conclusions must be justified in the base theory.

## Contents

- [Scope and non-claims](#scope-and-non-claims)
- [Base data](#base-data)
- [The USD record fibration](#the-usd-record-fibration)
- [USD functors as smart functors](#usd-functors-as-smart-functors)
- [Morphisms and the category of USD functors](#morphisms-and-the-category-of-usd-functors)
- [S-molecules and residue-stable sideways composites](#s-molecules-and-residue-stable-sideways-composites)
- [Causetons: six composition–decomposition pairs](#causetons-six-compositiondecomposition-pairs)
  - [Causeton coverage and saturation](#causeton-coverage-and-saturation)
- [Sensitons: art-anchored perceptual connectors](#sensitons-art-anchored-perceptual-connectors)
- [USD fusion and USD fission](#usd-fusion-and-usd-fission)
- [A syntactic reference implementation](#a-syntactic-reference-implementation)
- [Worked toy model](#worked-toy-model)
- [Relativistic test model](#relativistic-test-model)
  - [Newton-Einstein test](#newton-einstein-test)
- [Interdisciplinary test model](#interdisciplinary-test-model)
  - [Satoshi test](#satoshi-test)
  - [Oppenheimer test](#oppenheimer-test)
- [Reviewer-facing checklist](#reviewer-facing-checklist)
- [Open problems](#open-problems)
- [Conclusion](#conclusion)

## Scope and non-claims

This draft responds to a common failure mode in early USD notation: terms such as relation, boundary, observation, adoption, refusal, gap, and turn can sound like explanatory prose rather than mathematical data. The present version therefore treats USD theory as a typed reference implementation. The reader should not be asked to infer the missing interfaces. They are made explicit.

<div class="remark">

**Remark 1** (What this paper does not claim). This paper does not claim that USD notation proves a new equality, a new inequality, a physical theorem, or a computational separation. It does not identify boundary-visible connection with equality. It does not identify non-adoption with ordinary negation. It does not claim that the relativistic discussion below proves anything about special or general relativity. The relativistic section is a test model for the vocabulary of observers, frames, local restrictions, and temporal records.

</div>

<div class="remark">

**Remark 2** (What this paper does claim). This paper claims that one can specify a category of smart functors whose objects are ordinary functors equipped with additional USD structure, and that the main USD composition operations can be given as typed operations using standard categorical vocabulary: pushouts or gluing for compression, pullback or reindexing for downward composition, factorization for extension, fixed points for sideways stabilization, involution plus sequence reversal for temporal turnover, and Kan-style images for upward composition.

</div>

The intended comparison is with a smart pointer in programming. A raw pointer stores an address. A smart pointer stores an address together with ownership, lifetime, and release discipline. Likewise, a raw functor stores functorial action. A USD functor stores functorial action together with an adoptive face and a non-adoptive face that are stance-lifts of the same carrier, together with a boundary witness and a coherence contract. Forgetting these fields returns the raw functor. Keeping them enables safe composition of records without silently turning records into proof steps.

## Base data

This section fixes the data that later sections use. The goal is to avoid introducing objects such as $`\mathsf{Rel}`$, $`\mathsf{BVis}`$, $`\mathsf{Obs}`$, or $`\mathsf{NonAdopt}`$ as undefined prose.

<div class="assumption">

**Assumption 3** (Context category). Let $`\mathcal P`$ be a small category. Its objects are positions, contexts, observers, stages, regions, or local situations. A morphism $`\phi:p\to q`$ is an admissible transition of context. In concrete models $`\mathcal P`$ may be a poset, a site, or a category of local charts.

</div>

<div class="assumption">

**Assumption 4** (Indexed entity category). Let

```math
E:\mathcal P^{\mathrm{op}}\to \mathbf{Cat}
```

be an indexed category. For each context $`p`$ the category $`E(p)`$ contains the entities, expressions, records, or local objects available at $`p`$. For each transition $`\phi:p\to q`$, the reindexing functor $`E(\phi):E(q)\to E(p)`$ gives the local view of a $`q`$-object at $`p`$.

</div>

<div class="construction">

**Construction 5** (Situated occurrence category). The category of situated occurrences is the Grothendieck construction

```math
\mathsf{Occ}(E)\mathrel{:=}\int_{\mathcal P}E.
```

An object is a pair $`(p,x)`$ with $`x\in E(p)`$. A morphism $`(p,x)\to(q,y)`$ is a pair $`(\phi,\alpha)`$ where $`\phi:p\to q`$ in $`\mathcal P`$ and

```math
\alpha:x\to E(\phi)(y)
```

in $`E(p)`$. Composition is the usual composition in the Grothendieck construction.

</div>

This definition repairs the ambiguity that appears when a set of positions is used while morphisms $`p\to q`$ are also required. From this point on, context transitions are morphisms in $`\mathcal P`$.

<div class="assumption">

**Assumption 6** (Relation witness profunctor). Let $`\mathcal C`$ be a category. A relation witness structure on $`\mathcal C`$ is a profunctor valued in posets,

```math
\mathsf{Rel}_{\mathcal C}:\mathcal C^{\mathrm{op}}\times\mathcal C\to \mathbf{Pos}.
```

An element $`r\in \mathsf{Rel}_{\mathcal C}(a,b)`$ is a witness that $`a`$ and $`b`$ are related in the specified sense. Functoriality gives transport of relation witnesses along morphisms of $`\mathcal C`$.

</div>

<div class="assumption">

**Assumption 7** (Boundary visibility). Boundary visibility is a substructure of relation witnesses. We write

```math
\mathsf{BVis}_{\mathcal C}\hookrightarrow \mathsf{Rel}_{\mathcal C}
```

for a subfunctor or indexed subposet. A boundary witness over $`r\in\mathsf{Rel}_{\mathcal C}(a,b)`$ is denoted

```math
\beta\in \mathsf{BVis}_{\mathcal C}(r).
```

Thus $`\mathsf{BVis}`$ is not a metaphor; it is a typed predicate over relation witnesses.

</div>

<div class="remark">

**Remark 8** (Minimality of the base). Nothing in the formal development requires $`\mathsf{Rel}`$ to be equality, isomorphism, equivalence, metric proximity, causal accessibility, or logical entailment. Those are model choices. The USD reference implementation only assumes relation witnesses and boundary witnesses.

</div>

## The USD record fibration

The adoptive and non-adoptive sides are not introduced as two unrelated categories. They arise as fibers of a single record fibration.

<div class="definition">

**Definition 9** (Stance category). The stance category $`\mathsf{St}`$ has two distinguished objects

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

</div>

<div class="definition">

**Definition 10** (USD record fibration). A USD record fibration is a functor

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

</div>

<div class="definition">

**Definition 11** (Carrier-realized USD record fibration). Fix a carrier category $`\mathcal C`$. A carrier-realized USD record fibration over $`\mathcal C`$ is a USD record fibration together with a realization functor

```math
r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C
```

and hence a combined projection

```math
q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}.
```

We require

```math
\mathrm{pr}_{\mathsf{St}}\circ q=\pi,
  \qquad
  \mathrm{pr}_{\mathcal C}\circ q=r.
```

Thus every USD record has both a stance and a realized carrier. For $`c\in\mathcal C`$ and $`s\in\mathsf{St}`$, the notation

```math
(\mathsf{Rec}_{\mathsf{USD}})_{(c,s)}\mathrel{:=}q^{-1}(c,s)
```

denotes the category of stance-$`s`$ records realizing the carrier datum $`c`$. The notation suppresses the dependence of $`\mathsf{Rec}_{\mathsf{USD}}`$ on $`\mathcal C`$ when no confusion is possible.

</div>

<div class="remark">

**Remark 12** (Why realization is required). The projection $`\pi:\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{St}`$ separates adoptive from non-adoptive records, but by itself it does not say which ordinary carrier object a record is about. The realization functor $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$ fills this gap. It prevents the pure carrier, the adoptive face, and the non-adoptive face of a USD functor from becoming three unrelated functors.

</div>

<div class="definition">

**Definition 13** (Record constructors). The record category contains typed constructors

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
  \mathsf{Collapse}&: \mathsf{Rel}_{\mathcal C}(a,b)\to \mathsf{Rec}_{\mathsf{USD}}.
\end{aligned}
```

These constructors are part of the syntax of records. A model may interpret them as evidence, annotations, proof-search traces, logs, or semantic states. The realization functor $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$ records which carrier datum such a constructed record is about; two records may have different stances while realizing the same carrier.

</div>

<div class="definition">

**Definition 14** (Directed stance notation). Given $`x,y`$ in a common context, the notation

```math
x\mathrel{\leadsto_{\mathsf{USD}}}y
```

means that a boundary-visible connection record from $`x`$ to $`y`$ has been constructed. The notation

```math
x\mathrel{\dashrightarrow_{\mathsf{USD}}}y
```

means that a proposed connection from $`x`$ to $`y`$ has been observed but is recorded on the non-adoptive side. Neither notation is equality or ordinary inequality.

</div>

## USD functors as smart functors

We now define the main object. The definition is deliberately close to a reference implementation: a USD functor is a record with fields.

<div class="definition">

**Definition 15** (Pure carrier). Let $`\mathcal X`$ and $`\mathcal C`$ be categories. A pure carrier is an ordinary functor

```math
F:\mathcal X\to\mathcal C.
```

It is the raw functor that remains after forgetting all USD metadata.

</div>

<div class="definition">

**Definition 16** (Stance-lifts of a carrier). Let $`q=(r,\pi):\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C\times\mathsf{St}`$ be a carrier-realized USD record fibration and let $`F:\mathcal X\to\mathcal C`$ be a pure carrier. Write

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

</div>

<div class="definition">

**Definition 17** (USD functor). A USD functor from $`\mathcal X`$ to $`\mathcal C`$ is a tuple

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

</div>

<div class="definition">

**Definition 18** (Coherence contract). For a USD functor $`\mathbb H=(F,U_F,D_F,\partial_F,\kappa_F)`$, the coherence contract is a tuple of obligations

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

</div>

<div class="definition">

**Definition 19** (Forgetful functor). There is a forgetful functor

```math
|-|:\mathsf{Smart}_{\mathsf{USD}}(\mathcal X,\mathcal C)\to [\mathcal X,\mathcal C]
```

which sends

```math
(F,U_F,D_F,\partial_F,\kappa_F)\mapsto F.
```

This is the categorical version of dereferencing the smart functor to its pure carrier.

</div>

<div class="remark">

**Remark 20** (Why this is not merely gluing two categories). The data $`\mathcal U`$ and $`\mathcal D`$ are not assumed independently and then attached to $`F`$. They are stance fibers of the single record fibration $`\pi:\mathsf{Rec}_{\mathsf{USD}}\to\mathsf{St}`$, and the same records are realized in the carrier category by $`r:\mathsf{Rec}_{\mathsf{USD}}\to\mathcal C`$. Consequently the adoptive and non-adoptive faces of a USD functor are stance-lifts over the same pure carrier:

```math
q\circ U_F=(F,\underline U),
  \qquad
  q\circ D_F=(F,\underline D).
```

The boundary witness $`\partial_F`$ and coherence contract $`\kappa_F`$ therefore relate two readings of one carrier, not two unrelated functors.

</div>

<div class="definition">

**Definition 21** (Free and anchored USD functors). A free USD functor is a USD functor considered before anchoring it to particular entities. An anchored USD functor is a free USD functor equipped with endpoints or a local occurrence context. We write

```math
\mathsf{Anch}_{a,b}(\mathbb H)=\mathbb H_{a,b}:a\Rightarrow_{\mathsf{USD}}b
```

for anchoring $`\mathbb H`$ between $`a`$ and $`b`$ when the required endpoint and boundary data exist.

</div>

The distinction is essential. Functions, expressions, programs, formulas, and hypotheses may be free USD functors before they touch any particular pair of entities. Entity-to-entity contact is an anchoring of an already typed USD functor.

## Morphisms and the category of USD functors

<div class="definition">

**Definition 22** (Morphism of USD functors). Let

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

</div>

<div class="proposition">

**Proposition 23** (Category of USD functors). *For fixed $`\mathcal X`$ and $`\mathcal C`$, USD functors and their morphisms form a category, denoted

```math
\mathsf{Smart}_{\mathsf{USD}}(\mathcal X,\mathcal C),
```

provided the total record category admits vertical composition of $`q`$-compatible natural transformations and the coherence contracts are closed under identity and composition.*

</div>

<div class="proof">

*Proof.* Identities are inherited componentwise from the functor category and the record category. Composition is componentwise and remains compatible with $`q`$ because carrier and stance components compose in $`\mathcal C\times\mathsf{St}`$. The boundary compatibility and contract preservation conditions are stable by the assumed closure of contracts. The forgetful projection to $`[\mathcal X,\mathcal C]`$ is functorial by construction. ◻

</div>

This proposition is intentionally modest. It is not advertised as a deep category-theoretic theorem. It is the sanity check that the reference implementation has the shape of a category.

## S-molecules and residue-stable sideways composites

Before defining the six causeton types, we isolate one record shape that will be used repeatedly in examples: an $`S`$-molecule. This section does not define one of the six causetons and does not state a new proof rule. It fixes the local data needed to speak about two USD records that remain distinguishable while sharing a stable boundary-visible discrepancy. The term is internal to USD theory; it does not mean a chemical molecule unless a separate physical realization or descent license is supplied.

<div class="definition">

**Definition 24** (S-compatibility). Let $`A`$ and $`B`$ be USD records or USD functors. They are S-compatible when the following data are available:

1.  their realized carriers lie in a common carrier category, or have first been brought to a common comparison context;

2.  the relevant relation witnesses and boundary-visibility predicates are defined for cross-face comparisons between $`A`$ and $`B`$;

3.  their coherence contracts permit a shared boundary record and a residue record without detaching either U-face or D-face from its realized carrier.

S-compatibility is only a typing condition. It does not identify $`A`$ with $`B`$, and it does not imply that their gap is zero.

</div>

<div class="definition">

**Definition 25** (U/D interlock). Let $`A`$ and $`B`$ be S-compatible USD records or USD functors. A U/D interlock between $`A`$ and $`B`$ is boundary-visible data witnessing that the adoptive face of each side can be read against the non-adoptive face of the other side. In notation, this is recorded as

```math
U_A \mathrel{\leadsto_{\mathsf{USD}}}D_B,
  \qquad
  U_B \mathrel{\leadsto_{\mathsf{USD}}}D_A,
```

together with the relevant boundary witnesses and coherence data. The symbol $`\mathrel{\leadsto_{\mathsf{USD}}}`$ is not equality. It records a boundary-visible connection between stance-lifted records over their realized carriers.

</div>

<div class="definition">

**Definition 26** (Sideways gap datum). For S-compatible $`A`$ and $`B`$, a sideways gap datum consists of a complete lattice

```math
\Lambda_{A,B}
```

of possible gap values, a monotone update map

```math
\Phi_{A,B}:\Lambda_{A,B}\to\Lambda_{A,B},
```

and a selected fixed point

```math
\Delta^*=\Phi_{A,B}(\Delta^*).
```

The order on $`\Lambda_{A,B}`$ is chosen by the model; it may mean “no more discrepant than”, “no less resolved than”, or another typed refinement order. The selected fixed point is part of the datum unless it is supplied by an independent fixed-point theorem. Without such a point there is no stabilized $`S`$-molecule.

</div>

<div class="definition">

**Definition 27** (S-molecule). Let $`A`$ and $`B`$ be S-compatible USD records or USD functors equipped with a sideways gap datum. An $`S`$-molecule between $`A`$ and $`B`$ is a sideways-stabilized USD record

```math
\mathrm{SMol}(A,B;\Delta^*)
```

consisting of the fixed gap $`\Delta^*`$, a U/D interlock between $`A`$ and $`B`$, and coherence data asserting that $`\Delta^*`$ is preserved by the U-face, D-face, and boundary witness of the composite. Material not adopted by this main observable record is stored in the residue ledger defined next.

Thus an $`S`$-molecule is not the collapse of $`A`$ and $`B`$ into one identity. It is a USD composite in which two distinguishable sides keep a shared stable discrepancy and become observable as one composite record.

</div>

<div class="definition">

**Definition 28** (S-molecular residue ledger). Let

```math
\mathbb M=\mathrm{SMol}(A,B;\Delta^*)
```

be an $`S`$-molecule. A residue ledger for $`\mathbb M`$ is a self-anchored USD functor

```math
\mathbb W_{\mathbb M}:\mathbb M\Rightarrow_{\mathsf{USD}}\mathbb M
```

that records the loss, mismatch, delay, non-adoption, and boundary-visible waste not adopted by the main observable composite. The ledger is self-anchored because the residue is about the stabilized composite itself, not a separate USD-free conclusion.

</div>

<div class="definition">

**Definition 29** (S-molecular residue accounting). Let

```math
\mathsf{Qty}:\{A,B,\mathbb M,\mathbb W_{\mathbb M}\}\to\mathcal R
```

be a USD quantity valuation into an ordered commutative monoid, defined for the records under discussion. A residue ledger for $`\mathbb M=\mathrm{SMol}(A,B;\Delta^*)`$ is conservative when

```math
\mathsf{Qty}(A)+\mathsf{Qty}(B)
  =
  \mathsf{Qty}(\mathbb M)
  +
  \mathsf{Qty}(\mathbb W_{\mathbb M}).
```

This equation is a bookkeeping policy inside the USD model. It does not turn the unadopted residue into a base-language assertion.

</div>

<div class="remark">

**Remark 30** (Meaning of molecule). The word “molecule” is used here by analogy with stable composite entities. A physical covalent molecule, a polymer, a software package dependency cluster, or a social institution may be modeled as an $`S`$-molecule only after specifying an interpretation of $`A`$, $`B`$, the gap lattice, the update map, the residue ledger, and the relevant boundary witnesses. Without such an interpretation, $`\mathrm{SMol}(A,B;\Delta^*)`$ is only a USD record.

</div>

<div class="remark">

**Remark 31** (Why residue is part of the molecule). Without the residue ledger, the stabilized composite may look as if the unadopted part of the interaction has disappeared. The ledger prevents that reading. Every loss or mismatch must remain accountable either inside the main observable composite or inside $`\mathbb W_{\mathbb M}`$. This is consistent with the conservative design of USD theory: unadopted records are not silently converted into USD-free conclusions.

</div>

<div class="definition">

**Definition 32** (UD-spin). Let

```math
\mathbb M=\mathrm{SMol}(A,B;\Delta^*)
```

be an $`S`$-molecule, and let $`\xi`$ be an external perturbation, force, load, attack, or environmental input applied to $`\mathbb M`$. A UD-spin generated by $`\xi`$ is a finite or eventually stationary internal update sequence

```math
S_0\to S_1\to\cdots\to S_n
```

in which the perturbation circulates between the U-face and D-face of $`\mathbb M`$ before being absorbed, recorded in $`\mathbb W_{\mathbb M}`$, or ejected through boundary-visible residue.

UD-spin is a USD bookkeeping operation. It is not physical spin unless a separate physical model identifies it with a physical spin-like quantity.

</div>

<div class="definition">

**Definition 33** (Divergence, ejection, and spin termination). Let $`\omega`$ denote a UD-spin speed for an $`S`$-molecule $`\mathbb M`$. Let

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

</div>

<div class="definition">

**Definition 34** (Critical spin speed). The critical spin speed of an $`S`$-molecule $`\mathbb M`$ is the boundary spin speed at which the incoming perturbation rate begins to exceed the sum of the divergence capacity and ejection capacity:

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

</div>

<div class="definition">

**Definition 35** (Observed UD-spin speed). The internal UD-spin speed of an $`S`$-molecule and the externally observed UD-spin speed need not coincide. We write

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

</div>

<div class="definition">

**Definition 36** (Non-observable pending wait). During the formation or perturbation of an $`S`$-molecule, internal non-equivalent exchanges need not be externally observable. Let $`\sigma_A`$ be the time at which an internal accumulation begins in $`A`$, let $`\theta_A`$ be the time at which that accumulation becomes boundary-visible, and let $`\tau_{A\to B}`$ be the time at which the corresponding exchange is implemented toward $`B`$. The non-observable pending wait from $`A`$ to $`B`$ is

```math
T^{\mathrm{NP}}_{A\to B}
  =
  \tau_{A\to B}-\theta_A.
```

Here NP means “non-observable pending” and is unrelated to the complexity class NP.

</div>

<div class="definition">

**Definition 37** (S-polymer). An $`S`$-polymer is a finite or indexed serial joining of $`S`$-molecules

```math
\mathrm{SMol}_1
  \mathbin{\otimes_S}
  \mathrm{SMol}_2
  \mathbin{\otimes_S}
  \cdots
  \mathbin{\otimes_S}
  \mathrm{SMol}_n
```

which is externally observable as one higher-order USD entity at a chosen boundary resolution. Each adjacent joining must supply its own S-compatibility data, sideways gap datum, interlock, and residue ledger. An $`S`$-polymer may model a physical material, a software dependency cluster, an institution, or another composite system, provided that a suitable realization of the USD records is supplied.

</div>

<div class="remark">

**Remark 38** (S-molecules and physical examples). A covalent bond may be used as an intuitive model of an $`S`$-molecule: two atoms remain distinguishable while forming a stable shared state through electron-density-mediated interaction. This comparison is only a model reading. USD theory does not redefine covalent bonding, molecular physics, software dependency, or any other base-domain concept. To obtain a USD-free physical conclusion, the relevant descent license must still be supplied in the base theory.

</div>

## Causetons: six composition–decomposition pairs

The six basic USD operations are now treated as causetons. A causeton is not merely a composition step. It is a typed record of a composition operation together with the decomposition phenomenon emitted by that operation, the self-anchored residue ledger that stores what is not adopted by the main output, and the coherence contract that prevents the record from becoming an unlicensed proof rule.

<div class="definition">

**Definition 39** (Causeton). For

```math
\star\in\{C,D,E,S,T,U\},
```

a $`\star`$-causeton is a typed USD causal record

```math
\mathfrak c_\star
  =
  (\mathsf{Comp}_\star,\mathsf{Dec}_\star,\mathbb W_\star,\kappa_\star).
```

Here $`\mathsf{Comp}_\star`$ is the $`\star`$-typed composition operation, $`\mathsf{Dec}_\star`$ is the decomposition phenomenon emitted by that operation, $`\mathbb W_\star`$ is a self-anchored residue USD functor recording the unadopted byproduct, and $`\kappa_\star`$ is the coherence contract for the causeton.

</div>

<div class="remark">

**Remark 40** (Causetons are USD records). A causeton is not asserted to be a physical particle, a new causal law, or a base-language explanation. It is a USD record unit. A physical, historical, legal, or psychological reading requires the relevant carrier, relation witnesses, boundary witnesses, and descent licenses.

</div>

<div class="assumption">

**Assumption 41** (Common closure invariant for causetons). Every causeton below is required to preserve carrier-realized stance-lifts. If the main output has carrier

```math
F':\mathcal X'\to\mathcal C,
```

then its output faces must satisfy

```math
q\circ U_{F'}=(F',\underline U),
  \qquad
  q\circ D_{F'}=(F',\underline D).
```

This is the operational content of $`\kappa^{\mathrm{comp}}`$: composition may change the carrier, boundary, or indexing shape, and decomposition may emit residue, but neither side may detach U-face or D-face records from their carrier realization.

</div>

<div class="definition">

**Definition 42** (C-causeton: compression and interface decomposition). The C-causeton

```math
\mathfrak c_C
  =
  (\mathsf{Comp}_C,\mathsf{Dec}_C,\mathbb W_C,\kappa_C)
```

has the following data.

**Composition operation.** The input consists of two free USD functors

```math
\mathbb H:\mathcal X\to\mathcal C,
  \qquad
  \mathbb K:\mathcal Y\to\mathcal C,
```

together with an interface span

```math
\mathcal X\overset{i}{\leftarrow}\mathcal I\overset{j}{\rightarrow}\mathcal Y
```

and interface compatibility data between $`i^*\mathbb H`$ and $`j^*\mathbb K`$. When the pushout

```math
\mathcal X\sqcup_{\mathcal I}\mathcal Y
```

exists in $`\mathbf{Cat}`$, and the carrier and record data glue along the interface in a way compatible with $`q`$, the composition operation is

```math
\mathsf{Comp}_C(\mathbb H,\mathbb K)
  =
  \mathsf{CComp}_{\mathcal I}(\mathbb H,\mathbb K):
  \mathcal X\sqcup_{\mathcal I}\mathcal Y\to\mathcal C.
```



**Decomposition phenomenon.** Compression emits the decomposition of the interface. The old boundary data do not disappear; the interface discrepancy becomes separable as residue. A minimal boundary policy is

```math
\partial_{\mathsf{CComp}(\mathbb H,\mathbb K)}
  =
  \partial_{\mathbb H}\oplus
  \partial_{\mathbb K}\oplus
  \Delta_{\mathcal I}(\mathbb H,\mathbb K),
```

where $`\Delta_{\mathcal I}`$ is supplied by the model.

**Residue ledger.** The self-anchored ledger

```math
\mathbb W_C:
  \mathsf{CComp}_{\mathcal I}(\mathbb H,\mathbb K)
  \Rightarrow_{\mathsf{USD}}
  \mathsf{CComp}_{\mathcal I}(\mathbb H,\mathbb K)
```

records the projection loss, interface discrepancy, and non-adopted boundary material emitted by the compression.

</div>

<div class="definition">

**Definition 43** (D-causeton: restriction and background decomposition). The D-causeton

```math
\mathfrak c_D
  =
  (\mathsf{Comp}_D,\mathsf{Dec}_D,\mathbb W_D,\kappa_D)
```

has the following data.

**Composition operation.** The input is a context morphism

```math
\rho:\mathcal L\to\mathcal G
```

and a USD functor over the global context $`\mathcal G`$. The composition operation is reindexing or pullback:

```math
\mathsf{Comp}_D(\rho,\mathbb H)
  =
  \mathsf{DComp}_{\rho}(\mathbb H)
  =
  \rho^*\mathbb H:
  \mathcal L\to\mathcal C.
```

If $`\mathbb H`$ has carrier $`F`$, then the output has carrier $`\rho^*F`$, and its faces are the reindexed stance-lifts satisfying

```math
q(\rho^*U_F)=(\rho^*F,\underline U),
  \qquad
  q(\rho^*D_F)=(\rho^*F,\underline D).
```



**Decomposition phenomenon.** Downward restriction decomposes the global record into the local reading and the background material that the local context no longer displays. The local output is not a proof that the global claim holds locally; it is the typed reading of the global record through the chosen index.

**Residue ledger.** The self-anchored ledger

```math
\mathbb W_D:
  \rho^*\mathbb H\Rightarrow_{\mathsf{USD}}\rho^*\mathbb H
```

records the forgotten global constraints, boundary conditions, and nonlocal residue left outside the local restriction.

</div>

<div class="definition">

**Definition 44** (E-causeton: cut extension and path decomposition). The E-causeton

```math
\mathfrak c_E
  =
  (\mathsf{Comp}_E,\mathsf{Dec}_E,\mathbb W_E,\kappa_E)
```

has the following data.

**Composition operation.** The input is an anchored USD functor

```math
\mathbb H_{a,b}:a\Rightarrow_{\mathsf{USD}}b
```

and a proposed cut vertex $`m`$. When there is factorization data in the relevant arrow category, together with a comparison 2-cell

```math
\varepsilon_m:
  \mathbb H_{a,m}\circ \mathbb H_{m,b}
  \Rightarrow
  \mathbb H_{a,b}
```

or the reverse comparison, the composition operation is

```math
\mathsf{Comp}_E(\mathbb H_{a,b};m)
  =
  \mathsf{EComp}_m(\mathbb H_{a,b})
  =
  (\mathbb H_{a,m},\mathbb H_{m,b};\varepsilon_m).
```



**Decomposition phenomenon.** The cut vertex decomposes a direct anchored record into mediated partial records. The decomposition is a subdivision or refinement, not a proof that the original record is strictly equal to the subdivided composite.

**Residue ledger.** The self-anchored ledger

```math
\mathbb W_E:
  \mathsf{EComp}_m(\mathbb H_{a,b})
  \Rightarrow_{\mathsf{USD}}
  \mathsf{EComp}_m(\mathbb H_{a,b})
```

records the explanatory excess of the cut vertex, the direction of $`\varepsilon_m`$, and the material not adopted by either partial path.

</div>

<div class="definition">

**Definition 45** (S-causeton: stabilization and gap decomposition). The S-causeton

```math
\mathfrak c_S
  =
  (\mathsf{Comp}_S,\mathsf{Dec}_S,\mathbb W_S,\kappa_S)
```

has the following data.

**Composition operation.** The input is a pair of S-compatible USD functors $`\mathbb H,\mathbb K`$, together with a complete gap lattice

```math
\Lambda_{\mathbb H,\mathbb K}
```

and a monotone gap update map

```math
\Phi_{\mathbb H,\mathbb K}:
  \Lambda_{\mathbb H,\mathbb K}\to
  \Lambda_{\mathbb H,\mathbb K}.
```

After a fixed point

```math
\Delta^*=\Phi_{\mathbb H,\mathbb K}(\Delta^*)
```

is selected, the composition operation is

```math
\mathsf{Comp}_S(\mathbb H,\mathbb K;\Delta^*)
  =
  \mathsf{SComp}(\mathbb H,\mathbb K;\Delta^*)
  \mathrel{:=}
  \mathrm{SMol}(\mathbb H,\mathbb K;\Delta^*).
```

Existence follows, for example, from the Knaster-Tarski fixed point theorem when the stated monotonicity and completeness conditions hold.

**Decomposition phenomenon.** Sideways stabilization decomposes the interaction into the shared observable molecule and the gap that remains nonzero. The completion condition is not $`\Delta^*=0`$ but shared stability.

**Residue ledger.** The self-anchored ledger is the S-molecular ledger already introduced:

```math
\mathbb W_S
  =
  \mathbb W_{\mathrm{SMol}(\mathbb H,\mathbb K;\Delta^*)}:
  \mathrm{SMol}(\mathbb H,\mathbb K;\Delta^*)
  \Rightarrow_{\mathsf{USD}}
  \mathrm{SMol}(\mathbb H,\mathbb K;\Delta^*).
```

It records the non-adopted discrepancy, fixed sideways gap, and boundary-visible waste emitted by the stabilization.

</div>

<div class="definition">

**Definition 46** (Sequence category). Let $`\mathsf{Seq}(\mathsf{Smart}_{\mathsf{USD}})`$ be the category of finite composable sequences of USD functors. An object is a finite chain

```math
\mathcal H=(\mathbb H_1,\ldots,\mathbb H_n).
```



</div>

<div class="definition">

**Definition 47** (U/D flip). Assume that the stance involution $`\tau:\mathsf{St}\to\mathsf{St}`$ lifts to a carrier-preserving record involution

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
  q(\bar\tau U_F)=(F,\underline D).
```



</div>

<div class="definition">

**Definition 48** (T-causeton: turnover and directional decomposition). The T-causeton

```math
\mathfrak c_T
  =
  (\mathsf{Comp}_T,\mathsf{Dec}_T,\mathbb W_T,\kappa_T)
```

has the following data.

**Composition operation.** The input is a finite USD functor chain

```math
\mathcal H=(\mathbb H_1,\ldots,\mathbb H_n).
```

The composition operation is temporal turnover:

```math
\mathsf{Comp}_T(\mathcal H)
  =
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



**Decomposition phenomenon.** Turnover decomposes the original reading order, causal direction, responsibility direction, and adopted stance assignment into a turned record chain. A chain that was read forward as an identification proposal may be re-read backward as a non-adoption record, but this is a transformation of records, not a proof of ordinary inequality.

**Residue ledger.** The self-anchored ledger

```math
\mathbb W_T:
  \mathsf{TComp}(\mathcal H)\Rightarrow_{\mathsf{USD}}\mathsf{TComp}(\mathcal H)
```

records the directional residue emitted by reversal and U/D turnover. If no information is lost, $`\mathsf{TComp}`$ is involutive up to record equivalence:

```math
\mathsf{TComp}^2\cong 1.
```

If compression, stabilization, or descent has discarded information, the weaker USD-level comparison

```math
\mathsf{TComp}^2(\mathcal H)\mathrel{\leadsto_{\mathsf{USD}}}\mathcal H
```

may be all that remains.

</div>

<div class="definition">

**Definition 49** (U-causeton: upward image). D-composition has two common adjoints when the relevant Kan extensions exist. The U-causeton

```math
\mathfrak c_U
  =
  (\mathsf{Comp}_U,\mathsf{Dec}_U,\mathbb W_U,\kappa_U)
```

has the following data.

**Composition operation.** Let $`\rho:\mathcal L\to\mathcal G`$ be a context morphism. When the left Kan extension exists, define the existential upward operation by

```math
\mathsf{Comp}_U^{\exists}
  =
  \mathsf{UComp}^{\exists}_{\rho}
  \mathrel{:=}
  \Sigma_\rho
  \mathrel{:=}
  \mathrm{Lan}_{\rho}:
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal L,\mathcal C)\to
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal G,\mathcal C),
```

with

```math
\Sigma_\rho\dashv \rho^*.
```

When the right Kan extension exists, define the universal upward operation by

```math
\mathsf{Comp}_U^{\forall}
  =
  \mathsf{UComp}^{\forall}_{\rho}
  \mathrel{:=}
  \Pi_\rho
  \mathrel{:=}
  \mathrm{Ran}_{\rho}:
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal L,\mathcal C)\to
  \mathsf{Smart}_{\mathsf{USD}}(\mathcal G,\mathcal C),
```

with

```math
\rho^*\dashv \Pi_\rho.
```

These Kan extensions are admitted as U-causetons only when they lift from the pure carrier category to $`\mathsf{Smart}_{\mathsf{USD}}`$. For example, if $`\Sigma_\rho\mathbb H`$ has carrier $`\mathrm{Lan}_\rho F`$, then its faces must be records over that carrier:

```math
q\circ U_{\mathrm{Lan}_\rho F}=(\mathrm{Lan}_\rho F,\underline U),
  \qquad
  q\circ D_{\mathrm{Lan}_\rho F}=(\mathrm{Lan}_\rho F,\underline D),
```

and similarly for $`\Pi_\rho`$ and $`\mathrm{Ran}_\rho F`$.

**Decomposition phenomenon.** Upward image decomposes a local record into the global candidate and the local specificity not adopted by that global reading. The existence of the ordinary Kan extension of $`F`$ is not enough; the USD record and contract data must lift with it.

**Residue ledger.** The self-anchored ledger

```math
\mathbb W_U:
  \mathsf{UComp}_{\rho}(\mathbb H)\Rightarrow_{\mathsf{USD}}\mathsf{UComp}_{\rho}(\mathbb H)
```

records the boundary conditions, local assumptions, and non-generalized material left behind by the upward image. If the lifted Kan extension does not exist, the corresponding U-causeton is undefined in the smart category even when the carrier Kan extension exists.

</div>

### Causeton coverage and saturation

The six causetons are not phases of an algorithm. A model may instantiate them in any order, may instantiate the same causeton type more than once, and may feed the records produced by one causeton into any other causeton whenever the input and existence conditions match. What can be required without ambiguity is not a global application order, but a coverage certificate.

<div class="definition">

**Definition 50** (Causeton agenda). For a USD test model, a causeton agenda is a six-tuple

```math
\mathcal A
  =
  (\mathcal A_C,\mathcal A_D,\mathcal A_E,
   \mathcal A_S,\mathcal A_T,\mathcal A_U),
```

where $`\mathcal A_\star`$ is a finite or indexed family of typed candidate instances of the corresponding causeton. The agenda is six-causeton-covered when no component is empty and every listed candidate supplies the input data, existence conditions, decomposition phenomenon, residue ledger, and coherence contract required by its causeton type.

</div>

<div class="definition">

**Definition 51** (Saturation closure). Let $`R_0`$ be a family of seed USD records and let $`\mathcal A`$ be a six-causeton-covered causeton agenda. Write

```math
\Gamma_{\mathcal A}(R)
  =
  R\cup C_{\mathcal A}(R)\cup D_{\mathcal A}(R)
   \cup E_{\mathcal A}(R)\cup S_{\mathcal A}(R)
   \cup T_{\mathcal A}(R)\cup U_{\mathcal A}(R)
```

for the family obtained by adding all well-typed outputs and residue ledgers of the candidate instances whose inputs are present in $`R`$. A saturated expansion is a fixed point

```math
R^*=\Gamma_{\mathcal A}(R^*)
```

generated from $`R_0`$; in a finite agenda this is the least closure reached by repeatedly adding newly well-typed outputs. The expansion is accepted only when every generated record preserves the common stance-lift invariant through $`q`$.

</div>

<div class="definition">

**Definition 52** (Causeton coverage certificate). A coverage certificate for a USD test model consists of a six-causeton-covered causeton agenda $`\mathcal A`$, a saturated expansion $`R^*`$, and a check that the realized causeton types are exactly

```math
\{\mathfrak c_C,\mathfrak c_D,\mathfrak c_E,
    \mathfrak c_S,\mathfrak c_T,\mathfrak c_U\}.
```

Thus missing use of any one causeton type is a failure of the test model, while multiple instances of a causeton type are permitted whenever they are typed.

</div>

Diagrams in examples may still display dependency arrows between records. Such arrows describe which outputs and residue ledgers are used as later inputs; they are not a global execution order for the six causetons.

## Sensitons: art-anchored perceptual connectors

Causetons record typed composition–decomposition pairs. Sensitons record how selected causeton precedence patterns are anchored inside an artistic observation context and become perceptible as controlled abstraction. A sensiton is therefore not a violation pattern. It is a connector from a causeton pair to an observer’s cognitive S-polymer under the boundary of a work, medium, performance, recording, exhibition, or other art-anchored frame.

<div class="definition">

**Definition 53** (Art anchoring). An art anchoring is a context

```math
\mathcal A_{\mathrm{art}}
```

whose objects are works, media, performances, recordings, scripts, scores, images, scenes, audiences, exhibition spaces, or other records belonging to an artistic observation frame. The anchoring supplies a boundary contract asserting that records inside $`\mathcal A_{\mathrm{art}}`$ are not automatically licensed as USD-free real-world commands, empirical claims, or moral judgments.

</div>

<div class="remark">

**Remark 54** (Why art anchoring is needed). The precedence patterns below can be unsafe when they are read as unlicensed claims about the base world. Inside $`\mathcal A_{\mathrm{art}}`$, the same patterns may become aesthetic operations: symbol formation, plot compression, reversal, surprise, estrangement, catharsis, or controlled recomposition. Art anchoring is the contract that keeps the emitted fission perceptible without immediately turning it into an external descent.

</div>

<div class="definition">

**Definition 55** (Sensiton). Let $`O`$ be an observer with cognitive S-polymer $`\mathbb P_O`$. A sensiton is an art-anchored USD perceptual record

```math
\mathfrak s
  =
  (\mathfrak c_X\prec\mathfrak c_Y,
   \mathcal A_{\mathrm{art}},
   O,
   \mathbb P_O,
   \mathbb W_{\mathfrak s},
   \kappa_{\mathfrak s}),
```

where $`\mathfrak c_X\prec\mathfrak c_Y`$ means that the $`X`$-causeton is perceptually staged before the $`Y`$-causeton inside $`\mathcal A_{\mathrm{art}}`$. The ledger $`\mathbb W_{\mathfrak s}`$ records the perceptual residue emitted by that staging, and $`\kappa_{\mathfrak s}`$ keeps the record inside the art anchoring unless an explicit descent license is supplied.

</div>

<div class="definition">

**Definition 56** (Magic-Sensiton). The Magic-Sensiton is the art-anchored precedence pattern

```math
\mathsf{MagicSens}
  \mathrel{:=}
  \mathsf{Sens}(U\prec D).
```

It stages a U-causeton before the corresponding D-causeton. In an unanchored setting this may look like an upward image before local restriction, context, or verification. Inside $`\mathcal A_{\mathrm{art}}`$, the same pattern is read as magic, symbol, mythic ascent, or imaginative world-formation: a local or weakly anchored record is first lifted into a larger possible world and only afterward lowered into scenes, bodies, materials, or particular perceptions.

</div>

<div class="definition">

**Definition 57** (Plot-Sensiton). The Plot-Sensiton is the art-anchored precedence pattern

```math
\mathsf{PlotSens}
  \mathrel{:=}
  \mathsf{Sens}(C\prec E).
```

It stages a C-causeton before the corresponding E-causeton. In an unanchored setting this may compress anchored records before the relevant cut vertices, tests, or mediation points are exposed. Inside $`\mathcal A_{\mathrm{art}}`$, the same pattern is read as plot: fragments are first compressed into a line, myth, scene, motif, or narrative pressure, and only afterward subdivided by turns, cuts, revelations, delays, and reversals.

</div>

<div class="definition">

**Definition 58** (Hall-Sensiton). The Hall-Sensiton is the art-anchored precedence pattern

```math
\mathsf{HallSens}
  \mathrel{:=}
  \mathsf{Sens}(T\prec S).
```

It stages a T-causeton before the corresponding S-causeton. In an unanchored setting this may reverse a system before its stabilizing S-molecular reading has been supplied. Inside $`\mathcal A_{\mathrm{art}}`$, the same pattern is read as hall, stage, theater, or performance space: time order, viewpoint, role, and U/D stance are turned before the work restabilizes them as an observable scene. The observer may experience surprise, estrangement, dread, recognition, or catharsis, but these effects remain anchored to the work unless a descent license carries them outside $`\mathcal A_{\mathrm{art}}`$.

</div>

<div class="remark">

**Remark 59** (Order of the three basic sensitons). The order

```math
\mathsf{MagicSens},\qquad
  \mathsf{PlotSens},\qquad
  \mathsf{HallSens}
```

follows the increasing externalization of abstraction. Magic-Sensiton forms a possible world, Plot-Sensiton compresses fragments into a line of readability, and Hall-Sensiton stages the line before an observer through turned time, role, and stance.

</div>

<div class="remark">

**Remark 60** (Sensitons and USD fission). Sensitons are designed to emit controlled USD fission in the observer’s cognitive S-polymer. The fission is not treated as a defect merely because it occurs. It becomes aesthetically useful when the art anchoring allows the observer to hold the fragments, residues, and reversed readings long enough for recomposition inside the work.

</div>

## USD fusion and USD fission

Causetons separate the typed operation from what an observer sees. The operation side is composition and decomposition. The observational side is USD fusion and USD fission. Fusion and fission are treated here as two provisional USD phenomena; later refinements may classify them into C/D/E/S/T/U-specific fusion and fission types.

<div class="definition">

**Definition 61** (USD fusion). Let $`\mathfrak c_\star`$ be a causeton with main output $`\mathbb M`$, residue ledger $`\mathbb W_\star`$, and observer or boundary resolution $`O`$. USD fusion is the observer-relative event

```math
\mathsf{USDFusion}_O(\mathfrak c_\star,\mathbb M)
```

in which $`\mathbb M`$ is readable as one boundary-visible composite record. Fusion is not identity collapse: the residue ledger remains attached, and the U-face and D-face remain stance-lifted over their realized carrier.

</div>

<div class="definition">

**Definition 62** (USD fission). Let $`\mathfrak c_\star`$ be a causeton with decomposition phenomenon $`\mathsf{Dec}_\star`$, residue ledger $`\mathbb W_\star`$, and observer or entity polymer $`\mathbb P_O`$. USD fission is the observer-relative event

```math
\mathsf{USDFission}_O(\mathfrak c_\star,\mathbb P_O)
```

in which the emitted decomposition becomes readable inside $`\mathbb P_O`$ as multiple fragments or separated partial records. It may also appear as contradictions, unintelligible residue, uncanny residue, or other boundary-visible non-unified material. Fission is a USD observation, not by itself a USD-free assertion that the source theory is false.

</div>

<div class="definition">

**Definition 63** (Controlled and critical fission). USD fission is controlled for an observer $`O`$ when the emitted fragments can be reassembled, interpreted, or used under the observer’s coherence contract without losing the relevant boundary witnesses. It is critical when the emitted residue exceeds the observer’s available divergence, ejection, or recomposition capacity and the record can no longer be read as one stable composite at the chosen resolution.

</div>

<div class="remark">

**Remark 64** (No intrinsic moral valence). USD fusion and USD fission are observational phases, not moral judgments. A fission may be destructive, controlled, explanatory, analytic, or creative depending on the surrounding carrier model and descent licenses. Likewise, a fusion may be stabilizing, misleading, compressive, or over-adoptive depending on the residue ledger it emits.

</div>

<div class="remark">

**Remark 65** (Composition and decomposition versus fusion and fission). Composition and decomposition belong to the causeton record. Fusion and fission are how the output and emitted residue are observed. Thus the reference slogan is:

```math
\text{composition and fusion, decomposition and fission}.
```

This slogan does not identify USD fusion with physical nuclear fusion, nor USD fission with physical nuclear fission. Those readings require separate base-domain realization.

</div>

## A syntactic reference implementation

This section records the minimum syntax needed for a conservative USD calculus. It is intentionally austere.

<div class="definition">

**Definition 66** (Base language). Let $`\mathcal L_0`$ be a base formal language with judgments

```math
\Gamma\vdash_0 A.
```

The base language may be first-order logic, type theory, an internal language of a category, or another fixed formal system.

</div>

<div class="definition">

**Definition 67** (USD extension). The USD calculus $`\mathsf{USDCalc}`$ extends $`\mathcal L_0`$ with record terms:

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

</div>

<div class="definition">

**Definition 68** (Descent license). A descent license is an explicit rule instance

```math
\mathsf{IdLic}(R,A)
```

that permits a USD record $`R`$ to be translated into a base assertion $`A`$ in $`\mathcal L_0`$. Examples include a definition, an isomorphism, a proved equivalence, a semantic interpretation, or a verified coercion.

</div>

<div class="definition">

**Definition 69** (Erasure). The erasure translation

```math
|-|:\mathsf{USDCalc}\to\mathcal L_0
```

acts as identity on base terms and formulas and removes pure USD records unless a descent license supplies a base formula.

</div>

<div class="theorem">

**Theorem 70** (Conservative design theorem). *Assume that every USD inference rule is record-forming, record-transforming, or explicitly licensed by a descent rule. If

```math
\Gamma\vdash_{\mathsf{USDCalc}} A
```

and $`A`$ is USD-free, then the derivation of $`A`$ uses only base rules and licensed descents. Consequently

```math
|\Gamma|\vdash_0 A
```

provided each used descent license is valid in the base system.*

</div>

<div class="proof">

*Proof.* By induction on the given derivation. Base rules translate to base rules. Record-forming and record-transforming USD rules have USD-record conclusions and therefore cannot be the final step of a USD-free formula. If a USD record is used to produce a USD-free conclusion, the rule must be a licensed descent by hypothesis; replacing that step with its base license yields a derivation in $`\mathcal L_0`$. The induction removes all unlicensed USD bookkeeping from the derivation of $`A`$. ◻

</div>

This theorem is deliberately conditional. It states the safety contract of the reference implementation. A stronger metatheorem for a particular formal calculus would require a fully specified proof system, but this condition is already enough to prevent USD records from acting as hidden proof rules.

## Worked toy model

<div class="example">

**Example 71** (Poset record model). Let $`\mathcal C`$ be a poset regarded as a category. Let

```math
\mathsf{Rel}_{\mathcal C}(a,b)
```

be the truth value of $`a\leq b`$. Let $`\mathsf{BVis}`$ select those comparable pairs for which a chosen boundary label is present. Let $`\mathsf{Rec}_{\mathsf{USD}}`$ be the product category

```math
\mathcal C\times\mathsf{St}
```

with projection to $`\mathsf{St}`$. The realization projection is

```math
r=\mathrm{pr}_{\mathcal C}:\mathcal C\times\mathsf{St}\to\mathcal C,
```

so the combined projection is

```math
q=(r,\pi):\mathcal C\times\mathsf{St}\to\mathcal C\times\mathsf{St},
```

the identity in this minimal model. Then $`\mathcal U\cong\mathcal C\cong\mathcal D`$, but the two copies are distinguished as fibers. A USD functor is a functor $`F`$ together with two stance-lifted copies $`U_F,D_F`$ over the same $`F`$ and a boundary label. In this model D-composition is ordinary reindexing of monotone maps, C-composition is pushout of indexing posets when it exists, and T-composition swaps the two copies and reverses a finite chain while preserving realization.

</div>

<div class="example">

**Example 72** (Complete lattice gap model). Let the gap lattice be a complete lattice $`\Lambda`$. If a sideways interaction gives a monotone map $`\Phi:\Lambda\to\Lambda`$, then the set of fixed points is nonempty by the Knaster-Tarski theorem. Choosing the least fixed point gives a canonical minimal shared discrepancy. Choosing the greatest fixed point gives a maximal conservative discrepancy. The choice is part of the model policy.

</div>

## Relativistic test model

The relativistic material is not an application claiming new physics. It is a test model for the USD vocabulary because relativity naturally involves observers, frames, local restrictions, and time-oriented records. The historical sources are Einstein’s 1905 paper on special relativity and his 1916 paper on general relativity .

<div class="definition">

**Definition 73** (Lorentzian test base). Let $`(M,g)`$ be a Lorentzian manifold. Let $`\mathcal O(M,g)`$ be a chosen category of local observers or frames. A morphism in $`\mathcal O(M,g)`$ may be a change of frame, inclusion of a local chart, or another chosen admissible comparison of observations.

</div>

<div class="example">

**Example 74** (D-composition as local restriction). A global geometric record, such as a metric-dependent record on $`(M,g)`$, may be lowered along a local frame map

```math
\rho:O\to M
```

by pullback:

```math
\mathsf{DComp}_{\rho}(\mathbb H)=\rho^*\mathbb H.
```

This is the familiar mathematical shape of restricting global data to a local observer or frame. The USD interpretation only adds adoptive and non-adoptive record faces and boundary witnesses.

</div>

<div class="example">

**Example 75** (T-composition as record turnover). A time-oriented chain of observation records may be transformed by $`\mathsf{TComp}`$ into the reverse-order chain with U and D faces exchanged. This is not asserted to be physical time reversal symmetry. It is a record operation that leaves the entities and geometric carrier untouched while turning the USD bookkeeping upside down.

</div>

<div class="remark">

**Remark 76** (No hidden physics). If a model uses Lorentz transformations, connections, curvature, or field equations, those structures must be explicitly included in the base category or in the relation witness profunctor. USD functors do not supply them automatically.

</div>

### Newton-Einstein test

The Newton-Einstein test uses E-composition as its main operation. The test does not claim that Einstein proved Newtonian absolute time false by one direct replacement. It records a two-stage theoretical operation: Newton’s single global time parameter is first decomposed inside special relativity and then extended through local inertial structure into general relativity. The relevant historical base texts are Newton’s *Principia*, Einstein’s 1905 paper on special relativity, and Einstein’s 1916 paper on general relativity .

Let

```math
\mathcal N_{\mathrm{mech}},
  \qquad
  \mathcal S_{\mathrm{rel}},
  \qquad
  \mathcal G_{\mathrm{rel}}
```

denote schematic categories of Newtonian mechanics, special relativity, and general relativity. A Newtonian time record may be written

```math
\mathbb N_T:a\Rightarrow_{\mathsf{USD}} b,
```

where an event configuration is assigned to a single frame-independent temporal order. In the Newtonian record, simultaneity and duration are treated as globally available, and the time coordinate is not produced by a synchronization protocol internal to the theory.

The coarse E-composition flow is

```math
\mathbb N_T
  \xrightarrow{\mathsf{EComp}_{\mathcal S_{\mathrm{rel}}}}
  \mathbb E_{\mathrm{SR}}
  \xrightarrow{\mathsf{EComp}_{\mathcal G_{\mathrm{rel}}}}
  \mathbb E_{\mathrm{GR}}.
```

Thus special relativity is not skipped. It is the first cut vertex through which the Newtonian record is factored before the general relativistic record is formed.

**First E-instance: Newton to special relativity.** The cut vertex $`m_{\mathrm{SR}}`$ is itself resolved into smaller cuts:

```math
\begin{aligned}
  \mathbb N_T
  &\xrightarrow{\mathsf{EComp}_{\mathrm{clock}}}
  \text{local clock readings}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{sync}}}
  \text{light-signal synchronization}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{inertial}}}
  \text{inertial-frame coordinate time}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{Lorentz}}}
  \text{Lorentz-compatible transformations}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{interval}}}
  \mathbb E_{\mathrm{SR}}.
\end{aligned}
```

The central cut is synchronization. What was transparent in the Newtonian record becomes an explicit operation:

```math
\text{remote simultaneity}
  \quad\leadsto\quad
  \text{clock comparison by signal protocol}.
```

The carrier is no longer a single absolute time assignment. It is a special-relativistic carrier in which coordinate time is indexed by inertial frame and constrained by the constancy of light speed. The adoptive face contains

```math
\begin{aligned}
  U_{\mathrm{SR}}
  =
  \{&\text{local clocks, synchronization, inertial frames,}\\
    &\text{Lorentz transformations, invariant interval}\}.
\end{aligned}
```

The non-adoptive residue contains

```math
\begin{aligned}
  D_{\mathrm{Newton}}
  =
  \{&\text{universal simultaneity, frame-independent absolute time,}\\
    &\text{Galilean velocity addition, instantaneous global temporal order}\}.
\end{aligned}
```

This is not erasure of Newtonian mechanics. It is a factorization of the role played by absolute time into observable clock readings, synchronization, frame choice, transformation law, and invariant spacetime interval.

**Second E-instance: special to general relativity.** The next cut vertex is not another synchronization convention. It is the passage from global inertial frames to local inertial structure:

```math
\begin{aligned}
  \mathbb E_{\mathrm{SR}}
  &\xrightarrow{\mathsf{EComp}_{\mathrm{local}}}
  \text{local inertial frames}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{equiv}}}
  \text{equivalence principle}\\
  &\xrightarrow{\mathsf{EComp}_{g}}
  \text{metric field }g\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{curv}}}
  \text{curvature}\\
  &\xrightarrow{\mathsf{EComp}_{\mathrm{EFE}}}
  \mathbb E_{\mathrm{GR}}.
\end{aligned}
```

Special relativity remains as a local record: in sufficiently small regions and in the absence of curvature effects at the chosen resolution, the general relativistic record restricts to a special-relativistic one. The general relativistic extension changes the carrier from flat Minkowski spacetime to metric spacetime. Time is no longer merely frame-indexed coordinate time on a flat background; it is part of a metric field whose geometry is coupled to gravitation.

The complete theoretical surgery can therefore be summarized as

```math
\begin{aligned}
  \text{absolute Newtonian time}
  &\xrightarrow{\mathsf{EComp}_{\mathcal S_{\mathrm{rel}}}}
  \text{clock/synchronization/frame/interval structure}\\
  &\xrightarrow{\mathsf{EComp}_{\mathcal G_{\mathrm{rel}}}}
  \text{local inertial/metric/curvature structure}.
\end{aligned}
```

The USD reading is that Einstein did not merely negate the Newtonian record. He inserted the missing operational vertices, preserved the usable low-speed and weak-field residue through appropriate limiting policies, and moved the privileged invariant from absolute time to spacetime structure. A USD-free physical claim about the Newtonian limit, Lorentz transformations, or Einstein field equations still requires the ordinary base theory; the USD test only records the typed decomposition flow.

## Interdisciplinary test model

The preceding relativistic section tests USD vocabulary inside a mathematical physics setting. The same discipline can be used for interdisciplinary examples, where the carrier data are not all drawn from one field. The purpose of such a model is not to turn a social or economic interpretation into a proof of intention. It is to keep the interfaces visible when social records and economic records are read together.

<div class="definition">

**Definition 77** (Interdisciplinary test base). Let $`\mathcal S`$ be a category of sociological records and let $`\mathcal E`$ be a category of economic records. An interdisciplinary carrier may be taken to be the product category

```math
\mathcal C_{\mathcal S,\mathcal E}
  \mathrel{:=}
  \mathcal S\times\mathcal E,
```

or, more generally, a category equipped with projection functors

```math
p_{\mathcal S}:\mathcal C_{\mathcal S,\mathcal E}\to\mathcal S,
  \qquad
  p_{\mathcal E}:\mathcal C_{\mathcal S,\mathcal E}\to\mathcal E.
```

A USD functor into $`\mathcal C_{\mathcal S,\mathcal E}`$ records a joint social-economic reading. Its relation witnesses may compare social data, economic data, or boundary-visible couplings between them.

</div>

<div class="remark">

**Remark 78** (No hidden interdisciplinary descent). An interdisciplinary USD record is not, by itself, an empirical explanation. A descent license must specify the accepted historical sources, social model, economic model, and rule that permits a USD record to be translated into a USD-free claim. Without such a license, the record remains a structured hypothesis or interpretation.

</div>

### Satoshi test

The pseudonymous creator of Bitcoin gives a useful interdisciplinary test case. The Bitcoin white paper presents the system as peer-to-peer electronic cash without reliance on a trusted third party . Late in 2010, Satoshi Nakamoto publicly warned that Bitcoin was still a small beta community and that sudden WikiLeaks-driven attention could bring destructive heat . The following day, Satoshi also described denial-of-service resistance as unfinished work . Separately, claims that Satoshi or a dominant early miner controlled about one million bitcoins depend on chain-analysis heuristics; the evidence is suggestive but not as robust as popular retellings often imply .

The source data are kept in two different categories. The sociological side records legitimacy, founder authority, regulatory visibility, community dependence, and governance centrality. The economic side records early coin concentration, liquidity, expected sell-pressure signals, scarcity belief, and market confidence. The test is not licensed to derive an economic conclusion directly from a sociological one, or a sociological intention directly from an economic trace.

Let $`\mathcal A_{\mathcal S}`$ be a small category of sociological founder actions: revealing an identity, exercising founder authority, transferring control, remaining pseudonymous, or withdrawing from public control. Let $`\mathcal A_{\mathcal E}`$ be a small category of economic founder actions: moving early coins, not moving early coins, distributing control, signalling sale, or remaining economically inactive. These categories are not identified. They touch only through a boundary-visible interface.

**D0-instance.** Begin with broad sociological and economic USD records $`\mathbb H_{\mathcal S}^{0}`$ and $`\mathbb H_{\mathcal E}^{0}`$. Let

```math
\rho_{\mathcal S}^{0}:
  \mathcal A_{\mathcal S}\to\mathcal G_{\mathcal S},
  \qquad
  \rho_{\mathcal E}^{0}:
  \mathcal A_{\mathcal E}\to\mathcal G_{\mathcal E}
```

be context morphisms selecting only founder-action data from broader social and economic contexts. The first downward restriction is

```math
\mathbb H_{\mathcal S}^{f}
  \mathrel{:=}
  \mathsf{DComp}_{\rho_{\mathcal S}^{0}}(\mathbb H_{\mathcal S}^{0}),
  \qquad
  \mathbb H_{\mathcal E}^{f}
  \mathrel{:=}
  \mathsf{DComp}_{\rho_{\mathcal E}^{0}}(\mathbb H_{\mathcal E}^{0}).
```

This step does not select withdrawal as the answer. It only removes material outside the founder-action comparison class.

**C-instance.** The social and economic records are read together only inside the interdisciplinary carrier $`\mathcal C_{\mathcal S,\mathcal E}`$. Before applying compression, assume the model supplies typed carrier lifts

```math
\widehat{\mathbb H}_{\mathcal S}^{f}:
  \mathcal A_{\mathcal S}\to \mathcal C_{\mathcal S,\mathcal E},
  \qquad
  \widehat{\mathbb H}_{\mathcal E}^{f}:
  \mathcal A_{\mathcal E}\to \mathcal C_{\mathcal S,\mathcal E}
```

whose projections recover the restricted social and economic records:

```math
p_{\mathcal S}\circ\widehat{\mathbb H}_{\mathcal S}^{f}
  =
  \mathbb H_{\mathcal S}^{f},
  \qquad
  p_{\mathcal E}\circ\widehat{\mathbb H}_{\mathcal E}^{f}
  =
  \mathbb H_{\mathcal E}^{f}.
```

The unused projections are bookkeeping fields supplied by the model, not licenses for cross-disciplinary descent. Let

```math
\Theta_{\mathrm{Sat}}:
  \mathcal A_{\mathcal S}^{\mathrm{op}}\times\mathcal A_{\mathcal E}
  \to \mathbf{Pos}
```

be an interface profunctor. An element

```math
\theta\in\Theta_{\mathrm{Sat}}(s,e)
```

witnesses that a social founder action $`s`$ and an economic founder action $`e`$ are two boundary-visible readings of the same founder episode, such as public identity, authority, early coin movement, non-movement, market signal, or community dependence. Let

```math
\mathcal I_{\mathrm{Sat}}
  \mathrel{:=}
  \int_{\mathcal A_{\mathcal S}^{\mathrm{op}}\times\mathcal A_{\mathcal E}}
  \Theta_{\mathrm{Sat}}.
```

Compression along this interface gives the joint record

```math
\mathbb J_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{CComp}_{\mathcal I_{\mathrm{Sat}}}
  (\widehat{\mathbb H}_{\mathcal S}^{f},
   \widehat{\mathbb H}_{\mathcal E}^{f}).
```

The compression does not say that social authority is an economic price, or that economic non-movement is a social intention. It records only the typed interface through which both projections become visible in the same interdisciplinary carrier.

**D1-instance.** Now restrict the compressed record to the local Satoshi context. Let

```math
\rho_{\mathrm{Sat}}:
  \mathcal L_{\mathrm{Sat}}
  \to
  \mathcal A_{\mathcal S}\sqcup_{\mathcal I_{\mathrm{Sat}}}
  \mathcal A_{\mathcal E}
```

select the local span generated by pseudonymity, public withdrawal, non-exercise of founder authority, early coin non-movement, and the visible decentralization signal. Define

```math
\mathbb L_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{DComp}_{\rho_{\mathrm{Sat}}}(\mathbb J_{\mathrm{Sat}}).
```

This second downward restriction is local reading, not historical descent. It does not infer the inner intention, the identity, or the key status of Satoshi.

**E-instance.** Anchor the local record between an initial founder-action state $`a_0`$ and a decentralization-signal state $`a_1`$:

```math
\mathbb L_{\mathrm{Sat},a_0,a_1}:a_0\Rightarrow_{\mathsf{USD}}a_1.
```

Insert the following cut vertices by iterated E-composition:

```math
\begin{aligned}
  m_{\mathrm{id}} &= \text{public identity visibility},\\
  m_{\mathrm{auth}} &= \text{founder authority},\\
  m_{\mathrm{coin}} &= \text{early coin movement or non-movement},\\
  m_{\mathrm{sell}} &= \text{large sell-pressure signal}.
\end{aligned}
```

Thus

```math
\mathbb E_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{EComp}_{m_{\mathrm{sell}}}
  \mathsf{EComp}_{m_{\mathrm{coin}}}
  \mathsf{EComp}_{m_{\mathrm{auth}}}
  \mathsf{EComp}_{m_{\mathrm{id}}}
  (\mathbb L_{\mathrm{Sat},a_0,a_1}).
```

The first two cuts are sociological: they concern visibility, authority, central target formation, and community dependence. The last two cuts are economic: they concern coin movement and sell-pressure signals. The factorization is deliberately conservative; it prevents the record from jumping directly from withdrawal to decentralization or from coin non-movement to personal intention.

**S-instance.** The sideways stabilization is the core of the Satoshi test. Let $`\Lambda_{\mathrm{Sat}}`$ be a complete lattice of discrepancies between decentralization-supporting outputs and non-adopted founder residue, and let

```math
\Phi_{\mathrm{Sat}}:
  \Lambda_{\mathrm{Sat}}\to\Lambda_{\mathrm{Sat}}
```

be the monotone update map supplied by the model. Choose a fixed point

```math
\Delta_{\mathrm{Sat}}^*
  =
  \Phi_{\mathrm{Sat}}(\Delta_{\mathrm{Sat}}^*).
```

The adoptive face is a product reading

```math
U_{\mathrm{decent}}
  =
  (U_{\mathcal S},U_{\mathcal E}),
```

where

```math
\begin{aligned}
  U_{\mathcal S}
  &=
  \{\text{reduced founder authority, reduced central target,
    reduced community dependence}\},\\
  U_{\mathcal E}
  &=
  \{\text{reduced large-sell signal, reduced direct founder-liquidity
    pressure}\}.
\end{aligned}
```

The non-adoptive face is likewise a product reading

```math
D_{\mathrm{fame/wealth}}
  =
  (D_{\mathcal S},D_{\mathcal E}),
```

where

```math
\begin{aligned}
  D_{\mathcal S}
  &=
  \{\text{public fame, founder control, proved inner intention}\},\\
  D_{\mathcal E}
  &=
  \{\text{direct realization of early coin wealth, exact status of
    early coins}\}.
\end{aligned}
```

Let $`A_{\mathrm{decent}}`$ be the decentralization-support record whose adoptive face is $`U_{\mathrm{decent}}`$, and let $`B_{\mathrm{residue}}`$ be the founder-residue record whose non-adoptive face is $`D_{\mathrm{fame/wealth}}`$. The stabilized record is

```math
\mathrm{SMol}_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{SComp}(A_{\mathrm{decent}},B_{\mathrm{residue}};
   \Delta_{\mathrm{Sat}}^*)
  =
  \mathrm{SMol}
  (A_{\mathrm{decent}},B_{\mathrm{residue}};
   \Delta_{\mathrm{Sat}}^*).
```

At the visible boundary,

```math
U_{\mathrm{decent}}
  \mathrel{\leadsto_{\mathsf{USD}}}
  D_{\mathrm{fame/wealth}}.
```

This says that decentralized adoption can be modeled as stable only while public fame, founder control, direct realization of early coin wealth, proved intention, and exact early-coin status remain non-adopted residue. It does not say that fame or wealth were morally rejected, and it does not prove who Satoshi was.

A conservative best-effort policy can be expressed by assigning each compatible local action $`a\in\mathcal L_{\mathrm{Sat}}`$ a social cost and an economic cost,

```math
C_{\mathcal S}(a),
  \qquad
  C_{\mathcal E}(a),
```

and selecting an action whose worst visible cost is minimal:

```math
a^*
  \in
  \operatorname*{arg\,min}_{a\in\mathcal L_{\mathrm{Sat}}}
  \max\{C_{\mathcal S}(a),C_{\mathcal E}(a)\}.
```

Under one plausible policy, withdrawal together with non-movement of early coins is a candidate for $`a^*`$. The social reading is reduced founder centrality and reduced central target formation. The economic reading is the absence of a large direct sell-pressure signal. The loss is not erased: abandoned fame, unresolved identity, founder control, direct realization of early wealth, and exact early-coin status remain attached as self-anchored residue.

**T-instance.** Let $`\mathcal H_{\mathrm{Sat}}`$ be the finite subdivided record chain underlying $`\mathbb E_{\mathrm{Sat}}`$ and $`\mathrm{SMol}_{\mathrm{Sat}}`$. Temporal turnover gives

```math
\mathbb T_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{TComp}(\mathcal H_{\mathrm{Sat}}).
```

Forward, the record reads:

```math
\text{founder withdrawal and early-coin non-movement}
  \longrightarrow
  \text{decentralization-supporting signal}.
```

Turned over, it reads:

```math
\begin{aligned}
  &\text{decentralized Bitcoin record}\\
  &\quad\longrightarrow
  \text{founder fame, control, wealth, identity, and intention as residue}.
\end{aligned}
```

This reversal blocks a common overreading. The present decentralized record may be read as carrying founder-residue, but it does not reveal the founder’s private reason for withdrawing or not moving coins.

**U-instance.** When the relevant lifted Kan extension exists, image the turned local record upward along $`\rho_{\mathrm{Sat}}`$:

```math
\mathbb U_{\mathrm{Sat}}
  \mathrel{:=}
  \mathsf{UComp}^{\exists}_{\rho_{\mathrm{Sat}}}(\mathbb T_{\mathrm{Sat}})
  \leadsto
  \mathrm{FounderExitAsDecentralizationStabilizer}.
```

The upward image is a general schema, not a biographical claim. It says that, in projects where a founder has strong initial authority and a large visible economic position, public withdrawal, non-exercise of authority, and non-movement of large early holdings can stabilize a decentralization record, provided the fame, control, wealth, identity, and intention that are not adopted by the main output remain recorded as residue.

<div class="remark">

**Remark 79** (No proof of Satoshi’s intention). The Satoshi test licenses at most a structural conclusion: withdrawal and coin non-movement can be modeled as a best-effort stable record for Bitcoin’s social and economic decentralization. It does not license the USD-free assertion that Satoshi chose withdrawal for that reason. The inner intention, the exact identity, and the exact status of the early coins remain non-adopted residue unless supplied by independent historical evidence and an explicit descent license.

</div>

### Oppenheimer test

The Oppenheimer test is an interdisciplinary stress test for ethical translation. Its source data use only two categories: a category of theoretical nuclear physics and a category of public policy. The philosophical forum and the trial of Socrates are not assumed as source categories. They appear only after the test supplies a six-causeton coverage certificate and saturates the generated USD record family. No global application order of the causetons is part of the claim.

Historically, the Manhattan Project made nuclear fission and explosive chain reactions into an organized weapon program. The Smyth Report describes the scientific and administrative development of atomic energy for military purposes . The Franck Report records that some project scientists understood the use of the first atomic bombs as a social and political problem, not merely a technical one . Plato’s *Apology* records the trial in which Socrates’ public practice of examination was answered by charges of corrupting the youth and impiety . The USD claim below is not that these events are historically the same. It is that the Oppenheimer record can be saturated, without dropping the decisive gap, into a record family whose upward image realizes the forum structure made visible by the trial of Socrates.

Let

```math
\mathcal T_{\mathrm{nuc}}
```

be a category of theoretical nuclear-physics records. Its objects may be fission models, chain-reaction calculations, criticality estimates, yield predictions, uncertainty bounds, or experimental confirmations. Its morphisms are refinements, derivations, approximations, empirical constraints, or transitions from speculative theory to reliable prediction. Let

```math
\mathcal P_{\mathrm{pub}}
```

be a category of public-policy records. Its objects may be nonresearch, research, secret development, demonstration, military use, nonuse, international control, or postwar governance. Its morphisms are funding, authorization, classification, command, deployment, diplomatic proposal, or legal constraint.

The two categories touch through a feasibility profunctor

```math
\Theta_{\mathrm{Op}}:
  \mathcal T_{\mathrm{nuc}}^{\mathrm{op}}\times
  \mathcal P_{\mathrm{pub}}
  \to \mathbf{Pos}.
```

An element

```math
\theta\in\Theta_{\mathrm{Op}}(t,p)
```

is a witness that a theoretical record $`t`$ makes a policy record $`p`$ available, urgent, dangerous, or governable. Such a witness may record technical feasibility, predictability, destructive scale, uncertainty, time pressure, enemy-access risk, secrecy, irreversibility, or accountability. The interface category is the Grothendieck construction

```math
\mathcal I_{\Theta}
  \mathrel{:=}
  \int_{\mathcal T_{\mathrm{nuc}}^{\mathrm{op}}\times
        \mathcal P_{\mathrm{pub}}}
  \Theta_{\mathrm{Op}},
```

whose objects are triples $`(t,p,\theta)`$. This interface is the exact place where theoretical success becomes a public-policy option.

**C-instance.** Let $`\mathbb H_T`$ be a USD record over $`\mathcal T_{\mathrm{nuc}}`$ and let $`\mathbb H_P`$ be a USD record over $`\mathcal P_{\mathrm{pub}}`$. To type the compression, assume an interdisciplinary carrier category $`\mathcal C_{\mathrm{Op}}`$ and typed carrier lifts

```math
\widehat{\mathbb H}_T:
  \mathcal T_{\mathrm{nuc}}\to\mathcal C_{\mathrm{Op}},
  \qquad
  \widehat{\mathbb H}_P:
  \mathcal P_{\mathrm{pub}}\to\mathcal C_{\mathrm{Op}}.
```

Let

```math
i:\mathcal I_{\Theta}\to\mathcal T_{\mathrm{nuc}},
  \qquad
  j:\mathcal I_{\Theta}\to\mathcal P_{\mathrm{pub}}
```

be the interface projections, with the first projection read through the variance of $`\Theta_{\mathrm{Op}}`$. Compression along the interface gives an Oppenheimer record

```math
\mathbb O
  \mathrel{:=}
  \mathsf{CComp}_{\mathcal I_{\Theta}}
  (\widehat{\mathbb H}_T,\widehat{\mathbb H}_P).
```

Its compressed global context is

```math
\mathcal G_{\mathrm{Op}}
  \mathrel{:=}
  \mathcal T_{\mathrm{nuc}}
  \sqcup_{\mathcal I_{\Theta}}
  \mathcal P_{\mathrm{pub}}.
```

The compression does not identify theory with policy. It only records that the two sides now share a boundary witness: the same nuclear-physics result that counts as explanatory success in $`\mathcal T_{\mathrm{nuc}}`$ also counts as a possible state action in $`\mathcal P_{\mathrm{pub}}`$.

**D-instance.** Choose a local theory-practice context

```math
\rho_{\mathrm{Op}}:
  \mathcal L_{\mathrm{Op}}\to\mathcal G_{\mathrm{Op}}
```

that retains the possible/ought collision and forgets the details of isotopes, laboratories, committees, and military offices. Downward restriction gives

```math
\mathbb L_{\mathrm{Op}}
  \mathrel{:=}
  \mathsf{DComp}_{\rho_{\mathrm{Op}}}(\mathbb O).
```

The local carrier retains the typed collision

```math
\text{possible}
  \;\Longrightarrow\;
  \text{must decide whether it ought to be done}.
```

This is sharper than the slogan that can does not imply ought. The lowered record says that can creates a decision burden. A theory may remain epistemic in its own category, but after contact with public policy it generates an actionable option for which someone becomes answerable.

**E-instance.** To avoid a leap from theory to guilt, anchor $`\mathbb L_{\mathrm{Op}}`$ between the local records $`\mathrm{possible}`$ and $`\mathrm{responsible}`$:

```math
\mathbb L_{\mathrm{Op},\mathrm{possible},\mathrm{responsible}}:
  \mathrm{possible}\Rightarrow_{\mathsf{USD}}\mathrm{responsible}.
```

Insert an internal cut vertex

```math
m_{\mathrm{act}}
  =
  \text{actionability}.
```

The Oppenheimer record is subdivided as

```math
\mathbb E_{\mathrm{Op}}
  \mathrel{:=}
  \mathsf{EComp}_{m_{\mathrm{act}}}
  (\mathbb L_{\mathrm{Op},\mathrm{possible},\mathrm{responsible}})
  =
  (\mathbb O_{\mathrm{possible},m_{\mathrm{act}}},
   \mathbb O_{m_{\mathrm{act}},\mathrm{responsible}};
   \varepsilon_{m_{\mathrm{act}}}).
```

The first half records the passage from theoretical possibility to available state action. The second half records the passage from available state action to responsibility for irreversible consequences. Thus the ethical problem is not imported from outside physics or outside policy. It is produced at the cut where a prediction becomes an implementable public act.

**S-instance.** Let $`\Lambda_{\mathrm{Op}}`$ be a complete lattice of discrepancies between theoretical success and ethically non-neutral public action. Let

```math
\Phi_{\mathrm{Op}}:
  \Lambda_{\mathrm{Op}}\to\Lambda_{\mathrm{Op}}
```

be the monotone update map supplied by the model, and choose a fixed point

```math
\Delta_{\mathrm{Op}}^*
  =
  \Phi_{\mathrm{Op}}(\Delta_{\mathrm{Op}}^*).
```

Let $`A_{\mathrm{theory}}`$ be the theoretical-success record and $`B_{\mathrm{practice}}`$ the public-action residue record. The stable Oppenheimer molecule is

```math
\mathrm{SMol}_{\mathrm{Op}}
  \mathrel{:=}
  \mathsf{SComp}(A_{\mathrm{theory}},B_{\mathrm{practice}};
   \Delta_{\mathrm{Op}}^*)
  =
  \mathrm{SMol}
  (A_{\mathrm{theory}},B_{\mathrm{practice}};
   \Delta_{\mathrm{Op}}^*).
```

Its adoptive theoretical face is

```math
U_{\mathrm{theory}}
  =
  \{\text{truth, prediction, possibility, technical control}\},
```

while its non-adoptive public-policy face is

```math
D_{\mathrm{practice}}
  =
  \{\text{harm, authority, secrecy, irreversibility,
    accountability}\}.
```

The interlock is boundary-visible:

```math
U_{\mathrm{theory}}
  \mathrel{\leadsto_{\mathsf{USD}}}
  D_{\mathrm{practice}}.
```

The fixed gap is not zero. It is the stable discrepancy

```math
\begin{aligned}
  \Delta_{\mathrm{Op}}^*
  &=
  \text{the stable gap between theoretical success}\\
  &\quad\text{and ethically non-neutral public action}.
\end{aligned}
```

The residue contains both sides of the policy dilemma: use may create direct and irreversible destruction, while nonuse, delay, demonstration, or secrecy may leave war, arms-race, or governance risks unresolved. The molecule therefore preserves the dilemma instead of resolving it.

**T-instance.** Let $`\mathcal H_{\mathrm{Op}}`$ be a finite composable USD chain containing the subdivided local record $`\mathbb E_{\mathrm{Op}}`$ and the stabilized molecule $`\mathrm{SMol}_{\mathrm{Op}}`$ as typed factors. Temporal turnover gives

```math
\mathbb T_{\mathrm{Op}}
  \mathrel{:=}
  \mathsf{TComp}(\mathcal H_{\mathrm{Op}}).
```

This reverses the reading of the record chain. Forward, the Oppenheimer molecule reads:

```math
\text{theory discovers possibility}
  \longrightarrow
  \text{policy must decide action}.
```

Turned over, it reads:

```math
\text{public consequence}
  \longrightarrow
  \text{theoretical practice is judged by what it enabled}.
```

The turned record has the same carrier gap, but its vocabulary can now be read as a forum problem. In the forum normal form, theoretical discovery is replaced by contradiction discovery, and public-policy action is replaced by public authority over the speaker:

```math
\text{contradiction is found}
  \;\Longrightarrow\;
  \text{the forum must decide whether to rewind or expel}.
```

This is the no-rewind forum dilemma. A truth-seeking argument treats contradiction as a repair point. An authority-protecting forum may treat the same contradiction as disqualification. The boundary witness is the same shape as in the Oppenheimer molecule: a successful epistemic act creates an irreversible practical burden.

**U-instance.** Let

```math
\rho_{\mathrm{Forum}}:
  \mathcal L_{\mathrm{no\text{-}rewind}}
  \to
  \mathcal G_{\mathrm{Forum}}
```

be the context morphism from the local no-rewind forum pattern to a global forum schema. When the relevant lifted Kan extension exists, the upward image of the turned record is the Socratic trial schema:

```math
\mathbb U_{\mathrm{Op}}
  \mathrel{:=}
  \mathsf{UComp}^{\exists}_{\rho_{\mathrm{Forum}}}(\mathbb T_{\mathrm{Op}})
  \leadsto
  \mathrm{Trial}_{\mathrm{Socrates}}.
```

In this image, the theoretical side becomes Socratic examination: questions expose contradictions and force interlocutors back to their premises. The public-policy side becomes the authority of the Athenian forum: the city can treat the exposed instability not as an invitation to rewind the argument, but as corruption, impiety, or civic danger. The mapping is:

```math
\begin{array}{ccl}
  \text{nuclear possibility} &\mapsto& \text{exposed contradiction},\\
  \text{state action} &\mapsto& \text{public judgment},\\
  \text{irreversible use} &\mapsto& \text{irreversible punishment},\\
  \text{policy responsibility} &\mapsto& \text{forum authority},\\
  \text{unresolved residue} &\mapsto& \text{loss of rewind rights}.
\end{array}
```

The coverage certificate for the Oppenheimer test is the six-causeton-covered agenda

```math
\begin{aligned}
  \mathcal A_C
  &=
  \{\mathsf{CComp}_{\mathcal I_{\Theta}}
    (\widehat{\mathbb H}_T,\widehat{\mathbb H}_P)\},\\
  \mathcal A_D
  &=
  \{\mathsf{DComp}_{\rho_{\mathrm{Op}}}(\mathbb O)\},\\
  \mathcal A_E
  &=
  \{\mathsf{EComp}_{m_{\mathrm{act}}}
    (\mathbb L_{\mathrm{Op},\mathrm{possible},\mathrm{responsible}})\},\\
  \mathcal A_S
  &=
  \{\mathsf{SComp}(A_{\mathrm{theory}},B_{\mathrm{practice}};
    \Delta_{\mathrm{Op}}^*)\},\\
  \mathcal A_T
  &=
  \{\mathsf{TComp}(\mathcal H_{\mathrm{Op}})\},\\
  \mathcal A_U
  &=
  \{\mathsf{UComp}^{\exists}_{\rho_{\mathrm{Forum}}}
    (\mathbb T_{\mathrm{Op}})\}.
\end{aligned}
```

The agenda may be saturated in any order, and the displayed dependencies only say which generated records are available as inputs to other typed causeton instances. A stronger historical or moral conclusion is not produced by the saturation itself. The transformation is therefore not a metaphorical jump from physics to Athens. It passes through the common S-molecular form:

```math
\text{epistemic success}
  \mathrel{\leadsto_{\mathsf{USD}}}
  \text{practical authority over irreversible consequence}.
```



<div class="remark">

**Remark 80** (No proof of historical identity). The Oppenheimer test licenses a structural comparison, not a USD-free historical identity. It does not say that Oppenheimer was Socrates, that the Manhattan Project was a trial, or that Athenian law and nuclear policy were the same institution. It says that both records can realize the same no-rewind pattern: a practice whose internal norm is correction by truth is recoded by public authority as a source of irreversible judgment. Any stronger historical or moral conclusion requires an explicit descent license.

</div>

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

1.  Refine preferred subclasses of coherence contracts $`\kappa_F`$ and prove closure under all six causeton composition–decomposition types in nontrivial models.

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

The six causetons are typed composition–decomposition pairs backed by ordinary categorical constructions or explicit existence assumptions, and each causeton is defined only when it preserves the stance-lift invariant through $`q`$. The resulting system can guide interpretation and proof search while remaining conservative over the base language for USD-free conclusions.

<div class="thebibliography">

99

Saunders Mac Lane. *Categories for the Working Mathematician*. Springer, 1971.

Francis Borceux. *Handbook of Categorical Algebra, Volumes 1–3*. Cambridge University Press, 1994.

Peter T. Johnstone. *Sketches of an Elephant: A Topos Theory Compendium*. Oxford University Press, 2002.

Alexander Grothendieck. Revêtements ètales et groupe fondamental. In *SGA 1*, Lecture Notes in Mathematics 224, Springer, 1971.

Alfred Tarski. A lattice-theoretical fixpoint theorem and its applications. *Pacific Journal of Mathematics*, 5(2):285–309, 1955.

Isaac Newton. *Philosophiæ Naturalis Principia Mathematica*. .

Albert Einstein. Zur Elektrodynamik bewegter Körper. *Annalen der Physik*, 322(10):891–921, 1905.

Albert Einstein. Die Grundlage der allgemeinen Relativitätstheorie. *Annalen der Physik*, 354(7):769–822, 1916.

Henry DeWolf Smyth. *Atomic Energy for Military Purposes*. Princeton University Press, 1945. <https://www.osti.gov/opennet/manhattan-project-history/publications/smyth_report.pdf>.

James Franck et al. The Franck Report: A Report to the Secretary of War. June 1945. <https://sgp.fas.org/eprint/franck.html>.

Plato. *Apology*. Translated by Benjamin Jowett. Project Gutenberg. <https://www.gutenberg.org/ebooks/1656>.

Satoshi Nakamoto. Bitcoin: A Peer-to-Peer Electronic Cash System. . <https://bitcoin.org/bitcoin.pdf>.

Satoshi Nakamoto. Re: Wikileaks contact info? BitcoinTalk, December 5, 2010. Archived by the Satoshi Nakamoto Institute: <https://satoshi.nakamotoinstitute.org/posts/bitcointalk/523/>.

Satoshi Nakamoto. Added some DoS limits, removed safe mode (0.3.19). BitcoinTalk, December 12, 2010. Archived by the Satoshi Nakamoto Institute: <https://satoshi.nakamotoinstitute.org/posts/bitcointalk/543/>.

BitMEX Research. Does Satoshi have a million bitcoin? August 20, 2018. <https://www.bitmex.com/blog/satoshis-1-million-bitcoin>.

</div>
