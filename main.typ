#import "@preview/ctheorems:1.1.2": *
#show: thmrules.with(qed-symbol: $square$)

#set par(justify: true)

#let card(x) = $abs(#x)$

// #set page(width: 16cm, height: auto, margin: 1.5cm)
#set heading(numbering: "1.1.")

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#ffeeff"))
#let adj = math.tilde
#let pih = $hat(pi)$
#let clo(L) = math.overline(L)

#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#let ihom = $g$
#let lip = $f$

= Main result

Let $G$ be the co-normal product of $n$ graphs $G_i, i in [n]$, where each $G_i$ has
maximal vertex degree exactly 2 and at least two connected components. Define $S subset.eq G$ to be the subgraph
induced by those vertices $v in G$ for which $exists i in [n], deg(pi_i v) = 2$ and let $E subset.eq S$ be the subgraph induced by $forall i in [n], deg(pi_i v) = 2$. We also define $S_i = {v in G_i : deg(v) = 2}$.

For each vertex $x in E$ we define $T(x) = {y in E : forall i in [n], pi_i y = pi_i x or pi_i y adj pi_i x}$. It may be noted that $T(x)$ is a clique of $2^n$ elements.

We would like to prove the following theorem:

#theorem[Let $ihom : G -> G$ be an injective homomorphism. Then there exists a permutation $sigma: [n]->[n]$ and a family of local isomorphisms $ihom_i : S_i -> S_(sigma(i))$ such that for all $x in G$ and all $i in [n]$, we have $pi_i x in S_i => pi_(sigma(i))ihom(x) = ihom_i (pi_i x)$.] <thm:factors>

#lemma[
  A clique of $2^n-1$ points in $G$ has at most one extension
to a clique of $2^n$ points.
] <lem:clique-ext>

#proof[
  Induction on $n$. The case with $n=1$ is clear by inspection.

  First note that if the statement is true for a graph $G$, then the maximal clique size for $G$ is at most $2^n$. If there were a clique of $2^n+1$ points, then every subclique of size $2^n - 1$ would have at least two distinct extensions to a clique of size $2^n$.

  Consider an enumerated family $(x_i)_(i in [2^n])$ of pairwise adjacent
  vertices in $G$. We want to show that any vertex $q in G$ that is
  adjacent to all vertices $x_i$ with $i > 0$ is equal to $x_0$.

  Partition the family into $A union.dot B$ such that $A$ is any maximal
  subset of the family such that $pi_0 A$ is an edgeless graph.

  Note two things: $pi_0 B$ is also edgeless, and $card(A) = card(B) = 2^(n-1)$. From this, it follows that $B$ also satisfies the defining condition of $A$.

  Let's verify the first observation. If any element $pi_0 x$ of $pi_0 B$ were disconnected from $pi_0 A$, then $A$ could be extended to $A union {x}$, so $A$ would not be maximal. This implies that every element of $pi_0 B$ is connected to some element of $pi_0 A$, so $pi_0 B subset.eq N(pi_0 A)$. Since $pi_0 A$ is edgeless, then $N(pi_0 A)$ is edgeless,
  thus $pi_0 B$ is edgeless.

  Now the second observation. Since $A$ is maximal among those subsets $S$ for which $pi_0 S$ is edgeless, and $pi_0 B$ is edgeless, we have $card(A) >= card(B)$, from which $card(A) >= 2^(n-1)$. Now, since $forall a, a' in A, a adj a'$ while $pi_0 a adj.not pi_0 a'$, we must have $pih_0 a adj pih_0 a'$. This means that $pih_0 A$ is a clique of at least $card(A) >= 2^(n-1)$ points in $pih_0 G$ (we have that $card(pih_0 A) = card(A)$ since $a != a' => a adj a' => pih_0 a adj pih_0 a' => pih_0 a != pih_0 a'$). By the induction assumption, the largest clique size in $pih_0 G$ is at most $2^(n-1)$, so $card(A) >= 2^(n-1) >= card(pih_0 A) = card(A)$, hence $card(A) = 2^(n-1)$.

  Having shown that $B$ is also maximal w.r.t. A's defining condition, we have that $pi_0 A subset.eq N(pi_0 B)$. Since $N^2(S) subset.eq S$ for a subset $S$ of a graph of maximal degree 2, we have that $N(pi_0 A) subset.eq pi_0 B$, from which $pi_0 B = N(pi_0 A)$ and $pi_0 A = N(pi_0 B)$.

  Assume WLOG that $x_0 in A$. If $pi_0 q$ had no edge to $pi_0 B$, then
  $pih_0 B union.dot {pih_0 q}$ would form a clique of $2^(n-1)+1$ elements
  in $pih_0 G$, which is impossible. Thus $pi_0 q adj pi_0 b$ for some $b in B$. It follows that $pi_0 q$ has no edge to $pi_0 A$, from which $pih_0 q$ has edges to all members of $pih_0 (A - {x_0})$. This means $pih_0 (A - {x_0})$ is a clique of $2^(n-1)-1$ points in $pih_0 G$ which can be extended by $pih_0 q$ or by $pih_0 x_0$. By the induction assumption, this means $pih_0 q = pih_0 x_0$.
  
  Running the same argument by some index $j > 0$, we also have that $pih_j q = pih_j x_0$. Since these two projections cover all components, we must have $q = x_0$.
]
#let xfam = $(x_i)_(i in [2^n])$
#let yfam = $(y_i)_(i in [2^n])$

From here on, $ihom colon G -> G$ be an injective homomorphism and let $x_0 in E$. Let $xfam = T(x_0)$ and define $y_i = ihom(x_i)$.


#lemma[
  Let there be exactly one $k$ such that $pi_k x_a adj pi_k x_b$. Then there is exactly one $m$ for which $pi_(m) y_a adj pi_(m) y_b$ and $pih_(m) y_a = pih_(m) y_b$.
  ] <one-component>

#proof[
  Since $ihom$ is a homomorphism and $x_a adj x_b$, we have $y_a adj y_b$, so $y_a, y_b$ are adjacent in at least one component. Note also that $yfam$ is a clique in $G$.

  Suppose $y_a, y_b$ differ in at least two components, and let the first two of these have indices $i, j$.

  Let $A_i union.dot B_i$ be a partition of $yfam$ such that $pi_i A_i$ is maximal and edgeless, and $y_a in A_i, y_b in B_i$. To prove that such a partition exists, it is sufficient to find any $y_c$ such that $pi_i y_c adj pi_i y_b$, start with ${y_a, y_c} subset.eq A_i$ and extend $A_i$ to maximality (noting that $pi_i y_a != pi_i y_b$ implies $pi_i y_a adj.not pi_i y_c$). Such a $y_c$ exists, since any partition of $yfam$ into two maximal $pi_i$‑edgeless sets consists of two nonempty sets, one of which contains $y_b$, and any member of the other component can be $y_c$.
  Also construct an analogous partition $A_j union.dot B_j$ for $pi_j$.

  Let $k$ be the index for which $pi_k x_a adj pi_k x_b$. By the definition of $T$, this is the unique index at which $pi_k x_a != pi_k x_b$, so $pih_k x_a = pih_k x_b$. Fix $v in G$ such
  that $pih_k v = pih_k x_a, pih_k x_b$, and $pi_k v != pi_k x_a, pi_k x_b$. Note that $ihom(v)$ has edges to all of $yfam$ except possibly for $y_a, y_b$.

  Suppose that $pi_i ihom(v)$ has an edge to $pi_i A_i$. This implies $pi_i ihom(v) in N(pi_i A_i) = pi_i B_i$,
  // ref here?
  from which $pih_i ihom(v)$ forms a clique with $pih_i (B_i - {y_b})$. By @lem:clique-ext this implies that $pih_i ihom(v) = pih_i y_b$, from which $pi_j ihom(v) = pi_j y_b$. From this, we have that $pih_j ihom(v)$ forms a clique with $pih_j (B_j - {y_b})$, which implies by @lem:clique-ext that $pih_j ihom(v) = pih_j y_b$. Since $pih_i ihom(v) = pih_i y_b$ and $pih_j ihom(v) = pih_j y_b$, we have $ihom(v) = y_b = ihom(x_b)$, from which $v = x_b$, which contradicts our choice of $v$.

  Consequently, $pi_i ihom(v)$ has no edge to $pi_i A_i$, and by symmetrical argument it has no edge to $pi_i B_i$ either. From these, we have that $pih_i ihom(v)$ forms a clique with $pih_i (A_i - {y_a})$ and with $pih_i (B_i - {y_b})$, which implies by @lem:clique-ext that $pih_i y_a = pih_i ihom(v) = pih_i y_b$, so $pi_j y_a = pi_j y_b$, contradicting our choice of $j$ and thus our claim that $y_a, y_b$ differ in at least two components.

  Since $y_a$ and $y_b$ are adjacent in at least one component and differ in at most one component, these bounds must be saturated and exactly one component accounts for both, which is the $m$ at which $pi_(m) y_a adj pi_(m) y_b$ and $pih_(m) y_a = pih_(m) y_b$.
]

@one-component can be interpreted as saying that $ihom$ descends to an injective homomorphism of type $T(x_0) -> yfam$, where the domain and codomain are interpreted as subgraphs of $G' = square.big_(i in [n]) G_i$, which is the Cartesian product of the component graphs $G_i$. We now desire to show that this is a componentwise isomorphism.

// If $ihom$ failed to be an isomorphism in $G'$ between $T(x_0)$ and $yfam$, then there would be some $x_i$ for which $deg(ihom(x_i)) > deg(x_i) = n$, since an injective homomorphism with finite codomain can only fail to be an isomorphism by adding edges. By the pigeonhole principle, this would imply there is some index $j in [n]$ and indices $u != v in [2^n]$ such that $pi_j ihom(x_i) adj pi_j ihom(x_u), pi_j ihom(x_v)$. From @one-component, this would imply that $pih_j ihom(x_i) = pih_j ihom(x_u) = pih_j ihom(x_v)$, and since $G_j$ has maximal vertex degree 2, we also have that $pi_j ihom(x_u) = pi_j ihom(x_v)$. Consequently, $ihom(x_u) = ihom(x_v)$, from which $x_u = x_v$, contradicting our choice of $u, v$.

We first show that $ihom$ is an isomorphism between $T(x_0)$ and $yfam$ in $G'$. Since $T(y_0)$ is closed under the operation of swapping any component for its adjacent one, and every member of $yfam$ is related to $y_0$ by a sequence of such operations (by repeated application of @one-component along a path from $x_0$ to the preimage of the desired member of $yfam$), we must have that each vertex of $yfam$ is a vertex of $T(y_0)$, and since $T(y_0)$ is a full subgraph of $G'$, we have that $yfam$ is a subgraph of $T(y_0)$. This implies that $deg_(T(y_0))(y_i) <= n$ for each $i in [2^n]$, and by the fact that an injective homomorphism cannot decrease degree, we must have that $deg_(T(y_0))(y_i) = n$, from which $yfam = T(y_0)$ in $G'$. Since every edge $x_i adj x_j$ induces an edge $y_i adj y_j$, and $deg(x_i) = deg(y_i)$, we must have that every edge in $T(y_0)$ is induced by an edge in $T(x_0)$, from which $x_i adj x_j <=> y_i adj y_j$. Since $ihom$ is a bijection with finite codomain, this is sufficient for it to be an isomorphism.

That this isomorphism arises from a componentwise isomorphism (up to permutation of components) follows from e.g. Theorem 6.8 in @handbook.

Since these isomorphisms must glue compatibly across all of $E$, we have that there exists a permutation $sigma : [n] -> [n]$ and a family of local isomorphisms $ihom_i : S_i -> S_sigma(i)$ such that for all $x in E$, $pi_sigma(i) ihom(x) = ihom_i (pi_i x)$.

We would like to extend this slightly to the case of vertices outside of $E$ to finish our proof of @thm:factors.

#lemma[
  Let $q in G$ and $i in [n]$ be such that $pi_i q = pi_i x_0$. Then $pi_sigma(i) ihom(q) = pi_sigma(i) ihom(x_0) = ihom_i (pi_i x_0)$.
  ] <lem:interior>

#proof[
  This is trivial for the $n=1$ case (since then $q in E$ or the claim is vacuous), so we will assume $n > 1$.

  Let $(x_j)_(j in J)$ be the subfamily of $xfam$ for that satisfies $forall j in J, pi_i x_j adj pi_i x_0$. We then have that $card(J) = 2^(n-1)$ and $forall j in J, pi_sigma(i)y_j adj pi_sigma(i) y_0$. Note also that since $q adj x_j$, we have $ihom(q) adj y_j$ for each $j in J$.

  Suppose that $pi_(sigma(i)) ihom(q) != pi_(sigma(i)) y_0$. This implies that $pi_sigma(i)ihom(q) adj.not pi_sigma(i)y_j$ for each $j in J$, from which (by way of $ihom(q) adj y_j$) we must have $pih_sigma(i)ihom(q) adj pih_sigma(i)y_j$. This induces a clique of $2^(n-1)+1$ vertices ${pih_sigma(i)ihom(q)} union {pih_sigma(i)y_j : j in J}$ in $pih_(sigma(i))G$, which is impossible by @lem:clique-ext. We thus have that $pi_sigma(i) ihom(q) = pi_sigma(i)y_0 = ihom_i (pi_i x_0)$.
] 

Since for each $x_i in S_i$ there exists an $x in E$ with $pi_i x = x_i$, @lem:interior concludes our proof of @thm:factors.


= Applications to plasticity

We begin with a straightforward corollary of @thm:factors.

#theorem[
  Let $Z := plus.circle.big_(i in [n]) X_i$ and let $ihom : B_Z -> B_Z$ be a non-contractive function. Then there is some permutation $sigma : [n] -> [n]$ and a family of non-contractive functions $ihom_i : S_i -> S_(sigma(i))$ such that for all points $x in B_Z$ and all $i in [n]$ we have 
  $pi_i x in S_i => pi_(sigma(i)) G(x) = ihom_i (pi_i x)$.
] <thm:banach-factors>

@thm:banach-factors follows from applying @thm:factors to the graph with vertices in $B_Z$, edges ${{x,x'} : norm(x-x')=2}$ and $ihom$ as the injective homomorphism.

This can be applied to prove some more natural theorems concerning plasticity.

#theorem[
  Let $lip: B_Z -> B_Z$ be a 1-Lipschitz bijection. If $lip$ maps extreme points to extreme points, or $lip(S_Z) subset.eq S_Z$, then $lip$ is an isometry.
] <thm:natural>

// cite Leo here

We begin with some graph-theoretic lemmas mirroring the conditions of @thm:natural.

#lemma[
  Let $ihom, G, ihom_i, S, E$ be as in @thm:factors. If $E subset.eq ihom(E)$ or $S subset.eq ihom(S)$, then $ihom$ is an isomorphism.
]

#lemma[
  Each $ihom_i$ is a bijection.
] <lem:bijective-factors>

#proof[
  It is enough to show that each $ihom_i$ is surjective, i.e. that $y in ihom_i (S_i)$ for any $y in S_(sigma(i))$.

  We shall first consider the case where $S subset.eq ihom(S)$.

  First, fix a point $q in S$ such that $pi_sigma(i) q = y$ and $pi_j q in.not S_j$ for all $j != sigma(i)$. By $S subset.eq ihom(S)$, we may fix $x in S$ such that $ihom(x) = q$. Let $J = {j in [n] : pi_j x in S_j}$. From @thm:factors, we know that $pi_sigma(j) ihom(x) in S_sigma(j)$ for all $j in J$. It follows that $J subset.eq {i}$. Since $x in S$, we have that $J$ is nonempty, from which $J = {i}$. This allows us to use @thm:factors to conclude that $ihom_i (pi_i x) = pi_sigma(i) ihom(x) = y$, so $y in ihom_i (S_i)$.

  We now consider the case where $E subset.eq ihom(E)$.

  Fix a point $q in E$ such that $pi_sigma(i) q = y$. Since $q in E$, there is some $x in E$ for which $ihom(x) = q$, and by @thm:factors, we have $ihom_i (pi_i x) = pi_sigma(i) ihom(x) = y$.
]

#lemma[
  $S subset.eq ihom(S)$ implies that $E subset.eq ihom(E)$.
]

#proof[
  Fix any point $y in E$. We aim to construct a point $x in E$ such that $ihom(x)=y$.

  By $S subset.eq ihom(S)$ and @lem:bijective-factors, we have that each $ihom_i$ is a bijection, so we may define $x$ such that $ihom_i (pi_i x) = pi_sigma(i) y$ for each $i in [n]$. By @thm:factors, we have that $pi_sigma(i) ihom(x) = ihom_i (pi_i x) = pi_sigma(i) y$, so $ihom(x) = y$ as desired.

  // I have no idea whether the converse holds - I should try
  // pushing the formalism at some point.
]

We now proceed with more geometric results for which a graph-theoretic analogue has not been recovered.

#definition[
  Given a $1$-Lipschitz bijection $lip : B_Z -> B_Z$, the non-contractive map $ihom := lip^(-1)$ is said to be _homogeneous in $k$ components_ if, for all $J subset.eq [n]$ with $card(J) <= k$ and for all $x in B_Z$ such that $x$ has norm $1$ on components $[n] - J$, we have $forall i in [n], pi_sigma(i) ihom(x) = norm(pi_i x)ihom_i ((pi_i x)/norm(pi_i x))$, where the expression on the right-hand side is understood to be 0 whenever $norm(pi_i x) = 0$. Analogously, we say that $lip$ is homogeneous in $k$ components when, for the same $J$ and $x$, we have $forall i in [n], pi_(sigma^(-1)(i)) lip(x) = norm(pi_i x) lip_i ((pi_i x)/norm(pi_i x))$.
]

= Auxiliary results

#let induced = $f'$

#theorem[Suppose there are Banach spaces $X, Y$, and a non-expansive bijection $lip : B_X -> B_Y$ such that $lip$ is not an isometry. Then there is a Banach space $Z$ and a non-expansive bijection $induced : B_Z -> B_Z$ such that $induced$ is not an isometry.]

#proof[
  Let $C_i$ be a Banach space for each $i in ZZ$, such that $C_i = X$
  for $i < 0$ and $C_i = Y$ for $i >= 0$. Take $Z colon.eq plus.circle.big_(i=-infinity)^infinity C_i$ with the $infinity$-norm. Define $induced : B_Z -> B_Z$ by $pi_i induced(z) = pi_(i-1) z$ for $i != 0$ and $pi_0 induced(z) = lip(pi_(-1)z)$.

  It is clear by inspection that the codomain of $induced$ is correct and that it is a non-expansive bijection. That it is not an isometry follows from considering the natural inclusions of two points $x, x' in C_(-1)$ into $Z$, where $norm(induced(x) - induced(x')) = norm(lip(x)-lip(x')) < norm(x-x')$.
]

#lemma[Let $X$ be a Banach space and let $A subset.eq X$ be closed under scaling by rationals. Then $clo(A sect B_X) = clo(A) sect B_X$.] <rat-scaling>

#proof[Since $A sect B_X subset.eq clo(A) sect B_X$ and the latter is closed, we have $clo(A sect B_X) subset.eq clo(A) sect B_X$. It thus suffices to show the opposite inclusion.

Fix any $a in clo(A) sect B_X$ and a sequence $a_i in A$ that converges to $a$. If $norm(a) < 1$, then $a_i in A sect B_X$ for all sufficiently large $i$, from which $a in clo(A sect B_X)$. If $norm(a) = 1$, then choose a sequence of rationals $q_i in QQ$ such that $abs(q_i) <= 1/norm(a_i)$ for all sufficiently large $i$, and $q_i -> 1$. This is possible since $norm(a_i) -> norm(a) = 1$. We then have $q_i a_i in A sect B_X$ for all sufficiently large $i$, and $q_i a_i -> a$, so $a in clo(A sect B_X)$. We thus have that $clo(A) sect B_X subset.eq clo(A sect B_X)$, so $clo(A) sect B_X = clo(A sect B_X)$.
]

#let restr = $rho$

#theorem[Let $X$ be a Banach space and $lip: B_X -> B_X$ be a non-expansive homeomorphism that is not an isometry. Then $X$ has a separable closed subspace $Y$ such that $lip(B_Y) = B_Y$ and $restr colon.eq lip|_B_Y : B_Y -> B_Y$ is a non-expansive homeomorphism that is not an isometry.]

#proof[
  Let $x, x' in B_X$ be points for which $norm(lip(x)-lip(x')) < norm(x-x')$.

  Define the set function $H colon 2^X -> 2^X$ as $ H(S) = lip(S sect B_X) union lip^(-1)(S sect B_X) union QQ dot S union (S+S). $ Note that $H(S)$ is countable whenever $S$ is countable, $S subset.eq H(S)$. Moreover, since $H$ is a union of set functions which are monotonic and continuous with respect to ascending chains of set inclusions, then $H$ is monotonic and continuous with respect to ascending chains also.

  Define $S_0 = {x,x'}$ and $S_(n+1) = H(S_n)$ for $n in NN$. Let $L = union.big_(n=0)^infinity S_n.$ Since $L$ is the limit of an ascending chain, we have $H(L) = union.big_(n=0)^infinity H(S_n) = union.big_(n=0)^infinity S_(n+1) = L$, so $L$ is a fixed point of $H$. Since $L$ is a countable union of countable sets, then $L$ is itself countable.

  Since $L$ is a fixed-point of $H$, we have that it is closed under addition and rational scaling, from which $clo(L)$ is closed under addition and real scaling, so $clo(L)$ is a closed subspace of $X$.
  Since $L$ is countable, $clo(L)$ is separable. By @rat-scaling,
  we have that $clo(L sect B_X) = clo(L) sect B_X = B_(clo(L))$.

  Since $lip$ is continuous and $L$ is closed under $lip$, we have
  that $lip(clo(L sect B_X)) subset.eq clo(lip(L sect B_X)) subset.eq clo(L sect B_X)$, so $lip(B_clo(L)) subset.eq B_clo(L)$. Analogously, we have $lip^(-1)(B_clo(L)) subset.eq B_clo(L)$. From these, we have $lip(B_clo(L)) = B_clo(L)$, so $restr$ is a well-defined non-expansive homeomorphism. Since $x, x' in B_clo(L)$, we also have that $restr$ is not an isometry.
]

#bibliography("refs.yml")