# Counting DD-Graphs: A Recursive Formula for $N(m,n)$

*Derivation, proof, and computational verification*

---

## 1. Introduction

### 1.1 The objects being counted

Fix two disjoint sets of vertices:

* **Partition 1** — $P_1 = \{a_1,\dots,a_m\}$, of size $m$;
* **Partition 2** — $P_2 = \{v_1,\dots,v_n\}$, of size $n$.

The vertices are **labeled**: they have names and are distinguishable, so we are counting *edge sets*, not graphs up to isomorphism — two graphs are distinct as soon as their edge sets differ.

We work with **directed graphs** (*digraphs* for short): every edge is an ordered pair, and we write the pair $(u,w)$ for the edge $u \to w$ pointing from $u$ to $w$. Two pieces of standard vocabulary are used throughout:

* the **in-degree** $\deg^-(v)$ of a vertex $v$ is the number of edges pointing *into* $v$, and its **out-degree** $\deg^+(v)$ is the number of edges *leaving* $v$;
* a **source** is a vertex with $\deg^- = 0$ (nothing points to it), and a **sink** is a vertex with $\deg^+ = 0$ (it points to nothing).

A **DD-graph** on $(m,n)$ is a directed graph $G$ on the vertex set $P_1\cup P_2$ such that:

1. **(Bipartite)** every edge joins a $P_1$ vertex to a $P_2$ vertex — in either direction ($a\to v$ or $v\to a$); there are no edges inside a partition;
2. **(Acyclic)** $G$ contains no directed cycle — it is a *DAG*, a directed acyclic graph;
3. **(Boundary condition)** every source and every sink of $G$ lies in $P_1$.

We refer to conditions 1–3 collectively as the **DD conditions**. $N(m,n)$ denotes the number of DD-graphs on $(m,n)$.

Note that an isolated vertex (no edges at all) is simultaneously a source and a sink; condition 3 therefore allows isolated vertices in $P_1$ but forbids them in $P_2$.

**Example.** Take $m=2$, $n=1$. The graph

$$a_1 \longrightarrow v \longrightarrow a_2$$

is a DD-graph: it is bipartite and acyclic, $v$ has an incoming and an outgoing edge, and the unique source ($a_1$) and unique sink ($a_2$) both lie in $P_1$. By contrast, the single edge $a_1\to v$ alone is *not* a DD-graph ($v$ would be a sink in $P_2$), and completing it with $v\to a_1$ instead of $v \to a_2$ creates the directed cycle $a_1 \to v \to a_1$. In fact $N(2,1)=2$: the only other DD-graph is the mirror chain $a_2\to v\to a_1$.

### 1.2 A crucial reformulation

Condition 3 quantifies over *sources and sinks*, which sound like global objects. It is equivalent to a purely **local degree condition** on $P_2$:

> **Lemma 1 (reformulation).** *A bipartite digraph $G$ satisfies condition 3 if and only if every vertex of $P_2$ has in-degree $\ge 1$ **and** out-degree $\ge 1$. Vertices of $P_1$ are unconstrained.*

*Proof.* "All sources lie in $P_1$" says exactly that no $P_2$ vertex has in-degree $0$; "all sinks lie in $P_1$" says exactly that no $P_2$ vertex has out-degree $0$. Condition 3 puts no restriction on $P_1$ vertices, which are always allowed to be sources or sinks. $\blacksquare$

So a DD-graph is a bipartite DAG in which **every $P_2$ vertex is internal**: it has at least one incoming and at least one outgoing edge. This reformulation drives the whole derivation, because a condition of the form "vertex $v$ has degree $\ge 1$" is the kind of condition that inclusion–exclusion removes cleanly (§4).

### 1.3 Trivial values, and why no closed form is expected

* $N(m,0)=1$ for all $m\ge 0$: with no $P_2$ vertices there are no admissible edges at all, so the empty graph on $P_1$ is the only graph, and it is a valid DD-graph (all its sources/sinks are in $P_1$).
* $N(0,n)=0$ for $n\ge 1$: a $P_2$ vertex needs an incoming edge from $P_1$, which is empty.
* $N(1,n)=0$ for $n\ge 1$: a $P_2$ vertex $v$ would need both $a_1\to v$ and $v\to a_1$, a $2$-cycle.

Even for *unrestricted* labeled DAGs, no closed-form counting formula is known: the classical result of Robinson (1973) — see §11; **no familiarity with it is assumed**, the technique is rederived from scratch in §4–5 — is a *recurrence*, not a closed formula. Robinson counts all labeled DAGs by inclusion–exclusion over which vertices are forced to be sources; §5.1 adapts exactly that idea to the bipartite setting. Our problem strictly contains that difficulty, so we aim — as anticipated — for a **recursive formula**.

### 1.4 Roadmap

* **§2** states the two main results and the verified table of values. It is meant for reference; first-time readers may prefer to read §3 first.
* **§3** develops the layer intuition behind the problem and proves the structural lemmas (how DD-graphs decompose into alternating layers, and what deleting the sink layer leaves behind).
* **§4** builds the inclusion–exclusion toolkit from first principles.
* **§5** proves Theorem 1 (the streamlined system) and **§6** proves Theorem 2 (the literal layer recursion).
* **§7** collects base cases and independently checkable sanity anchors.
* **§8** documents the computational verification.
* **§9** treats a variant count (DD-graphs over all sub-partitions) used by a TLA+ specification.
* **§10** eliminates the auxiliary functions and derives *self-contained* recurrences whose right-hand sides use only $N$ (resp. $\widehat N$) at smaller indices.
* **§11** lists the code; **§12** gives references.

### 1.5 Notation summary

| Symbol | Meaning | Where |
|---|---|---|
| $P_1, P_2$; $m, n$ | the two vertex sets and their sizes | §1.1 |
| $(u,w)$ | the directed edge $u \to w$ | §1.1 |
| $\deg^-(v),\ \deg^+(v)$ | in-degree, out-degree of $v$ | §1.1 |
| source / sink | vertex with $\deg^-=0$ / $\deg^+=0$ | §1.1 |
| $N(m,n)$ | number of DD-graphs | §1.1 |
| $E(m,n)$ | number of all bipartite DAGs (no degree constraints) | §2.1 |
| $D(m,n)$ | number of bipartite DAGs with all sources in $P_1$ | §2.1 |
| $a_s(m,n),\ b_s(m,n)$ | sink-count-refined classes for the layer recursion | §2.2 |
| $\varphi(p,q,r)$ | count of constrained bipartite edge sets | §2.2, §6.3 |
| $\beta_j(m),\ \gamma_j(m)$ | the integers $2^{m+1}-2^j-2^{m-j}$ and $2^{m+1}-2^{j+1}-2^{m-j}$ | §10 |
| $G-T$ | graph obtained from $G$ by deleting the vertices of $T$ and all edges touching them | §3.3 |
| $\rho(v)$; $L_k$ | length of the longest path starting at $v$; the $k$-th layer $\{v:\rho(v)=k\}$ | §3.2 |
| $[\![P]\!]$ | $1$ if the statement $P$ holds, else $0$ | §4 |
| $\widehat N(m,n)$ | number of DD-graphs over all sub-partitions | §9 |

---

## 2. Main results

**The shape of the argument.** By Lemma 1, $N(m,n)$ counts bipartite DAGs subject to two families of "degree $\ge 1$" constraints on $P_2$ (in-degrees and out-degrees). The plan of Theorem 1 is: *strip the two constraint families off one at a time by inclusion–exclusion* — first the out-degree constraints (reducing $N$ to $D$), then the in-degree constraints (reducing $D$ to $E$) — and then count the fully unconstrained bipartite DAGs $E$ by a self-recursion obtained by deleting sources. Theorem 2 instead attacks the DD-graphs head-on, repeatedly deleting the set of sinks — we call this *peeling*, made precise in §3 — at the cost of tracking one extra statistic (the number of sinks). Both routes are proved independently and verified against brute force.

*First-time readers may prefer to read §3 (the intuition and the structural lemmas) before the formal statements below.*

### 2.1 Theorem 1 — the streamlined system

Define two auxiliary counting functions on the same labeled bipartite vertex sets:

* $E(m,n)$ — the number of **all** bipartite DAGs (conditions 1–2 only, no degree constraints);
* $D(m,n)$ — the number of bipartite DAGs in which every $P_2$ vertex has in-degree $\ge 1$ (equivalently: all sources lie in $P_1$; sinks unconstrained).

> **Theorem 1.** With $E(0,0)=1$ and, for $(m,n)\neq(0,0)$,
>
> $$E(m,n)\;=\;\sum_{\substack{0\le j\le m,\;0\le i\le n\\ (j,i)\neq(0,0)}} (-1)^{\,i+j+1}\,\binom{m}{j}\binom{n}{i}\; 2^{\,j(n-i)+i(m-j)}\;E(m-j,\,n-i),$$
>
> the number of DD-graphs is obtained by the two inclusion–exclusion transforms
>
> $$D(m,n)\;=\;\sum_{k=0}^{n} (-1)^k \binom{n}{k}\, 2^{\,km}\; E(m,\,n-k),$$
>
> $$\boxed{\;N(m,n)\;=\;\sum_{k=0}^{n} (-1)^k \binom{n}{k}\, \bigl(2^{m}-1\bigr)^{k}\; D(m,\,n-k).\;}$$

Reading guide for the three formulas (each factor is *proved* in §5; stating its meaning here makes the theorem readable):

* In the $E$-recursion, the sum runs over how many vertices of each partition ($j$ from $P_1$, $i$ from $P_2$) are *forced to be sources*; the factor $2^{\,j(n-i)+i(m-j)}$ counts their free outgoing edges into the rest of the graph (§5.1 accounts for every potential edge).
* In the $D$-transform, $k$ counts $P_2$ vertices *forced to have in-degree $0$*; the factor $2^{km}$ counts their free out-edges towards the $m$ vertices of $P_1$.
* In the boxed $N$-transform, $k$ counts $P_2$ vertices *forced to be sinks*; the factor $(2^m-1)^k$ counts their in-neighbourhoods — a **nonempty** subset of $P_1$ for each, since the in-degree constraint is still in force.

Substituting the $D$-transform into the $N$-transform gives, if a single formula in terms of $E$ is preferred,

$$N(m,n)\;=\;\sum_{k=0}^{n}\sum_{\ell=0}^{n-k} (-1)^{k+\ell}\,\binom{n}{k}\binom{n-k}{\ell}\,\bigl(2^m-1\bigr)^k\, 2^{\ell m}\; E(m,\,n-k-\ell) ,$$

where the product of binomials may also be written as the *multinomial coefficient* $\binom{n}{k}\binom{n-k}{\ell} = \frac{n!}{k!\,\ell!\,(n-k-\ell)!}$ — it counts the ways to split the $n$ vertices of $P_2$ into the $k$ sink-forced ones, the $\ell$ source-forced ones, and the $n-k-\ell$ unconstrained ones (the inner range $\ell \le n-k$ is what produces the constraint $k+\ell\le n$).

The recursion for $E$ needs the single base case $E(0,0)=1$; each term on the right has strictly fewer vertices, so it terminates. **Cost.** The $E$-table has $(m+1)(n+1)$ entries and each entry is a double sum of $O(mn)$ terms, so computing $N(m,n)$ costs $O(m^2n^2)$ big-integer operations — versus the $3^{mn}$ graphs a brute-force enumeration must inspect (three states per cross-partition pair: no edge, or one of the two directions; see §8). A *self-contained* recurrence for $N$ alone — no auxiliary functions on the right-hand side — is derived by elimination in §10.

### 2.2 Theorem 2 — the alternating sink-layer recursion

For the layered form we refine the count by the number of sinks. Two classes appear:

* $a_s(m,n)$ — number of DD-graphs on $(m,n)$ with exactly $s$ sinks (necessarily all in $P_1$);
* $b_s(m,n)$ — number of bipartite DAGs on $(m,n)$ with **all sources in $P_1$, all sinks in $P_2$**, and exactly $s$ sinks.

The class $b$ may look arbitrary, but it is forced on us: it is *precisely* the class of graphs obtained by deleting the sinks of a DD-graph (Lemma 3, §3.3), and deleting the sinks of a $b$-graph gives back a DD-graph — the two classes alternate as the graph is peeled. The number of sinks must be tracked because it governs in how many ways a deleted layer can be glued back (§3.4).

Also define the covering function

$$\varphi(p,q,r)\;=\;\sum_{t=0}^{p} (-1)^t \binom{p}{t}\, \bigl(2^{\,p+q-t}-1\bigr)^{r},$$

which counts the sets of edges between a *left* set of $p+q$ vertices and a *right* set of $r$ vertices such that every right vertex has degree $\ge 1$ and each of the $p$ designated left vertices has degree $\ge 1$ (proved in §6.3). It is called a *covering* function because every right vertex must be covered — touched — by at least one edge; direction plays no role in this count, so "degree" here just means the number of incident edges.

> **Theorem 2.** With base cases $a_0(0,0)=b_0(0,0)=1$, and $a_s(m,n)=0$, $b_s(m,n)=0$ whenever $m+n\ge 1$ and $s$ is outside the ranges written below:
>
> $$a_s(m,n)\;=\;\binom{m}{s}\sum_{s'=0}^{n}\;\bigl(2^{s}-1\bigr)^{s'}\;2^{\,s\,(n-s')}\;\;b_{s'}(m-s,\,n) \qquad (m+n\ge 1,\ 1\le s\le m),$$
>
> $$b_s(m,n)\;=\;\binom{n}{s}\sum_{s''=0}^{m}\;\varphi\bigl(s'',\,m-s'',\,s\bigr)\;\;a_{s''}(m,\,n-s) \qquad (m+n\ge 1,\ 1\le s\le n),$$
>
> and
>
> $$N(m,n)\;=\;\sum_{s=0}^{m} a_s(m,n).$$

Note the asymmetry, which mirrors the peeling: the first recurrence deletes a layer of $s$ sinks lying wholly in $P_1$ (so it lowers $m$, not $n$), the second deletes a layer in $P_2$ (lowering $n$). Each application deletes $s\ge 1$ vertices, so the mutual recursion terminates at $(0,0)$.

### 2.3 Verification summary

Both theorems were implemented and checked against exhaustive brute-force enumeration for all $0\le m,n\le 4$ — **bold** in the table below: 24 of the 25 values by the naive generate-and-filter enumeration, and $N(4,4)=1{,}034{,}882$ by the pruned exhaustive enumerator of §11.1 (an exhaustive search over $50^4 = 6.25$ million candidate configurations, itself validated against the naive enumerator on the other 24 pairs; see §8). The two methods were also checked against each other for all $0\le m,n\le 12$. All assertions pass.

| $m\backslash n$ | 0 | 1 | 2 | 3 | 4 | 5 |
|---:|---:|---:|---:|---:|---:|---:|
| **0** | **1** | **0** | **0** | **0** | **0** | 0 |
| **1** | **1** | **0** | **0** | **0** | **0** | 0 |
| **2** | **1** | **2** | **2** | **2** | **2** | 2 |
| **3** | **1** | **12** | **96** | **588** | **3 264** | 17 292 |
| **4** | **1** | **50** | **1 730** | **45 938** | **1 034 882** | 21 198 770 |
| **5** | 1 | 180 | 22 080 | 2 055 540 | 158 367 360 | 10 755 120 180 |
| **6** | 1 | 602 | 237 602 | 69 613 562 | 16 532 823 362 | 3 386 838 834 842 |

Non-bold entries come from the — now verified — recursion. As a further sanity check, column $n=1$ obeys the closed form $N(m,1)=3^m-2^{m+1}+1$, proved from scratch in §7.2.

---

## 3. Why a layered approach works — analysis of the intuition

The derivation was guided by the following intuition, which this section evaluates and makes rigorous:

> *A DD-graph can be seen as a set of "layers" originating from a topological sort, each layer contained in one of the two partitions. To enumerate all DD-graphs, build the graph layer by layer and count the nodes in each layer and the valid edges between layers. Since all sinks must lie in Partition 1, the final layer consists of Partition-1 vertices only — remove this sink layer and ask what the remaining graph looks like.*

Throughout, "graph" means a bipartite digraph on $(P_1,P_2)$.

### 3.1 Three elementary observations

Three basic facts about directed graphs are used many times; we record them once, with proofs.

> **Observation 1 (cycles avoid boundary vertices).** *Every directed cycle enters and leaves each vertex it visits, so every vertex on a cycle has in-degree $\ge 1$ **and** out-degree $\ge 1$. Consequently, no cycle passes through a source or a sink; and if $T$ is a set of sources (or a set of sinks) of $G$, then $G$ is acyclic **iff** $G-T$ is acyclic.*

*Proof.* The first sentence is immediate. For the last claim: if $G$ is acyclic so is its subgraph $G-T$; conversely, any cycle of $G$ avoids $T$ (its vertices all have in-degree and out-degree $\ge1$), so it survives in $G-T$. $\blacksquare$

> **Observation 2 (walks in a DAG; existence of sources and sinks).** *In a DAG, a directed walk (a sequence of vertices following edges) never repeats a vertex — a repeat would close a directed cycle — so every walk is a path, and since the graph is finite, no walk can be extended forever. Following edges **backwards** from any vertex must therefore stop, at a vertex with no incoming edge: a source. Following edges **forwards** stops at a sink. Hence every nonempty DAG has at least one source and at least one sink, and every non-extendable directed path starts at a source and ends at a sink.*

*Proof.* Only the last clause needs a word: if the last vertex $z$ of a path had an out-edge $z\to y$, then either $y$ is not on the path — and the path extends, contradiction — or $y$ is on the path, and the path segment from $y$ to $z$ followed by $z\to y$ is a cycle, contradiction. $\blacksquare$

> **Observation 3 (edge reversal).** *Reversing every edge of a digraph is an involution (doing it twice restores the graph). It preserves bipartiteness, preserves acyclicity (reversing a cycle yields a cycle), and swaps in-degrees with out-degrees — hence it exchanges sources and sinks.*

### 3.2 Layers of a DAG, and why they alternate between partitions

For a DAG $G$ and a vertex $v$, let $\rho(v)$ be the length (number of edges) of the longest directed path **starting** at $v$. Stratify the vertices into **layers**

$$L_k \;=\; \{\,v : \rho(v)=k\,\}, \qquad k = 0,1,2,\dots$$

Three facts hold in any DAG:

* **(F1)** $L_0$ is exactly the set of sinks: $\rho(v)=0$ means no edge leaves $v$.
* **(F2)** Every edge $u\to w$ satisfies $\rho(u) \ge \rho(w)+1$: prepend the edge $u \to w$ to a longest path from $w$; the result is still a path (if $u$ appeared on the path from $w$, the segment from $u$... rather, the segment from $w$'s path reaching back to $u$ together with $u\to w$ would close a cycle), of length $\rho(w)+1$. So edges always point from a higher layer to a **strictly lower** layer. In particular each layer is an *independent set*: no edge joins two vertices of the same layer.
* **(F3)** Every vertex with $\rho(v)=k\ge 1$ has at least one out-neighbour (a vertex it points to) in $L_{k-1}$: let $v \to w \to \cdots$ be a longest path from $v$; its tail starting at $w$ is a path of length $k-1$, so $\rho(w)\ge k-1$, while F2 gives $\rho(w) \le \rho(v)-1 = k-1$. Hence $\rho(w)=k-1$.

Now suppose all **sinks of $G$ lie in $P_1$** (half of the DD boundary condition).

> **Lemma 2 (alternation).** *In a bipartite DAG whose sinks all lie in $P_1$, the layers alternate:*
> $$L_0, L_2, L_4,\dots \subseteq P_1, \qquad L_1, L_3, L_5,\dots \subseteq P_2 .$$

*Proof.* Take any vertex $v$ and a longest path from it; it has length $\rho(v)$ and, being non-extendable, it ends at a sink $z$ (Observation 2), and $z\in P_1$ by hypothesis. Because every edge joins the two partitions, the partition membership alternates at each step along the path; after $\rho(v)$ steps it reaches $z \in P_1$. Hence $v$ lies in $P_1$ exactly when $\rho(v)$ is even, and in $P_2$ exactly when $\rho(v)$ is odd. $\blacksquare$

This confirms the intuition's premise: a DD-graph *is* organized into layers, each contained in a single partition, with $P_1$ and $P_2$ layers alternating. (The boundary condition is essential: in an arbitrary bipartite DAG a layer may mix both partitions — e.g. two isolated vertices, one in each partition, both lie in $L_0$.)

Here is a concrete DD-graph on $m=3$, $n=2$ (vertices $a_1,a_2,a_3\in P_1$, $v_1,v_2\in P_2$; edges $a_1\to v_1$, $v_1\to a_2$, $a_2\to v_2$, $v_2\to a_3$, and $a_1\to v_2$) together with its layers:

```
   layer            vertex          (all edges point downwards)

   L4 (in P1):        a1 ─────────┐
                       │          │
   L3 (in P2):        v1          │    the "jump" edge a1 → v2
                       │          │    skips two layers: edges
   L2 (in P1):        a2          │    may jump, but always go
                       │          │    strictly down and join
   L1 (in P2):        v2 ◄────────┘    opposite partitions
                       │
   L0 (in P1):        a3               L0 = the sinks, all in P1
```

Beware of one refinement over the naive picture, visible above: edges do **not** only join consecutive layers. The jump edge $a_1\to v_2$ goes from $L_4$ to $L_1$ — it only has to go strictly downwards (F2) and connect opposite partitions (automatic, since layer parities of its endpoints differ). What *is* guaranteed is at least one edge into the *next* layer down from each non-sink vertex (F3).

### 3.3 Peeling the sink layer: what remains

The intuition asks: *remove the final layer — what does the remaining graph look like?* The cleanest "final layer" to remove is $L_0$, the set of **all** sinks. (Removing sinks repeatedly removes exactly $L_0, L_1, L_2, \dots$ in order: after $L_0$ is deleted, the vertices with $\rho=1$ are precisely those that become sinks.) Recall that $G-T$ denotes the graph obtained from $G$ by deleting the vertices of $T$ together with every edge touching them.

> **Lemma 3 (class alternation).** *Let $G$ be a bipartite DAG and $T$ its set of sinks.*
> *(i) If all sources and sinks of $G$ lie in $P_1$ (DD-graph), then $G-T$ is a bipartite DAG with **all sources in $P_1$ and all sinks in $P_2$**.*
> *(ii) If all sources of $G$ lie in $P_1$ and all sinks in $P_2$, with $T\subseteq P_2$ its sink set, then $G-T$ is a **DD-graph** (sources and sinks in $P_1$).*

*Proof.* (i) $T\subseteq P_1$. Since the vertices of $T$ are sinks, the only edges deleted are those *entering* $T$; no remaining vertex loses an incoming edge, so in-degrees are unchanged and the sources of $G-T$ are sources of $G$, hence in $P_1$. Now take a sink $u$ of $G-T$. If $u$ had no out-edges in $G$ it would belong to $T$; so $u$ has out-edges in $G$ and they all end in $T$. Since $T\subseteq P_1$ and edges into $P_1$ leave from $P_2$, we get $u\in P_2$. Thus all sinks of $G-T$ lie in $P_2$. Acyclicity is preserved by deletion.

(ii) Symmetric: now $T \subseteq P_2$; again only edges *into* $T$ are deleted, so in-degrees are unchanged and sources of $G-T$ stay in $P_1$; and a sink $u$ of $G-T$ has all its $G$-out-edges ending in $T\subseteq P_2$, forcing $u\in P_1$. $\blacksquare$

On the figure of §3.2: deleting the sink layer $T=L_0=\{a_3\}$ removes the edge $v_2\to a_3$ — the only out-edge of $v_2$ — so $v_2$ becomes the sink of the remainder, in $P_2$, exactly as Lemma 3(i) predicts.

This answers the intuition's question precisely, and reveals the shape of the recursion: **peeling the sink layer alternates between two classes of graphs** —

$$\underbrace{\text{sources} \subseteq P_1,\ \text{sinks}\subseteq P_1}_{\text{DD-graphs, count } a} \;\xrightarrow{\ \text{peel } T\subseteq P_1\ }\; \underbrace{\text{sources} \subseteq P_1,\ \text{sinks}\subseteq P_2}_{\text{count } b} \;\xrightarrow{\ \text{peel } T\subseteq P_2\ }\; \text{DD-graphs again, } \dots$$

exactly the "layer by layer" build-up the intuition proposes (and the same spirit as Robinson's classical method of counting DAGs via their sources or sinks).

### 3.4 The coupling — and the two ways out

To turn the peeling into a *formula* we must count, for each remainder $G'$, the ways to glue a deleted sink layer $T$ back on. Take first the DD-graph direction, $T\subseteq P_1$ (so the remainder $G'$ is a $b$-graph and the vertices that may send edges into $T$ are the $P_2$ vertices of $G'$). The constraints are:

* every sink of $G'$ must **send** at least one edge into $T$ — otherwise it would remain a sink of the glued graph, and it lies in $P_2$, the wrong partition;
* every other $P_2$ vertex of $G'$ may send an arbitrary (possibly empty) set of edges into $T$.

Each $P_2$ vertex chooses the set of edges it sends into $T$ *independently of the others*: a nonempty subset of $T$ for a sink of $G'$ ($2^{|T|}-1$ options), an arbitrary subset for the rest ($2^{|T|}$ options). Writing $\sigma$ for the number of sinks of $G'$ (all in $P_2$) and $n-\sigma$ for the number of its other $P_2$ vertices, the number of gluings is

$$\bigl(2^{|T|}-1\bigr)^{\sigma} \cdot \bigl(2^{|T|}\bigr)^{\,n-\sigma}.$$

It depends not only on the sizes $(m',n')$ of the remainder but on **how many sinks the remainder has** — consecutive layers are *coupled* through this number. (In the other peeling direction, $T\subseteq P_2$, there is an *additional* constraint: each vertex of $T$ must itself **receive** at least one edge, because sources must stay in $P_1$. With both sides of the glued edge set constrained, the count no longer factors vertex by vertex — that is what the function $\varphi$ of Theorem 2 handles, in §6.3.)

There are two clean resolutions of the coupling:

1. **Track the coupling.** Count remainders refined by their number of sinks. This yields the honest, literal layer recursion — Theorem 2, proved in §6.
2. **Dissolve the coupling by inclusion–exclusion.** Lemma 1 rewrote the DD condition as "every $P_2$ vertex has in-degree $\ge 1$ and out-degree $\ge 1$". Constraints of the form "degree $\ge 1$" can be stripped off by inclusion–exclusion *before* any peeling, reducing $N$ to the unconstrained count $E$, for which the classical source-peeling recursion works without any coupling. This is Theorem 1, proved in §5.

---

## 4. The inclusion–exclusion toolkit

Everything in §5 and §6 rests on two counting lemmas and one decomposition lemma, which we now develop from first principles. The point of the two counting lemmas is always the same: they replace a hard count (graphs whose set of "special" vertices is *exactly* something) by easy counts (graphs in which a *chosen, fixed* set of vertices is forced to be special) at the price of alternating signs. Throughout, $[\![P]\!]$ denotes $1$ if the statement $P$ holds and $0$ otherwise.

> **Lemma 4 (alternating sums over a nonempty set).** *For every finite nonempty set $S$,*
> $$\sum_{\emptyset \neq T \subseteq S} (-1)^{|T|+1} = 1 .$$

*Proof.* By the binomial theorem, $\sum_{T\subseteq S}(-1)^{|T|} = \sum_{k=0}^{|S|}\binom{|S|}{k}(-1)^k = (1-1)^{|S|} = 0$ since $S\neq\emptyset$. Move the $T=\emptyset$ term (equal to $1$) to the other side and negate. $\blacksquare$

Now suppose every object $G$ of a finite family $\mathcal F$ carries a **marked set** $S(G)\subseteq U$ inside some fixed universe $U$. (In all our uses, $\mathcal F$ is a family of graphs and $S(G)$ is a distinguished vertex set of $G$ — its set of sources, or its set of degree-0 offenders.) If every marked set is nonempty, then

$$|\mathcal F| \;=\; \sum_{\emptyset\neq T\subseteq U} (-1)^{|T|+1}\, \#\{\,G\in\mathcal F : T\subseteq S(G)\,\}. \tag{4.1}$$

*Proof of (4.1).* Count the **pairs** $(G, T)$ with $G\in\mathcal F$ and $\emptyset\neq T\subseteq S(G)$, each pair carrying the weight $(-1)^{|T|+1}$, in two ways. Grouping the pairs by $G$: for each fixed $G$ the inner sum is $\sum_{\emptyset\neq T\subseteq S(G)}(-1)^{|T|+1} = 1$ by Lemma 4, so the total is $|\mathcal F|$. Grouping the pairs by $T$: for each fixed nonempty $T\subseteq U$, the objects paired with it are exactly those with $T\subseteq S(G)$, contributing $(-1)^{|T|+1}\,\#\{G : T\subseteq S(G)\}$. The two groupings count the same weighted set of pairs, so the two totals agree. $\blacksquare$

> **Lemma 5 (avoiding all marks).** *If each $G\in\mathcal F$ carries a (possibly empty) marked set $S(G)\subseteq U$, then*
> $$\#\{\,G : S(G)=\emptyset\,\} \;=\; \sum_{T\subseteq U} (-1)^{|T|}\, \#\{\,G : T\subseteq S(G)\,\}.$$

*Proof.* Same double counting, now over all pairs $(G,T)$ with $T \subseteq S(G)$ (the empty $T$ included), weighted $(-1)^{|T|}$. Grouped by $G$: the inner sum is $\sum_{T\subseteq S(G)}(-1)^{|T|}$, which equals $1$ if $S(G)=\emptyset$ (only $T=\emptyset$ occurs) and $0$ otherwise (binomial theorem, as in Lemma 4) — that is, $[\![\,S(G)=\emptyset\,]\!]$. Grouped by $T$: the stated right-hand side. $\blacksquare$

**Bridge to the familiar two-set inclusion–exclusion.** For $U=\{v_1,v_2\}$, write $A_i = \{G : v_i \in S(G)\}$. Lemma 5 reads
$$\#\{S(G)=\emptyset\} = |\mathcal F| - |A_1| - |A_2| + |A_1\cap A_2|,$$
which is exactly the classical $|A_1\cup A_2| = |A_1|+|A_2|-|A_1\cap A_2|$ rearranged to count the objects in *neither* set. Lemma 5 is nothing more than this, for any number of "bad" properties.

**Worked micro-example.** Let $\mathcal F$ be the three bipartite DAGs on $m=n=1$ (no edge; $a\to v$; $v\to a$) and mark the offending vertex: $S(G) = \{v\}$ if $v$ has in-degree $0$, else $\emptyset$. The marked sets are $\{v\}, \emptyset, \{v\}$ respectively. Lemma 5 with $U=\{v\}$: $\#\{S=\emptyset\} = 3 - \#\{G : v \text{ has in-degree } 0\} = 3-2 = 1$ — correctly counting the single graph $a\to v$, which is $D(1,1)$ as computed again in §5.2.

The final tool packages the "easy count" appearing on the right of (4.1) and Lemma 5:

> **Lemma 6 (forced sources factor out).** *Let $T$ be a fixed set of vertices with $j = |T\cap P_1|$ and $i=|T\cap P_2|$. Then the bipartite digraphs $G$ on $(m,n)$ that are acyclic and in which every vertex of $T$ has in-degree $0$ are in bijection with the pairs $(G', F)$ where:*
> * *$G'$ is an arbitrary bipartite DAG on the remaining $(m-j,\,n-i)$ vertices, and*
> * *$F$ is an arbitrary set of edges from $T$ to the opposite-partition vertices outside $T$.*
>
> *Hence there are exactly $2^{\,j(n-i)+i(m-j)}\;E(m-j,\,n-i)$ such graphs.*

*Proof.* Classify every potential edge of a bipartite digraph by its position relative to $T$:

* *edges entering a vertex of $T$* (from anywhere): forbidden, since $T$-vertices must have in-degree $0$;
* *edges between two vertices of $T$*: any such edge enters a $T$-vertex — forbidden as well;
* *edges among the remaining vertices*: these constitute an arbitrary bipartite digraph $G'$ on the other $m-j$ vertices of $P_1$ and $n-i$ vertices of $P_2$;
* *edges leaving $T$ towards the rest*: each of the $j$ vertices of $T\cap P_1$ may point to any of the $n-i$ remaining $P_2$ vertices ($j(n-i)$ potential edges), and each of the $i$ vertices of $T\cap P_2$ may point to any of the $m-j$ remaining $P_1$ vertices ($i(m-j)$ potential edges). Each of these $j(n-i)+i(m-j)$ edges is freely present or absent: $2^{\,j(n-i)+i(m-j)}$ choices for $F$.

It remains to see that the acyclicity of $G$ does not constrain $F$: the vertices of $T$ are sources of $G$, so by Observation 1, $G$ is acyclic **iff** $G-T = G'$ is acyclic — whatever $F$ is. Conversely $G$ determines $(G',F)$ uniquely, so the correspondence is a bijection, and $G'$ ranges over the $E(m-j,n-i)$ bipartite DAGs. $\blacksquare$

*Worked micro-example.* $m=2$, $n=1$, $T=\{a_1\}$ (so $j=1$, $i=0$): the formula predicts $2^{1\cdot 1+0}\,E(1,1) = 2\cdot 3=6$ bipartite DAGs on $(\{a_1,a_2\},\{v\})$ in which $a_1$ has in-degree $0$. Indeed: the edge $v\to a_1$ is forbidden, the edge $a_1\to v$ is free ($2$ choices), and the rest is one of the $E(1,1)=3$ bipartite DAGs on $(\{a_2\},\{v\})$ — no edge, $a_2\to v$, or $v\to a_2$ — and none of these $6$ combinations can create a cycle since $a_1$ has no incoming edge.

By Observation 3 (edge reversal), the mirror statement of Lemma 6 also holds: for a set $T$ forced to have **out-degree $0$** (forced sinks), the same factorization applies with "edges leaving $T$" replaced by "edges entering $T$".

---

## 5. Proof of Theorem 1

The strategy, justified by §3.4: first strip the two degree constraints of Lemma 1 off with Lemma 5 (transforms $N \to D \to E$), then count $E$ by peeling source layers with (4.1). We present the proof in the order of computation ($E$, then $D$, then $N$).

### 5.1 The recursion for $E(m,n)$ (source peeling)

Let $(m,n)\neq (0,0)$ and let $\mathcal F$ be the family of all bipartite DAGs on $(m,n)$, so $|\mathcal F| = E(m,n)$. Take as marked set $S(G)$ the set of *sources* of $G$ — nonempty by Observation 2 — and apply (4.1) with universe $U = P_1\cup P_2$:

$$E(m,n) \;=\; \sum_{\emptyset\neq T\subseteq P_1\cup P_2} (-1)^{|T|+1}\, \#\{\,G \in \mathcal F: \text{every } v\in T \text{ is a source}\,\}.$$

"Every $v\in T$ is a source" means precisely "every $v \in T$ has in-degree $0$", so Lemma 6 applies: if $T$ contains $j$ vertices of $P_1$ and $i$ of $P_2$, the inner count equals $2^{\,j(n-i)+i(m-j)}\, E(m-j,n-i)$. Crucially, this count depends on $T$ **only through the pair $(j,i)$**, so we may group the sum over sets $T$ into a sum over types: there are $\binom{m}{j}\binom{n}{i}$ ways to choose which $j$ vertices of $P_1$ and which $i$ vertices of $P_2$ make up $T$, and every such choice contributes the same amount. Summing over the types $(j,i)\neq(0,0)$:

$$E(m,n)=\sum_{(j,i)\neq(0,0)} (-1)^{i+j+1}\binom{m}{j}\binom{n}{i} 2^{\,j(n-i)+i(m-j)}\,E(m-j,\,n-i). \qquad\blacksquare$$

This is the layer-by-layer build-up of the intuition in its classical (Robinson) form: the alternating signs compensate for the fact that a fixed $T$ inside the source set does not determine the source set exactly.

*Worked check.* $E(1,1)$: types $(1,0)$ and $(0,1)$ contribute $+2\cdot E(0,1) = 2$ and $+2\cdot E(1,0)=2$; type $(1,1)$ contributes $-E(0,0)=-1$. Total $E(1,1)=3$ — correct: no edge, $a\to v$, or $v\to a$.

### 5.2 From $E$ to $D$: forbidding $P_2$ sources

Recall $D(m,n)$ counts bipartite DAGs in which no $P_2$ vertex has in-degree $0$. Apply Lemma 5 to the family of **all** bipartite DAGs with marked set $Y(G) = \{v\in P_2 : \deg^-(v)=0\}$ (the offending vertices) and universe $U=P_2$:

$$D(m,n) = \#\{G: Y(G)=\emptyset\} = \sum_{K\subseteq P_2} (-1)^{|K|}\,\#\{\,G:\ \text{every } v\in K \text{ has in-degree } 0\,\}.$$

For fixed $K$ with $|K|=k$, Lemma 6 (with $T=K$, so $j=0$, $i=k$) gives $\#\{\dots\} = 2^{\,k m}\, E(m,\,n-k)$: the $k$ forced-source vertices have no in-edges and completely free out-edges to the $m$ vertices of $P_1$, and what remains is an arbitrary bipartite DAG on $(m,\,n-k)$. Grouping the $\binom{n}{k}$ sets $K$ of size $k$ (the count again depends only on $k$):

$$D(m,n) = \sum_{k=0}^n (-1)^k \binom{n}{k}\, 2^{km}\, E(m,\,n-k). \qquad\blacksquare$$

*Worked check.* $D(1,1) = E(1,1) - 2^{1}E(1,0) = 3-2 = 1$ — matching the micro-example of §4: only $a\to v$ gives $v$ an in-edge.

### 5.3 From $D$ to $N$: forbidding $P_2$ sinks

First, a remark on why the two inclusion–exclusions must be **nested** rather than run side by side: to count the graphs with no $P_2$ sink by inclusion–exclusion, the ambient family must contain graphs that *do* have $P_2$ sinks — so the sink constraint must already be relaxed. The right ambient family is $\mathcal D(m,n)$, the class counted by $D$ (bipartite DAGs, every $P_2$ vertex of in-degree $\ge1$, sinks unconstrained): it keeps the source-side constraint while leaving the sink side free.

Apply Lemma 5 to $\mathcal D(m,n)$ with marked set $Z(G) = \{v \in P_2 : \deg^+(v) = 0\}$. By Lemma 1, $N(m,n) = \#\{G \in \mathcal D : Z(G)=\emptyset\}$, so

$$N(m,n) \;=\; \sum_{K\subseteq P_2} (-1)^{|K|}\, \#\{\,G\in\mathcal D:\ \text{every } v \in K \text{ has out-degree } 0\,\}.$$

Fix $K$ with $|K|=k$. We claim the graphs $G\in\mathcal D$ in which all of $K$ has out-degree $0$ are in bijection with the pairs

$$\Bigl(\ G'' \in \mathcal D(m,\,n-k)\ ;\ \ \text{an independent choice, for each } v\in K, \text{ of a nonempty subset of } P_1 \text{ as its in-neighbourhood}\ \Bigr).$$

**From $G$ to the pair.** Set $G'' = G-K$ and record the in-edges of each $v\in K$ (they come from $P_1$, since $G$ is bipartite and $K\subseteq P_2$; and each is nonempty because $G\in\mathcal D$ forces $\deg^-(v)\ge1$ — this is where the kept constraint contributes the factor $(2^m-1)$ per vertex instead of $2^m$). Two things could go wrong with $G''$ and do not:

* deleting $K$ deletes only edges $P_1\to K$ — out-edges of $P_1$ vertices — so some $P_1$ vertices may become **sinks** of $G''$. Harmless: membership in $\mathcal D$ constrains only the in-degrees of $P_2$ vertices. (Concretely: $G$ with edges $a_1\to v_1,\ v_1\to a_2,\ a_2\to v_2$ and $K=\{v_2\}$ leaves $G''=a_1\to v_1\to a_2$, in which $a_2$ is a new sink — still a perfectly good member of $\mathcal D(2,1)$. Had the ambient class also constrained sinks, this remainder would have had to be rejected and the bijection would fail.)
* the in-degrees of the surviving $P_2$ vertices are untouched (their in-edges come from $P_1$, not from $K$), so $G''\in\mathcal D(m,\,n-k)$ indeed.

**From the pair to $G$.** Given $G''$ and the chosen in-neighbourhoods, add the $k$ vertices of $K$ with exactly those incoming edges and no outgoing ones. The result is acyclic by Observation 1 (the vertices of $K$ are sinks, and $G''$ is acyclic — this is the out-degree mirror of the observation), every vertex of $K$ has in-degree $\ge1$ by construction, and the other $P_2$ in-degrees are those of $G''$, all $\ge 1$. So $G\in\mathcal D(m,n)$ with all of $K$ of out-degree $0$. The two constructions invert each other.

Counting the pairs: $D(m,\,n-k)$ choices of $G''$ and $(2^m-1)$ nonempty subsets of $P_1$ for each of the $k$ vertices of $K$, independently. Grouping the $\binom{n}{k}$ sets $K$ of size $k$:

$$N(m,n) = \sum_{k=0}^n (-1)^k\binom{n}{k}\,(2^m-1)^k\, D(m,\,n-k). \qquad\blacksquare$$

*Worked check.* $N(2,1) = D(2,1) - (2^2-1)\,D(2,0)$. Here $D(2,0)=E(2,0)=1$ and $D(2,1) = E(2,1) - 4E(2,0) = 9-4=5$, so $N(2,1) = 5-3 = 2$ — matching the two chains $a_1 \to v \to a_2$ and $a_2 \to v \to a_1$ found by hand in §1.1.

### 5.4 Remarks on the structure of the proof

* The roles of the two constraints can be exchanged: define $D'(m,n)$ = bipartite DAGs with no $P_2$ *sink*, strip the source condition second. By Observation 3 (edge reversal maps the class of $D$ bijectively onto the class of $D'$), $D'=D$ and the same formula results.
* The only genuine recursion is the one for $E$; the transforms are finite sums along one row of the $E$-table. This is what makes Theorem 1 cheap to evaluate.

---

## 6. Proof of Theorem 2 — the literal layer recursion

Here we implement the peeling of §3.3 directly, tracking the sink counts that §3.4 identified as the coupling variable. Recall

* $a_s(m,n)$: DD-graphs on $(m,n)$ with exactly $s$ sinks;
* $b_s(m,n)$: bipartite DAGs on $(m,n)$, sources $\subseteq P_1$, sinks $\subseteq P_2$, exactly $s$ sinks.

Both classes contain the empty graph when $m=n=0$ (it has no sinks, so $a_0(0,0)=b_0(0,0)=1$). For a nonempty graph the sink set is nonempty — every nonempty DAG has a sink by Observation 2 — and contained in $P_1$ (class $a$) resp. $P_2$ (class $b$), forcing $1\le s\le m$ resp. $1\le s\le n$; all other values of $s$ count nothing.

### 6.1 Peeling a DD-graph ($a$ in terms of $b$)

Let $G$ be a DD-graph on $(m,n)$, $m+n\ge1$, with sink set $T$, $|T|=s\ge 1$, $T\subseteq P_1$. We claim $G$ is uniquely determined by, and can be freely reassembled from, the triple

$$\bigl(\,T,\;\; G'=G-T,\;\; F = \text{the set of edges entering } T\,\bigr)$$

subject to: $T\subseteq P_1$ with $|T| = s$; $G'$ in the class counted by $b_{s'}(m-s,\,n)$ for some $s'$; and $F$ a set of edges from $P_2$ into $T$ such that **every sink of $G'$ sends at least one edge into $T$**.

*Proof of the claim.* Given $G$, Lemma 3(i) shows $G'$ has sources $\subseteq P_1$ and sinks $\subseteq P_2$, i.e. lies in class $b$; and $F$ consists of edges from $P_2$ into $T\subseteq P_1$ by bipartiteness. Every sink of $G'$ is a non-sink of $G$ (the sinks of $G$ are exactly $T$), and its out-edges in $G$ all go into $T$, so it sends $\ge 1$ edge into $T$. Conversely, assemble $G$ from any admissible triple:

* **Acyclicity**: the vertices of $T$ have out-degree $0$, so by Observation 1, $G$ is acyclic iff $G'$ is. ✔
* **Sink set of $G$ is exactly $T$**: vertices of $T$ have out-degree $0$ ✔; a sink of $G'$ sends an edge into $T$, hence is not a sink of $G$ ✔; a non-sink of $G'$ keeps its out-edge ✔.
* **Sources of $G$ lie in $P_1$**: adding $F$ only *increases* in-degrees, and only on $T$; the in-degrees of the vertices of $G'$ are unchanged, and the sources of $G'$ lie in $P_1$. A vertex of $T$ receiving no edge of $F$ is isolated in $G$ — a source *and* sink in $P_1$, which is allowed. ✔ (This is why the $T$-side of $F$ is unconstrained.)

So all DD conditions hold, and the two constructions invert each other. $\blacksquare$

**Counting the triples.** Choose $T$: $\binom{m}{s}$ ways. Choose $G'$: $b_{s'}(m-s,n)$ ways, for each number $s'$ of sinks. Choose $F$: as computed in §3.4, each of the $s'$ sinks of $G'$ picks a *nonempty* subset of $T$ ($2^s-1$ ways), each of the other $n - s'$ vertices of $P_2$ picks an arbitrary subset ($2^s$ ways) — independent choices, because they concern out-edges of distinct vertices. Hence

$$a_s(m,n)=\binom{m}{s}\sum_{s'=0}^{n} \bigl(2^{s}-1\bigr)^{s'}\, 2^{\,s(n-s')}\; b_{s'}(m-s,\,n).$$

*Remark (the $s'=0$ term).* For a nonempty remainder, $b_0 = 0$; the $s'=0$ term is nonzero only when the remainder is empty, $(m-s,n)=(0,0)$, and then it carries the base case — e.g. $a_m(m,0) = \binom{m}{m}\cdot b_0(0,0) = 1$, the edgeless graph whose $m$ isolated vertices are all sinks. All other vanishing terms are harmless under the zero conventions of Theorem 2.

### 6.2 Peeling a $b$-graph ($b$ in terms of $a$)

Let $G$ be in class $b$ on $(m,n)$, $m+n \ge 1$, with sink set $U \subseteq P_2$, $|U| = s\ge 1$. As before, $G$ corresponds to a triple $(U,\ G''=G-U,\ F)$ where now, by Lemma 3(ii), $G''$ is a **DD-graph** on $(m,\,n-s)$ — say with $s''$ sinks, all in $P_1$ — and $F$ is a set of edges from $P_1$ into $U$ subject to **two** constraints:

* every vertex of $U$ **receives** at least one edge of $F$: in class $b$ all sources lie in $P_1$, and $U\subseteq P_2$, so each $u\in U$ needs in-degree $\ge1$ — and its in-edges are precisely its edges in $F$;
* every sink of $G''$ **sends** at least one edge of $F$ into $U$: otherwise it would stay a sink of $G$, but it lies in $P_1$ and the sinks of $G$ must be exactly $U\subseteq P_2$.

The verification that any admissible triple assembles into a valid $b$-graph with sink set exactly $U$ mirrors §6.1:

* **Acyclicity**: the vertices of $U$ have out-degree $0$, so by Observation 1, $G$ is acyclic iff $G''$ is. ✔
* **Sink set of $G$ is exactly $U$**: vertices of $U$ have out-degree $0$ since $F$ only *enters* $U$ ✔; a sink of $G''$ sends an edge into $U$, hence is not a sink of $G$ ✔; the remaining vertices of $G''$ keep their out-edges ✔ — and note that the $P_2$ vertices of $G''$ are non-sinks of $G''$ *automatically*, because the sinks of a DD-graph lie in $P_1$.
* **Sources of $G$ lie in $P_1$**: in-degrees of $G''$-vertices are unchanged ($F$ enters only $U$) and the sources of the DD-graph $G''$ lie in $P_1$; each vertex of $U$ has in-degree $\ge1$ by the first constraint on $F$. ✔
* **Sinks of $G$ lie in $P_2$**: the sink set is $U\subseteq P_2$ by the second point. ✔

**Counting the edge sets $F$.** Unlike §6.1, *both sides* of $F$ are constrained — every right vertex ($U$) must be covered and the $s''$ designated left vertices (the sinks of $G''$) must each send an edge — so $F$ no longer factors vertex by vertex. This is exactly the count $\varphi(s'',\,m-s'',\,s)$ defined in §2.2 and computed next in §6.3: left set $=P_1$ with the $s''$ sinks of $G''$ designated, right set $=U$ of size $s$. Hence

$$b_s(m,n)=\binom{n}{s}\sum_{s''=0}^{m} \varphi\bigl(s'',\,m-s'',\,s\bigr)\; a_{s''}(m,\,n-s).$$

### 6.3 The covering function $\varphi$

> **Lemma 7.** *Let $L$ be a set of $p+q$ "left" vertices with a designated subset $L_0\subseteq L$, $|L_0|=p$, and let $R$ be a set of $r$ "right" vertices. The number of bipartite edge sets $F$ between $L$ and $R$ such that every vertex of $R$ has degree $\ge1$ and every vertex of $L_0$ has degree $\ge 1$ equals*
> $$\varphi(p,q,r) \;=\; \sum_{t=0}^{p} (-1)^t \binom{p}{t}\,\bigl(2^{\,p+q-t}-1\bigr)^{r}.$$

*Proof.* First observe that an edge set $F$ between $L$ and $R$ is the same thing as an independent choice, for each right vertex, of its neighbourhood — the subset of $L$ it is joined to; the condition "every right vertex has degree $\ge1$" says each chosen neighbourhood is nonempty. Now apply Lemma 5, taking as objects the edge sets $F$ that already satisfy the right-side condition, and as marked set $S(F) = \{\ell \in L_0 : \deg_F(\ell) = 0\}$ — the designated left vertices missed by $F$. For a fixed $B\subseteq L_0$ with $|B|=t$, the edge sets avoiding $B$ entirely while covering $R$ are counted by letting each right vertex choose a nonempty neighbourhood inside $L\setminus B$: $\bigl(2^{p+q-t}-1\bigr)^r$ ways, independently. Group the $\binom{p}{t}$ sets $B$ of size $t$. $\blacksquare$

*Worked micro-check.* $\varphi(1,0,1)$ (one designated left vertex, one right vertex) $= (2^1-1) - (2^0-1) = 1$: the only admissible edge set is the single edge, as it must be.

### 6.4 Assembling $N$, termination, and a worked check

Summing the refined counts over the number of sinks, $N(m,n)=\sum_{s} a_s(m,n)$ (for $m=n=0$ this reads $N(0,0)=a_0(0,0)=1$). The recurrence for $a_s(m,n)$ calls $b_{\cdot}(m-s,n)$ with $s\ge1$, and $b_s(m,n)$ calls $a_{\cdot}(m,n-s)$ with $s\ge1$; the total number of vertices drops strictly at each step until $(0,0)$, where the base cases stop the recursion. $\blacksquare$

*Worked check ($N(2,1)$ via Theorem 2).* We need $a_1(2,1)$ and $a_2(2,1)$.

* $b_1(1,1) = \binom{1}{1}\,\varphi(1,0,1)\,a_1(1,0)$, where $a_1(1,0)=1$ (the isolated vertex $a$, one sink) and $\varphi(1,0,1)=1$ as just computed — so $b_1(1,1)=1$. (This $b$-graph is the single edge $a\to v$.)
* $a_1(2,1) = \binom{2}{1}\bigl[(2^1-1)^1\,2^{0}\,b_1(1,1)\bigr] = 2\cdot 1 = 2$ (the $s'=0$ term vanishes: $b_0(1,1)=0$).
* $a_2(2,1) = \binom{2}{2}\sum_{s'}(\cdots)\, b_{s'}(0,1) = 0$, since a $b$-graph on $(0,1)$ would need an in-edge into its $P_2$ vertex from an empty $P_1$.

Hence $N(2,1) = 2+0 = 2$ — again matching §1.1. ✔

The two theorems were derived by genuinely different routes (global inclusion–exclusion vs. explicit layer peeling), so their agreement on all $0\le m,n\le 12$ — on top of the brute-force match — is strong evidence that both proofs are sound.

---

## 7. Base cases and sanity anchors

### 7.1 Base cases

**Theorem 1** needs exactly one base case:

$$E(0,0)=1 \quad (\text{the empty graph}).$$

Every term of the $E$-recursion strictly reduces $m+n$, and the transforms $D, N$ are finite sums, so nothing else is required. The recursion then *derives*: $E(m,0)=E(0,n)=1$, $D(m,0)=1$, $D(0,n)=[\![n=0]\!]$, $N(m,0)=1$, $N(0,n)=[\![n=0]\!]$.

**Theorem 2** needs:

$$a_0(0,0)=b_0(0,0)=1, \qquad a_s(m,n)=0 \ \ (m+n\ge 1,\ s\notin[1,m]), \qquad b_s(m,n)=0 \ \ (m+n\ge1,\ s\notin [1,n]).$$

### 7.2 Independent sanity anchors

These values can be checked by a reader with pencil and paper, independently of both theorems.

* $N(m,0)=1$, $N(0,n)=N(1,n)=[\![n=0]\!]$ — §1.3; reproduced by both formulas.

* $N(m,1) = 3^m - 2^{m+1} + 1$. A single $P_2$ vertex $v$ is described by the pair (its in-neighbourhood, its out-neighbourhood) in $P_1$. The two sets must be **disjoint** — a common vertex $a$ would give the $2$-cycle $a\to v\to a$ — and both **nonempty** (Lemma 1); conversely any such choice is acyclic, since a cycle would have to visit $v$ twice. So each $a \in P_1$ independently plays one of three roles (*in*, *out*, or *unused*): $3^m$ maps, minus those with empty in-set or empty out-set, by the two-set inclusion–exclusion of §4: $3^m - 2^m - 2^m + 1$. This matches column $n=1$ of the table: $0, 0, 2, 12, 50, 180, 602,\dots$ *(Aside for readers who know them: this equals $2\,S(m+1,3)$, where $S(m+1,3)$ — a Stirling number of the second kind — counts the partitions of $m+1$ labeled items into $3$ nonempty unordered blocks: adjoin a dummy item to absorb the "unused" role, and the factor $2$ orders the in/out blocks.)*

* $N(2,n)=2$ for $n\ge1$. With $m=2$, the disjoint-nonempty requirement above forces each $P_2$ vertex to be a "through vertex": in-set $\{a_i\}$, out-set $\{a_j\}$ with $i \ne j$ — i.e. one of the two orientations $a_1\to v\to a_2$ or $a_2\to v\to a_1$. Two vertices with opposite orientations create the $4$-cycle $a_1 \to v \to a_2 \to w \to a_1$. Conversely, if all $n$ vertices share one orientation, say $a_1\to v_i \to a_2$ for all $i$, the graph is acyclic: every edge goes strictly forward in the ordering $a_1 \prec \{v_1,\dots,v_n\} \prec a_2$. Hence exactly $2$ DD-graphs, for every $n\ge1$.

---

## 8. Computational verification

The work was staged in three phases: **Phase 1** established brute-force ground truth, **Phase 2** produced the recursive formulas of §5–6, and **Phase 3** verified the formulas against the ground truth and against each other.

**1. Ground truth (`phase1_bruteforce.py`).** For each pair $(m,n)$ the script enumerates *all* bipartite digraphs — each of the $mn$ vertex pairs $\{a,v\}$ independently takes one of the states $\{$no edge, $a\to v$, $v\to a$, both$\}$ — and filters by acyclicity and by the source/sink condition. Acyclicity is tested with Kahn's algorithm: repeatedly delete vertices of in-degree $0$; the graph is acyclic iff every vertex is eventually deleted. The full $4$-state enumeration was run for $mn\le 9$ and shown to agree with the $3$-state enumeration that drops the "both" state (a pair with both arcs is a $2$-cycle, so it can never survive the acyclicity filter); the $3$-state version was then run for all $mn\le 12$ — that is, for 24 of the 25 pairs with $m,n\le4$.

**2. The $(4,4)$ case.** $3^{16}\approx 43$ million graphs is out of naive reach, so $N(4,4)$ was computed by a still-exhaustive but reorganized search: each $P_2$ vertex chooses a pair (in-neighbourhood, out-neighbourhood) of **disjoint nonempty** subsets of $P_1$ — nonempty by Lemma 1, disjoint because a common neighbour creates a $2$-cycle — giving $3^4-2\cdot2^4+1 = 50$ options per vertex (the count proved in §7.2), hence $50^4 = 6{,}250{,}000$ candidate configurations, pruned as follows. The search adds one $P_2$ vertex at a time and aborts any branch that has already created a cycle, detected on a compressed digraph justified by:

> **Lemma 8 (composition digraph).** *Let $G$ be a bipartite digraph on $(P_1,P_2)$ in which no $P_2$ vertex has a common in- and out-neighbour (true here: the two sets are disjoint). Define the digraph $H$ on the vertex set $P_2$ with an edge $v\to w$ whenever some $a\in P_1$ has $v\to a$ and $a\to w$ in $G$. Then $G$ has a directed cycle **iff** $H$ has one.*

*Proof.* Edges of $G$ cross the partitions, so a directed cycle of $G$ alternates between $P_2$ and $P_1$ vertices; rotate it to start in $P_2$: $v_1\to a_1\to v_2\to \cdots \to v_k\to a_k\to v_1$. The case $k=1$ is the $2$-cycle $v_1\to a_1\to v_1$, excluded by hypothesis. For $k\ge2$, each segment $v_i\to a_i\to v_{i+1}$ is an edge of $H$, so $v_1\to v_2\to\cdots\to v_k\to v_1$ is a cycle of $H$. Conversely, replacing each edge of a cycle of $H$ by a witnessing length-$2$ segment of $G$ yields a closed directed walk in $G$, and a closed walk always contains a directed cycle (shorten it until no vertex repeats). $\blacksquare$

This enumerator was cross-checked against the naive one on all 24 other pairs before being trusted for $(4,4)$, where it produced $N(4,4)=1{,}034{,}882$.

**3. Assertions (`phase2_3_recursive.py`).** The script computes $N(m,n)$ by Theorem 1 and by Theorem 2 and asserts equality with all 25 ground-truth values — **all assertions pass** — then asserts Theorem 1 $\equiv$ Theorem 2 on $0\le m,n\le 12$ — **passes**.

**4. Scale.** The recursion evaluates instantly far beyond brute-force reach, e.g. $N(8,8) = 310\,094\,666\,650\,192\,907\,649\,600\,002$.

---

## 9. Variant: counting over all sub-partitions (the `DDGraphOf` semantics)

### 9.1 Motivation and definition

In formal-specification settings a graph is usually a record $g = [\mathrm{node},\ \mathrm{edge}]$ that *carries its own vertex set*, and two records with the same edges but different node sets are different graphs. This section counts DD-graphs in that semantics.

The concrete motivation is the specification language **TLA+** (an *operator* there is a definable set-valued expression, and **TLC** is the tool that evaluates and exhaustively enumerates such sets). The operator `DDGraphOf(T, O)` of `ArmoniK.Spec` (module `DDGraphs`) enumerates, over a set $T$ of *task* ids and a set $O$ of *object* ids, **all** DD-graphs whose node set is *any* subset of $T\cup O$ — not only those whose node set is all of $T \cup O$. The role mapping to this report, fixed before reading the code: sources and sinks must be objects, so the **objects $O$ play the role of $P_1$** and the **tasks $T$ play the role of $P_2$** — and note that the operator takes tasks *first* while our functions take $|P_1|=m$ first:

```tla
DDGraphOf(T, O) ==
    UNION {
        { g \in [node: {to[1] \union to[2]},
                 edge: SUBSET ((to[1] \X to[2]) \union (to[2] \X to[1]))] :
            /\ IsDag(g)
            /\ Source(g) \subseteq to[2]
            /\ Sink(g) \subseteq to[2]
        } : to \in (SUBSET T) \X (SUBSET O)
    }
```

*Notation legend:* `SUBSET X` is the powerset of $X$; `A \X B` the Cartesian product; `to` ranges over pairs (task subset, object subset), i.e. `to[1]` $\subseteq T$ and `to[2]` $\subseteq O$; and `[node: A, edge: B]` is the set of records whose `node` field lies in $A$ and `edge` field in $B$ — here `node` ranges over the *singleton* $\{$`to[1]` $\cup$ `to[2]`$\}$, i.e. it equals that union. **In words:** for every choice of a subset of tasks and a subset of objects, collect every pair (node set, edge set) that forms a DD-graph on exactly that sub-partition; then take the union of all these collections.

Accordingly, define the **sub-partition-closed count**

$$\widehat N(m,n) \;=\; \#\bigl\{\, (V,\;A) \;:\; V \subseteq P_1\cup P_2,\ \ A \text{ an edge set making } (V, A) \text{ a DD-graph on } \bigl(V\cap P_1,\; V\cap P_2\bigr) \,\bigr\},$$

so that $\mathrm{Cardinality}\bigl(\texttt{DDGraphOf}(T,O)\bigr) = \widehat N\bigl(|O|,\,|T|\bigr)$.

**Why $\widehat N$ is much bigger than $N$.** The same *edge set* appears under many node sets — every enlargement of the node set by isolated objects yields a distinct graph record (isolated objects are legal; isolated tasks are not, by Lemma 1). The edgeless graphs alone already contribute $2^m$ records, one per subset of $P_1$ — which is why $\widehat N(m,0)=2^m$ while $N(m,0)=1$. The other trivial row is $\widehat N(0,n) = 1$: only the empty graph survives without objects.

### 9.2 The transform

> **Proposition.** *For all $m,n\ge 0$,*
> $$\widehat N(m,n) \;=\; \sum_{j=0}^{m}\sum_{i=0}^{n} \binom{m}{j}\binom{n}{i}\; N(j,\,i),$$
> *(in the standard terminology: $\widehat N$ is the "double binomial transform" of $N$). Conversely,*
> $$N(m,n) \;=\; \sum_{j=0}^{m}\sum_{i=0}^{n} (-1)^{\,(m-j)+(n-i)}\,\binom{m}{j}\binom{n}{i}\; \widehat N(j,\,i).$$

*Proof of the first identity.* Partition the counted family by the node set $V$. Could two different sub-partition pairs produce the same graph record? No: they would have the same node set $V$, and since $T$ and $O$ are disjoint, a pair with union $V$ must be exactly $(V\cap T,\ V\cap O)$ — so the `UNION` in the TLA+ definition is overlap-free. For a fixed $V$ with $|V\cap P_1| = j$ and $|V\cap P_2| = i$, the admissible edge sets are exactly the DD-graphs on those labeled vertex sets, of which there are $N(j,i)$ — recall that $N$'s convention already allows isolated $P_1$ vertices, matching `Source(g) ⊆ O` / `Sink(g) ⊆ O`. There are $\binom{m}{j}\binom{n}{i}$ node sets $V$ with intersection sizes $(j,i)$. Summing proves the identity. $\blacksquare$

*Proof of the inverse.* It rests on one orthogonality identity: for $k \le m$,

$$\sum_{j=k}^{m} (-1)^{m-j}\binom{m}{j}\binom{j}{k} \;=\; [\![\,m=k\,]\!].$$

Indeed $\binom{m}{j}\binom{j}{k} = \binom{m}{k}\binom{m-k}{j-k}$ (choose the $k$ elements first, then the remaining $j-k$ from the other $m-k$), so with $t=j-k$ the sum becomes $\binom{m}{k}\sum_{t=0}^{m-k}(-1)^{m-k-t}\binom{m-k}{t} = \binom{m}{k}\,(1-1)^{m-k}\cdot(\pm1)$, which vanishes unless $m=k$, where it is $1$. Now substitute the first identity of the Proposition into the right side of the claimed inverse and swap the summation order; the inner sums over the intermediate indices are exactly this orthogonality identity, once for the $P_1$ index and once for the $P_2$ index, collapsing the double sum to the single term $N(m,n)$. $\blacksquare$

### 9.3 Verified table

$\widehat N(m,n)$, computed by applying the Proposition to the (already verified) $N$-table:

| $m\backslash n$ | 0 | 1 | 2 | 3 | 4 | 5 |
|---:|---:|---:|---:|---:|---:|---:|
| **0** | 1 | 1 | 1 | 1 | 1 | 1 |
| **1** | 2 | 2 | 2 | 2 | 2 | 2 |
| **2** | 4 | **6** | 10 | 18 | 34 | 66 |
| **3** | 8 | 26 | **146** | **962** | 6 338 | 40 706 |
| **4** | 16 | 126 | 2 362 | 55 026 | 1 254 370 | 27 012 546 |
| **5** | 32 | 602 | 32 882 | 2 388 002 | 172 931 522 | 11 702 390 402 |
| **6** | 64 | 2 766 | 403 450 | 83 849 778 | 17 831 605 474 | 3 540 011 433 666 |

The three bold entries are exactly the cardinalities asserted in the TLC test suite `DDGraphsTests.tla`: `DDGraphOf({"t"}, {"o","p"})` has $\widehat N(2,1)=6$ members, `Cardinality(DDGraphOf({"t","u"}, {"o","p","q"})) = \widehat N(3,2) = 146$, and `Cardinality(DDGraphOf({"t","u","v"}, {"o","p","q"})) = \widehat N(3,3) = 962$; likewise `DDGraphOf({}, {"o"})` has $\widehat N(1,0)=2$ members. All four match, which independently cross-validates the TLA+ enumeration and the recursions of this report against each other. In addition, $\widehat N(m,n)$ was recomputed for all $0\le m,n\le 3$ by per-node-set brute-force enumeration (summing `count_dd_naive` over all sub-partition pairs), and the inverse transform was checked to recover $N(m,n)$ for all $0\le m,n\le 7$.

For reference, the subfamily of records using the full vertex sets, $\{\,g \in \texttt{DDGraphOf}(T,O) : g.\mathrm{node} = T\cup O\,\}$, has cardinality exactly $N(|O|,|T|)$ — e.g. $96$ and $588$ for the two TLC test instances above — so either count is recoverable from the other.

### 9.4 Code

```python
from math import comb

def N_hat(m, n):
    """Cardinality of DDGraphOf(T, O) with |O| = m objects (P1) and
    |T| = n tasks (P2): DD-graphs over ALL sub-partitions."""
    return sum(comb(m, j) * comb(n, i) * N_methodA(j, i)
               for j in range(m + 1) for i in range(n + 1))
```

(`N_methodA` is the Theorem 1 implementation listed in §11.2.)

---

## 10. Self-contained recurrences: eliminating the auxiliary functions

### 10.1 Motivation

Theorems 1 and 2 are recursive, but not *self-contained*: their right-hand sides involve auxiliary counting functions ($E$ and $D$, respectively $a_s$, $b_s$ and $\varphi$). It is natural to ask whether $N$ — and likewise $\widehat N$ — satisfies a recurrence whose right-hand side uses **only the function itself at strictly smaller index pairs**, with explicit elementary coefficients. The answer is yes for both (Theorems 3 and 4 below).

Two caveats frame the result. The recurrences are obtained from Theorem 1 by *algebraic elimination* — no new counting argument is involved — and their coefficients accordingly have no combinatorial reading: unlike in Theorems 1 and 2, the individual factors no longer count edges, neighbourhoods or layers, and the signed intermediate terms can exceed the final count. Nothing is gained computationally either: filling the table below $(m,n)$ still costs $O(m^2n^2)$ big-integer operations. The value is conceptual — the DD-graph counts are pinned down by a single two-dimensional recurrence with no scaffolding.

### 10.2 Un-stripping the constraints: $E$ in terms of $N$

The two transforms of Theorem 1 pass from the unconstrained count $E$ down to $N$. The first step towards elimination is to *invert* them — to reconstruct $E$ from $N$. The inversion rests on a one-parameter lemma of independent interest:

> **Lemma 9 (shift inversion).** *Let $c$ be a fixed number and let $F, G$ be sequences related by*
> $$F(\nu) \;=\; \sum_{k=0}^{\nu} (-1)^k\binom{\nu}{k}\, c^k\, G(\nu-k) \qquad \text{for all } \nu\ge0 .$$
> *Then, conversely,*
> $$G(\nu) \;=\; \sum_{k=0}^{\nu} \binom{\nu}{k}\, c^k\, F(\nu-k) \qquad \text{for all } \nu \ge 0.$$

*Proof.* Substitute the hypothesis into the claimed right-hand side and collect terms by the total shift $t=k+l$, using $\binom{\nu}{k}\binom{\nu-k}{l} = \binom{\nu}{t}\binom{t}{k}$ (choose the $t$ shifted units first, then which $k$ of them belong to the outer sum):

$$\sum_{k}\binom{\nu}{k}c^k\,F(\nu-k) \;=\; \sum_{k,l}\binom{\nu}{k}c^k\,(-1)^l\binom{\nu-k}{l}c^l\,G(\nu-k-l) \;=\; \sum_{t}\binom{\nu}{t}\,c^t\Bigl[\sum_{k=0}^{t}(-1)^{t-k}\binom{t}{k}\Bigr]G(\nu-t).$$

The bracket is $(1-1)^t = [\![t=0]\!]$ by the binomial theorem, so only the $t=0$ term survives, leaving $G(\nu)$. $\blacksquare$

> **Lemma 10 (un-stripping).** *For all $m,\nu\ge 0$,*
> $$E(m,\nu) \;=\; \sum_{t=0}^{\nu}\binom{\nu}{t}\,\bigl(2^{m+1}-1\bigr)^{t}\; N(m,\nu-t).$$

*Proof.* For each fixed $m$, both transforms of Theorem 1 have exactly the shape required by Lemma 9 (in the second index). Applying it with $c = 2^m-1$ to the $N$-transform, and with $c=2^m$ to the $D$-transform:

$$D(m,\nu) = \sum_{k}\binom{\nu}{k}(2^m-1)^k\,N(m,\nu-k), \qquad E(m,\nu) = \sum_{l}\binom{\nu}{l}\,2^{lm}\,D(m,\nu-l).$$

Chain the two and collect by the total shift $t=l+k$, with the same binomial regrouping as in Lemma 9:

$$E(m,\nu) = \sum_{t}\binom{\nu}{t}\Bigl[\sum_{l=0}^{t}\binom{t}{l}\,(2^m)^l\,(2^m-1)^{t-l}\Bigr]N(m,\nu-t),$$

and the bracket equals $\bigl(2^m + 2^m-1\bigr)^t = \bigl(2^{m+1}-1\bigr)^t$ by the binomial theorem. $\blacksquare$

In words: stripping the two "degree $\ge1$" constraint families off costs two *signed* transforms, but putting them back on is a single *unsigned* one.

### 10.3 Theorem 3 — the pure recurrence for $N$

> **Theorem 3.** *Set $\beta_j(m) = 2^{m+1}-2^{j}-2^{m-j}$ (a nonnegative integer for $0\le j\le m$, symmetric under $j\leftrightarrow m-j$, with $\beta_0=\beta_m=2^m-1$). Then $N(0,0)=1$ and, for $(m,n)\neq(0,0)$,*
> $$N(m,n)\;=\;\sum_{\substack{0\le j\le m,\ 0\le r\le n\\(j,r)\neq(0,0)}} (-1)^{j+1}\,\binom{m}{j}\binom{n}{r}\; 2^{\,j(n-r)}\;\beta_j(m)^{\,r}\; N(m-j,\,n-r).$$

*Proof.* Package the recursion of Theorem 1 homogeneously: for **every** pair $(m,n)$, including $(0,0)$,

$$\sum_{j=0}^m \sum_{i=0}^n (-1)^{i+j}\, \binom{m}{j}\binom{n}{i}\, 2^{\,j(n-i)+i(m-j)}\; E(m-j,\,n-i) \;=\; [\![\,(m,n)=(0,0)\,]\!]. \tag{10.1}$$

(At $(0,0)$ the only term is $E(0,0)=1$; for $(m,n)\neq(0,0)$, the $(j,i)=(0,0)$ term is $+E(m,n)$, and moving it to the other side recovers the $E$-recursion of Theorem 1.)

Now substitute Lemma 10 at each argument pair, with $c_{m-j} = 2^{\,m-j+1}-1$:

$$E(m-j,\,n-i) \;=\; \sum_{k=0}^{n-i}\binom{n-i}{k}\, c_{m-j}^{\,k}\; N(m-j,\,n-i-k),$$

and in the resulting triple sum group the two second-index shifts into $r=i+k$, using $\binom{n}{i}\binom{n-i}{r-i} = \binom{n}{r}\binom{r}{i}$. For fixed $j$ and $r$, the inner sum over $i$ is

$$\sum_{i=0}^{r} (-1)^i \binom{r}{i}\, 2^{\,j(n-i)+i(m-j)}\, c_{m-j}^{\,r-i}.$$

Split the first exponent as $n-i = (n-r)+(r-i)$, i.e. $2^{j(n-i)} = 2^{j(n-r)}\cdot 2^{j(r-i)}$; the sum becomes

$$2^{\,j(n-r)} \sum_{i=0}^{r}\binom{r}{i}\,\bigl(-2^{\,m-j}\bigr)^{i}\,\bigl(2^{j} c_{m-j}\bigr)^{r-i} \;=\; 2^{\,j(n-r)}\,\bigl(2^{j}c_{m-j} - 2^{\,m-j}\bigr)^{r}$$

by the binomial theorem, and $2^{j}c_{m-j} - 2^{m-j} = 2^{m+1}-2^{j}-2^{m-j} = \beta_j(m)$. Identity (10.1) has therefore become

$$\sum_{j=0}^m \sum_{r=0}^n (-1)^{j}\, \binom{m}{j}\binom{n}{r}\, 2^{\,j(n-r)}\,\beta_j(m)^{r}\; N(m-j,\,n-r) \;=\; [\![\,(m,n)=(0,0)\,]\!]. \tag{10.2}$$

The $(j,r)=(0,0)$ term is exactly $N(m,n)$ (its coefficient is $2^0\beta_0^0=1$); moving every other term across the equality gives the theorem. $\blacksquare$

*Worked checks.*

* $n=0$: only $r=0$ survives, and the theorem reads $N(m,0) = \sum_{j\ge1}(-1)^{j+1}\binom{m}{j}N(m-j,0)$ — satisfied by the constant row $N(\cdot,0)=1$, since $\sum_{j\ge1}(-1)^{j+1}\binom{m}{j} = 1$ for $m\ge1$.
* $(m,n)=(2,1)$: here $\beta_0=3$, $\beta_1=4$, $\beta_2=3$, and the five terms are
  $(j,r)=(0,1)$: $-3\,N(2,0)=-3$; $(1,0)$: $+2\cdot 2\,N(1,1)=0$; $(1,1)$: $+2\cdot 4\,N(1,0)=+8$; $(2,0)$: $-4\,N(0,1)=0$; $(2,1)$: $-3\,N(0,0)=-3$. Total: $N(2,1) = 2$. ✔

### 10.4 Theorem 4 — the pure recurrence for $\widehat N$

> **Theorem 4.** *Set $\gamma_j(m) = 2^{m+1}-2^{j+1}-2^{m-j}$ (an integer, possibly negative: $\gamma_m(m)=-1$) and*
> $$W(m,n,p,q)\;=\;\sum_{j=0}^{m-p}\binom{m-p}{j}\,2^{\,jq}\,\gamma_j(m)^{\,n-q}.$$
> *Then $\widehat N(0,0)=1$ and, for $(m,n)\neq(0,0)$,*
> $$\widehat N(m,n)\;=\;\sum_{\substack{0\le p\le m,\ 0\le q\le n\\(p,q)\neq(m,n)}} (-1)^{\,m-p+1}\,\binom{m}{p}\binom{n}{q}\; W(m,n,p,q)\;\widehat N(p,q).$$

Unlike Theorem 3, the coefficient retains one inner summation (over $j$); see §10.5 for why.

*Proof.* Start from identity (10.2) and eliminate $N$ in favour of $\widehat N$ using the inverse transform proved in §9.2,

$$N(a,b) \;=\; \sum_{p\le a,\ q\le b} (-1)^{(a-p)+(b-q)}\,\binom{a}{p}\binom{b}{q}\; \widehat N(p,q),$$

applied at $(a,b) = (m-j,\,n-r)$. Expanding and gathering the coefficient of $\widehat N(p,q)$ in (10.2): the total sign of the $(j,r)$ term is $(-1)^{j}\cdot(-1)^{(m-j-p)+(n-r-q)} = (-1)^{m-p}\,(-1)^{n-q}\,(-1)^{r}$, and the binomials regroup as $\binom{m}{j}\binom{m-j}{p} = \binom{m}{p}\binom{m-p}{j}$ and $\binom{n}{r}\binom{n-r}{q} = \binom{n}{q}\binom{n-q}{r}$. For fixed $j$, the sum over $r$ collapses — split $2^{j(n-r)} = 2^{jq}\cdot (2^{j})^{\,n-q-r}$:

$$\sum_{r=0}^{n-q} (-1)^r \binom{n-q}{r}\, 2^{\,j(n-r)}\, \beta_j(m)^{r} \;=\; 2^{\,jq}\sum_{r}\binom{n-q}{r}\bigl(-\beta_j(m)\bigr)^{r}\bigl(2^{j}\bigr)^{n-q-r} \;=\; 2^{\,jq}\,\bigl(2^{j}-\beta_j(m)\bigr)^{\,n-q},$$

and $2^{j}-\beta_j(m) = 2^{j+1}+2^{m-j}-2^{m+1} = -\gamma_j(m)$. Combining with the sign $(-1)^{n-q}$ gathered above, $(-1)^{n-q}\bigl(-\gamma_j\bigr)^{n-q} = \gamma_j^{\,n-q}$, so the coefficient of $\widehat N(p,q)$ in (10.2) equals

$$(-1)^{m-p}\,\binom{m}{p}\binom{n}{q}\, \sum_{j=0}^{m-p}\binom{m-p}{j}\,2^{\,jq}\,\gamma_j(m)^{\,n-q} \;=\; (-1)^{m-p}\,\binom{m}{p}\binom{n}{q}\;W(m,n,p,q).$$

At $(p,q)=(m,n)$ the only contribution comes from $(j,r)=(0,0)$ and the coefficient is $1$. Isolating that term in (10.2) gives the theorem. $\blacksquare$

*Worked checks.*

* $n=0$: $W(m,0,p,0)=2^{m-p}$, and the theorem reduces to $\widehat N(m,0) = \sum_{p<m}(-1)^{m-p+1}\binom{m}{p}\,2^{m-p}\,\widehat N(p,0)$ — satisfied by $\widehat N(m,0)=2^m$ (divide through by $2^m$ and use $\sum_{p<m}(-1)^{m-p+1}\binom{m}{p}=1$).
* $(m,n)=(2,1)$: here $\gamma_0=2$, $\gamma_1=2$, $\gamma_2=-1$, and with the values $\widehat N(0,0)=\widehat N(0,1)=1$, $\widehat N(1,0)=\widehat N(1,1)=2$, $\widehat N(2,0)=4$ of §9.3, the five terms are
  $(p,q)=(2,0)$: $-2\cdot 4=-8$; $(1,1)$: $+2\cdot 3\cdot 2=+12$; $(1,0)$: $+2\cdot 4\cdot 2=+16$; $(0,1)$: $-9\cdot 1=-9$; $(0,0)$: $-5\cdot 1=-5$. Total: $\widehat N(2,1) = 6$. ✔

### 10.5 Why the asymmetry, and verification status

For $N$ the elimination collapsed completely because both constraint-strippings act on the *same* index ($n$): the two inner summations merge into a single binomial-theorem collapse. The closure transform defining $\widehat N$ acts on **both** indices, and its $m$-component does not commute with the $m$-dependent weights $2^{jq}$ — one index refuses to telescope, leaving the inner $j$-sum inside $W$. (Expanding $\gamma_j^{\,n-q}$ multinomially can trade which index survives, but no fully closed collapse was found; we do not claim a proof that none exists.)

**Verification.** Both recurrences were implemented and asserted against the previously verified methods: Theorem 3 agrees with Theorem 1 for all $0\le m,n\le 10$, and Theorem 4 agrees with the transform of §9.2 for all $0\le m,n\le 8$ (code in §11.2). The worked checks above were also confirmed numerically.

---

## 11. Code appendix

### 11.1 Brute force (Phase 1)

```python
"""Ground truth for N(m, n) by brute-force enumeration."""
import itertools

def is_acyclic(num_nodes, adj, indeg):
    """Kahn's algorithm."""
    indeg = indeg[:]
    stack = [v for v in range(num_nodes) if indeg[v] == 0]
    seen = 0
    while stack:
        u = stack.pop()
        seen += 1
        for w in adj[u]:
            indeg[w] -= 1
            if indeg[w] == 0:
                stack.append(w)
    return seen == num_nodes

def count_dd_naive(m, n, states=3):
    """Enumerate every bipartite digraph between P1 = {0..m-1} and
    P2 = {m..m+n-1}; count those that are acyclic with all sources
    and sinks in P1.
    states=4: per pair {u,v}: none / u->v / v->u / both.
    states=3: without 'both' (a 2-cycle can never be acyclic;
              validated against states=4)."""
    P2 = range(m, m + n)
    pairs = [(u, v) for u in range(m) for v in P2]
    total_nodes = m + n
    count = 0
    for assign in itertools.product(range(states), repeat=len(pairs)):
        adj = [[] for _ in range(total_nodes)]
        indeg = [0] * total_nodes
        outdeg = [0] * total_nodes
        for (u, v), s in zip(pairs, assign):
            if s & 1:
                adj[u].append(v); indeg[v] += 1; outdeg[u] += 1
            if s & 2:
                adj[v].append(u); indeg[u] += 1; outdeg[v] += 1
        # all sources and sinks in P1  <=>  every P2 node has
        # in-degree >= 1 and out-degree >= 1
        if not all(indeg[v] > 0 and outdeg[v] > 0 for v in P2):
            continue
        if is_acyclic(total_nodes, adj, indeg):
            count += 1
    return count

def count_dd_fast(m, n):
    """Exhaustive search organised per P2 vertex, used for (4,4).
    Each P2 vertex picks disjoint nonempty (in_set, out_set) in P1
    (nonempty by Lemma 1; disjoint since a common neighbour is a
    2-cycle); the bipartite digraph is acyclic iff the 'composition'
    digraph on P2 (arc v->w iff out_v meets in_w) is acyclic — see
    Lemma 8.  Cyclic partial assignments are pruned."""
    if n == 0:
        return 1
    if m == 0:
        return 0
    full = (1 << m) - 1
    options = []
    for in_mask in range(1, full + 1):
        rest = full & ~in_mask
        out_mask = rest
        while out_mask:
            options.append((in_mask, out_mask))
            out_mask = (out_mask - 1) & rest
    ins, outs = [0] * n, [0] * n
    comp = [[False] * n for _ in range(n)]
    def has_cycle(k):
        color = [0] * k
        def dfs(u):
            color[u] = 1
            for w in range(k):
                if comp[u][w]:
                    if color[w] == 1: return True
                    if color[w] == 0 and dfs(w): return True
            color[u] = 2
            return False
        return any(color[u] == 0 and dfs(u) for u in range(k))
    count = 0
    def rec(v):
        nonlocal count
        if v == n:
            count += 1
            return
        for in_mask, out_mask in options:
            ins[v], outs[v] = in_mask, out_mask
            for w in range(v):
                comp[v][w] = bool(out_mask & ins[w])
                comp[w][v] = bool(outs[w] & in_mask)
            if not has_cycle(v + 1):
                rec(v + 1)
    rec(0)
    return count
```

### 11.2 The recursive formulas and the verification (Phases 2–3)

```python
"""Recursive formulas for N(m, n) (Theorems 1 and 2) + verification."""
from functools import lru_cache
from math import comb

# ---------- Theorem 1: streamlined system ----------

@lru_cache(maxsize=None)
def E(m, n):
    """All bipartite labeled DAGs on (m, n)."""
    if m == 0 and n == 0:
        return 1
    total = 0
    for j in range(m + 1):
        for i in range(n + 1):
            if i == 0 and j == 0:
                continue
            total += ((-1) ** (i + j + 1) * comb(m, j) * comb(n, i)
                      * 2 ** (j * (n - i) + i * (m - j)) * E(m - j, n - i))
    return total

@lru_cache(maxsize=None)
def D(m, n):
    """Bipartite DAGs with every P2 vertex of in-degree >= 1."""
    return sum((-1) ** k * comb(n, k) * 2 ** (k * m) * E(m, n - k)
               for k in range(n + 1))

def N_methodA(m, n):
    """DD-graphs."""
    return sum((-1) ** k * comb(n, k) * (2 ** m - 1) ** k * D(m, n - k)
               for k in range(n + 1))

# ---------- Theorem 2: alternating sink-layer peeling ----------

def phi(p, q, r):
    """Edge sets between p+q left / r right vertices: every right vertex
    and each of the p designated left vertices has degree >= 1."""
    return sum((-1) ** t * comb(p, t) * (2 ** (p + q - t) - 1) ** r
               for t in range(p + 1))

@lru_cache(maxsize=None)
def a(s, m, n):
    """DD-graphs on (m, n) with exactly s sinks (all in P1)."""
    if m == 0 and n == 0:
        return 1 if s == 0 else 0
    if s < 1 or s > m:
        return 0
    return comb(m, s) * sum(
        b(sp, m - s, n) * (2 ** s - 1) ** sp * 2 ** (s * (n - sp))
        for sp in range(n + 1))

@lru_cache(maxsize=None)
def b(s, m, n):
    """Bipartite DAGs, sources in P1, sinks in P2, exactly s sinks."""
    if m == 0 and n == 0:
        return 1 if s == 0 else 0
    if s < 1 or s > n:
        return 0
    return comb(n, s) * sum(
        a(spp, m, n - s) * phi(spp, m - spp, s)
        for spp in range(m + 1))

def N_methodB(m, n):
    return sum(a(s, m, n) for s in range(m + 1)) if m + n else 1

# ---------- Theorems 3 & 4: self-contained (pure) recurrences ----------

@lru_cache(maxsize=None)
def N_pure(m, n):
    """Theorem 3: right-hand side uses only N at smaller index pairs."""
    if m == 0 and n == 0:
        return 1
    total = 0
    for j in range(m + 1):
        for r in range(n + 1):
            if j == 0 and r == 0:
                continue
            beta = 2 ** (m + 1) - 2 ** j - 2 ** (m - j)
            total += ((-1) ** (j + 1) * comb(m, j) * comb(n, r)
                      * 2 ** (j * (n - r)) * beta ** r * N_pure(m - j, n - r))
    return total

@lru_cache(maxsize=None)
def N_hat_pure(m, n):
    """Theorem 4: right-hand side uses only N_hat at smaller index pairs."""
    if m == 0 and n == 0:
        return 1
    total = 0
    for p in range(m + 1):
        for q in range(n + 1):
            if p == m and q == n:
                continue
            w = sum(comb(m - p, j) * 2 ** (j * q)
                    * (2 ** (m + 1) - 2 ** (j + 1) - 2 ** (m - j)) ** (n - q)
                    for j in range(m - p + 1))
            total += ((-1) ** (m - p + 1) * comb(m, p) * comb(n, q)
                      * w * N_hat_pure(p, q))
    return total

# ---------- Phase 3: verification ----------

if __name__ == "__main__":
    from phase1_bruteforce import count_dd_naive, count_dd_fast
    # the 4th 'both' state only ever creates 2-cycles: the honest 4-state
    # enumeration agrees with the 3-state one wherever it is tractable
    for m in range(5):
        for n in range(5):
            if m * n <= 9:
                assert count_dd_naive(m, n, 4) == count_dd_naive(m, n, 3)
    # both theorems reproduce the brute-force ground truth
    for m in range(5):
        for n in range(5):
            truth = (count_dd_naive(m, n) if m * n <= 12
                     else count_dd_fast(m, n))
            assert N_methodA(m, n) == truth, (m, n)
            assert N_methodB(m, n) == truth, (m, n)
    # the two independent theorems agree well beyond brute-force reach
    for m in range(13):
        for n in range(13):
            assert N_methodA(m, n) == N_methodB(m, n), (m, n)
    # Theorem 3 (pure recurrence for N) agrees with Theorem 1
    for m in range(11):
        for n in range(11):
            assert N_pure(m, n) == N_methodA(m, n), (m, n)
    # Theorem 4 (pure recurrence for N_hat) agrees with the section 9.2
    # double binomial transform of N
    for m in range(9):
        for n in range(9):
            n_hat = sum(comb(m, j) * comb(n, i) * N_methodA(j, i)
                        for j in range(m + 1) for i in range(n + 1))
            assert N_hat_pure(m, n) == n_hat, (m, n)
    print("All assertions passed.")
```

---

## 12. References

* R. W. Robinson, *Counting labeled acyclic digraphs*, in **New Directions in the Theory of Graphs** (F. Harary, ed.), Academic Press, 1973 — the origin of the source-peeling inclusion–exclusion recurrence for labeled DAGs, rederived from scratch in §4–5 and adapted there to the bipartite setting.
* R. P. Stanley, *Acyclic orientations of graphs*, Discrete Math. 5 (1973) — a companion classical work on DAG enumeration, cited for historical context only; nothing in this report depends on it.
