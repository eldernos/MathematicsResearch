# Weighted Lambert series for ln 2 and signed multiplicative benchmarks

This note analyzes the weighted Lambert series
```math
\ln 2 = \sum_{m=1}^{\infty} \frac{a_m}{2^m - 1},
\qquad
a_m = \frac{1}{m} \prod_{p \mid m} (1 - p),
```
in direct comparison with the Erdős–Borwein constant $E = \sum_{m \ge 1} (2^m - 1)^{-1} = \sum_{n \ge 1} \tau(n) 2^{-n}$ and Mira Cult's local isolation method ([Phase 13 audit](../phase13/reviews/erdos-local-limit.md), [Phase 14 arrival analysis](../phase14/erdos-borwein-frequencies.md)).

**Summary of conclusions.**

1. **Exact arithmetic and $v_2(a_m)$ distribution (Paper theorems).** The coefficient $a_m$ is multiplicative with $\operatorname{sgn}(a_m) = (-1)^{\omega(m)}$, $|a_m| = (\operatorname{rad}(m)/m)(\varphi(m)/m) < 1$ for $m \ge 2$, and $a_{2^e u} = -2^{-e} a_u$ for $e \ge 1$, $u$ odd. The largest prime factor $P^+(m)$ always divides $\operatorname{den}(a_m)$ to its full power $v_{P^+(m)}(m)$; thus $a_m \in \mathbb{Z} \iff m = 1$ and $a_m \in \mathbb{Z}[1/2] \iff m = 2^e$. For odd $m \le x$, $v_2(a_m) = \sum_{p \mid m} v_2(p - 1)$ satisfies an unconditional Erdős–Kac law with mean $2\log\log x + C_1 + O((\log\log x)/\log x)$ and variance $6\log\log x + C_2 - \sum_{p>2} v_2(p-1)^2/p^2 - 2\pi^2/3 + o(1)$, matching a compound Poisson law with $\operatorname{Geom}(1/2)$ steps ($\mathbb{E}[X]=2$, $\mathbb{E}[X^2]=6$, generating exponent $\alpha(z) = z/(2-z)$).
2. **Exact failure of Mira's local isolation for $\ln 2$ (Paper theorem).** Expanding $2^N \ln 2$ in Lambert coordinates splits identically into the binary-level head $H_N^{\mathrm{Lam}} = \sum_{m \le N} a_m \sum_{r=1}^{\lfloor N/m \rfloor} 2^{N - mr} = R_N = \sum_{n \le N} 2^{N-n}/n$ and tail $T_N^{\mathrm{Lam}} = \sum_{m \ge 1} a_m 2^{N \bmod m}/(2^m - 1) = \sum_{n > N} 2^{N-n}/n < 1/(N+1)$. Every odd prime $p \in (N/3, N] \setminus \{5\}$ divides $\operatorname{den}_{\mathrm{odd}}(H_N^{\mathrm{Lam}})$, giving $\operatorname{den}_{\mathrm{odd}}(H_N^{\mathrm{Lam}}) \ge \exp(\frac{2}{3}N(1+o(1)))$. All three pillars of Mira's method fail: integral head annihilation fails catastrophically; the $2$-adic drift $v_2(a_m) \sim 2\log\log m$ is invisible mod $1$ because $P^+(m) \mid \operatorname{den}(a_m)$ blocks integrality; the Lambert tail $m > N$ decays as $2^{-(m-N)}$ with no $\log\log N$ band and cancels against the $m \le N$ remainder down to $T_N^{\mathrm{Lam}} < 1/(N+1)$; and for every prime $p \in (N/2, N]$, the Lambert-head term $a_p 2^{N-p} = 2^{N-p}/p - 2^{N-p}$ is algebraically identical mod $1$ to the Taylor prime-band term $2^{N-p}/p$.
3. **Classification of integer-valued signed multiplicative Lambert series $L_f = \sum_{m \ge 1} f(m)/(2^m - 1) = \sum_{n \ge 1} (f * 1)(n) 2^{-n}$ (Paper theorems + model benchmark).**
   - *Rational collapse*: $L_\mu = 1/2$, $L_\varphi = 2$.
   - *Density-zero support (unconditionally non-normal)*: $L_\lambda = \sum_{k \ge 1} 2^{-k^2}$ has one-frequency $0$; for $f(m) = (-1)^{\omega(m)}$, $(f * 1)(n) = \prod_{p^e \parallel n} (1 - e)$ is supported on powerful numbers ($O(\sqrt{x})$), forcing constant binary runs across gap interiors and asymptotic bit-transition frequency $O(\sqrt{N}\log N / N) \to 0$.
   - *Half-split real Dirichlet characters $L_\chi$ (flagship $\chi = \chi_4$, $(\chi_4 * 1)(n) = r_2(n)/4$)*: **both unconditionally non-normal and base-2 disjunctive with exact word count $\Theta_w(N/\sqrt{\log N})$**. Phase 14's arrival-sum reindexing plus Markov's inequality proves that the $1$-bit frequency on $[N, 2N)$ and $[1, N]$ is $O_\chi(1/\sqrt{\log N}) \to 0$ (Theorem 3.2). Conversely, planting split primes $n + j_0 = bp$ with $b = p_0^{2u_w} m$ ($m \le N^\theta$ split squarefree) and applying Selberg's upper-bound sieve over inert primes $q \in ((\log N)^2, (H/b)^{\rho/4}]$ with Perelli–Pintz–Salerno's short-interval Bombieri–Vinogradov theorem forces all other offsets $j \le 10\log\log N$ to vanish identically ($c_\chi = 0$) and gives $\gg_{a,w,\chi} H/\sqrt{\log N}$ distinct occurrences of every binary word $w$ on every window $N^a \le H \le N$, $7/12 < a \le 1$ (Theorem 3.3).
   - *Zero-drift, linearly-growing odd $f(m) = g(m) = m a_m = \prod_{p \mid m} (1 - p)$*: $(g * 1)(n) = \prod_{p^e \parallel n} (1 + e(1-p))$ satisfies $|(g*1)(n)| < n$ for $n \ge 2$, vanishes iff $n \equiv 2 \pmod 4$, and has $v_2((g*1)(n)) = 0$ on density $2/3$ (zero $2$-adic drift) while $|(g*1)(p)| = p - 2$ generates carries of size $\asymp N$ across $\Theta(\log N)$ active offsets—indicating why local isolation fails from the Archimedean side (large signed carries rather than small fractional parts).
   - *Full-density signed positive drift (benchmark model)*: $f_{\mathrm{sym}}$ with $(f_{\mathrm{sym}} * 1)(2^e u) = (2e+1)(-2)^{\omega(u)}$ is genuinely signed with equal $+$ and $-$ densities and exact $2$-adic drift $\omega(u) \sim \log\log n$; its independent symmetric Poisson arrival model has one-frequency exactly $1/2$ (a model benchmark only; actual word density and normality for $L_{f_{\mathrm{sym}}}$ remain open).

All finite assertions, exact rational identities, empirical $v_2(a_m)$ statistics up to $200{,}000$, and certified integer-carry binary expansions up to $2^{17} = 131{,}072$ bits are verified by [scripts/phase16_weighted_lambert.py](../../scripts/phase16_weighted_lambert.py); the exact algebraic identities of §§1 and 3 are also **kernel-verified** in [WeightedLambertIdentities.lean](../../NormalityChecker/WeightedLambertIdentities.lean).

## 1. Exact arithmetic structure of $a_m$

### 1.1 Möbius inversion, multiplicativity, and denominator non-cancellation

Expanding $(2^m - 1)^{-1} = \sum_{r \ge 1} 2^{-mr}$ gives
```math
\sum_{m=1}^{\infty} \frac{a_m}{2^m - 1}
= \sum_{n=1}^{\infty} \left(\sum_{m \mid n} a_m\right) 2^{-n}.
```
Matching $\ln 2 = \sum_{n \ge 1} 2^{-n}/n$ requires $(a * 1)(n) = 1/n$ for all $n \ge 1$. By Möbius inversion,
```math
a_m = \sum_{d \mid m} \mu(d)\,\frac{1}{m/d}
= \frac{1}{m} \sum_{d \mid m} d\,\mu(d)
= \frac{1}{m} \prod_{p \mid m} (1 - p),
```
with $a_{p^e} = (1 - p)/p^e$ for $e \ge 1$. Hence for every $m \ge 1$:
- $\operatorname{sgn}(a_m) = (-1)^{\omega(m)}$;
- $|a_m| = \frac{\varphi(\operatorname{rad}(m))}{m} = \frac{\operatorname{rad}(m)}{m} \cdot \frac{\varphi(m)}{m} \le \frac{\varphi(m)}{m} < 1$ for $m \ge 2$ (equality iff $m$ is squarefree), justifying absolute convergence and Fubini rearrangement;
- for $m = 2^e u$ ($e \ge 1$, $u$ odd), $a_{2^e u} = -2^{-e} a_u$, so $v_2(a_m) = \sum_{p \mid m, p > 2} v_2(p - 1) - v_2(m)$ (and for odd $m$, $v_2(a_m) = \sum_{p \mid m} v_2(p - 1) \ge \omega(m)$).

**Proposition 1.1 (Exact prime valuations and non-cancellation at $P^+(m)$).** For every $m \ge 2$ and every prime $q$,
```math
v_q(a_m) = \sum_{p \mid m} v_q(p - 1) - v_q(m),
\qquad
v_q(\operatorname{den}(a_m)) = \max\!\left(0,\; v_q(m) - \sum_{p \mid m} v_q(p - 1)\right).
```
For the largest prime divisor $P^+(m)$ of $m$, every $p \mid m$ satisfies $0 < p - 1 < P^+(m)$, so $v_{P^+(m)}(p - 1) = 0$ and $v_{P^+(m)}(a_m) = -v_{P^+(m)}(m)$. Thus $P^+(m)^{v_{P^+(m)}(m)} \parallel \operatorname{den}(a_m)$, whence $a_m \in \mathbb{Z} \iff m = 1$ and $a_m \in \mathbb{Z}[1/2] \iff m = 2^e$. Smaller odd primes can cancel completely (e.g., $a_{21} = 4/7$, $a_{42} = -2/7$). $\square$

### 1.2 Exact Erdős–Kac distribution of $v_2(a_m)$

Set $W(m) := \sum_{2 < p \mid m} v_2(p - 1)$, $w(p) = v_2(p - 1)$, $\mathcal{O}(x) = \{1 \le m \le x : 2 \nmid m\}$, $A(x) = \sum_{2 < p \le x} w(p)/p$, and $B(x)^2 = \sum_{2 < p \le x} w(p)^2/p$.

**Theorem 1.2 (Mean, variance, and Gaussian law of $v_2(a_m)$).** There exist absolute constants $C_1, C_2$ such that as $x \to \infty$:
```math
A(x) = 2\log\log x + C_1 + O\!\left(\frac{\log\log x}{\log x}\right),
\qquad
B(x)^2 = 6\log\log x + C_2 + O\!\left(\frac{(\log\log x)^2}{\log x}\right).
```
Over odd integers $m \in \mathcal{O}(x)$,
```math
\mathbb{E}_{\mathcal{O}(x)}[v_2(a_m)] = 2\log\log x + C_1 + O\!\left(\frac{\log\log x}{\log x}\right),
```
```math
\operatorname{Var}_{\mathcal{O}(x)}(v_2(a_m))
= B(x)^2 - \sum_{2 < p \le x} \frac{w(p)^2}{p^2} - \sum_{\substack{2 < p, q \le x \\ pq > x}} \frac{w(p)w(q)}{pq} + o(1)
= 6\log\log x + C_2 - \sum_{p > 2} \frac{w(p)^2}{p^2} - \frac{2\pi^2}{3} + o(1).
```
Moreover, both on $\mathcal{O}(x)$ and on $\{1, \dots, x\}$, $(v_2(a_m) - 2\log\log x)/\sqrt{6\log\log x} \xrightarrow{d} \mathcal{N}(0, 1)$.

*Proof.* Writing $w(p) = \sum_{k \ge 1} \mathbf{1}_{p \equiv 1 (2^k)}$ and $w(p)^2 = \sum_{k \ge 1} (2k - 1)\mathbf{1}_{p \equiv 1 (2^k)}$ splits $A(x)$ and $B(x)^2$ into $S_k(x) = \sum_{p \le x, p \equiv 1(2^k)} 1/p$. Applying Siegel–Walfisz for $k \le K = \lfloor \log_2 \log x \rfloor$ (with $\varphi(2^k) = 2^{k-1}$) and uniform Brun–Titchmarsh for $k > K$ yields leading constants $\sum_{k \ge 1} 2^{-(k-1)} = 2$ and $\sum_{k \ge 1} (2k-1)2^{-(k-1)} = 6$ (the first two raw moments of $\operatorname{Geom}(1/2)$, giving compound-Poisson variance $6\log\log x$). Expanding $\sum_{m \in \mathcal{O}(x)} W(m)^2$ over pairs $(p, q)$ with $pq \le x$ leaves the missing-corner constant $\sum_{pq > x} w(p)w(q)/(pq) \to 4 \int_0^1 \frac{-\log(1-u)}{u}\,du = \frac{2\pi^2}{3} \approx 6.57974$. The Gaussian CLT follows from the Billingsley–Kubilius moment method on $W_y(m) = \sum_{2 < p \le y, p \mid m} \min(w(p), K_x)$ with $y = x^{1/\log\log x}$ and $K_x = \lfloor 2\log_2 \log\log x \rfloor$; in Dirichlet-series terms, truncating at fixed $K$ yields the classical Selberg–Delange exponent $\alpha_K(z) = \sum_{k=1}^{K-1}(z/2)^k + z^K/2^{K-1} \to z/(2-z)$ ($|z| < 2$). $\square$

### 1.3 Exact identity for $2^N \ln 2$ in Lambert coordinates

Splitting $2^N/(2^m - 1) = \sum_{r=1}^{\lfloor N/m \rfloor} 2^{N - mr} + 2^{N \bmod m}/(2^m - 1)$ and summing against $a_m$ gives $2^N \ln 2 = H_N^{\mathrm{Lam}} + T_N^{\mathrm{Lam}}$, where
```math
H_N^{\mathrm{Lam}} = \sum_{m=1}^{N} a_m \sum_{r=1}^{\lfloor N/m \rfloor} 2^{N - mr} = \sum_{n=1}^{N} \frac{2^{N-n}}{n} = R_N,
\qquad
T_N^{\mathrm{Lam}} = \sum_{m=1}^{\infty} a_m \frac{2^{N \bmod m}}{2^m - 1} = \sum_{n=N+1}^{\infty} \frac{2^{N-n}}{n} \in \left(\frac{1}{2(N+1)},\; \frac{1}{N+1}\right).
```
Every odd prime $p \in (N/3, N] \setminus \{5\}$ divides $\operatorname{den}_{\mathrm{odd}}(R_N)$ (for $p \in (N/3, N/2]$, $2^{N-p}/p + 2^{N-2p}/(2p) = 2^{N-2p}(2^{p+1}+1)/(2p)$ and $2^{p+1} + 1 \equiv 5 \pmod p$), giving $\operatorname{den}_{\mathrm{odd}}(H_N^{\mathrm{Lam}}) \ge \exp(\frac{2}{3}N(1+o(1)))$. For the Lambert partial sum $L_N = \sum_{m=1}^N a_m/(2^m - 1)$ vs $S_N = 2^{-N} R_N$,
```math
2^N(L_N - S_N) = \sum_{m=1}^{N} a_m \frac{2^{N \bmod m}}{2^m - 1} = T_N^{\mathrm{Lam}} - \sum_{k=1}^{\infty} a_{N+k} 2^{-k} + O(2^{-N}),
```
which oscillates at scale $O(1)$. For every prime $p \in (N/2, N]$, $\lfloor N/p \rfloor = 1$ and
```math
a_p 2^{N-p} = \frac{1-p}{p} 2^{N-p} = \frac{2^{N-p}}{p} - 2^{N-p} \equiv \frac{2^{N-p}}{p} \pmod{1}.
```

## 2. Diagnosis: why Mira's local isolation fails completely for $\ln 2$

Mira Cult's positive word-density proof for $E$ relies on three pillars: (i) integral head annihilation mod $1$, (ii) positive $2$-adic valuation drift $V(n) \sim \log\log n$ creating a localized active band where one planted prime $N + j_0 = bp$ lands at the target midpoint, and (iii) complement avoidance on all other band sites.

**Theorem 2.1 (Structural obstruction for $\ln 2$).** All three pillars fail for $\ln 2$:
1. *Failure of Pillar (i):* $H_N^{\mathrm{Lam}} = R_N$ carries odd denominator $\ge \exp(\frac{2}{3}N(1+o(1)))$ while $T_N^{\mathrm{Lam}} < 1/(N+1)$; 100% of the digit information resides in the global rational head $R_N \pmod 1$.
2. *Failure of Pillar (ii):* For $m > N$, $|a_m| < 1$ forces $|a_m 2^N/(2^m - 1)| < 2^{-(m-N)}(1 + 2^{-N})$ with no $\log\log N$ band. Although $v_2(a_m) \sim 2\log\log m$, Proposition 1.1 guarantees $P^+(m) \mid \operatorname{den}(a_m)$ for every $m \ge 2$, so no individual term $a_m 2^{-k}$ is an integer (preventing termwise mod-$1$ annihilation by powers of $2$, though cancellation across distinct terms is controlled separately by the prime-band identity in Pillar (iii)). The apparent $O(1)$ Lambert tail cancels identically against $\sum_{m \le N} a_m 2^{N \bmod m}/(2^m - 1)$ down to $T_N^{\mathrm{Lam}} < 1/(N+1)$.
3. *Failure of Pillar (iii) and reformulations:* Clearing $H_N^{\mathrm{Lam}}$ requires multiplying by $M \ge \exp(\frac{2}{3}N(1+o(1)))$, destroying $\{2^N \ln 2\}$; isolating a prime $m = p \in (N/2, N]$ in the Lambert head is algebraically identical mod $1$ to isolating $2^{N-p}/p$ in $R_N$, leaving all $\Theta(N/\log N)$ other primes in $(N/2, N]$ simultaneously active. $\square$

## 3. Classification of integer-valued signed multiplicative Lambert series

For multiplicative $f: \mathbb{N}_{\ge 1} \to \mathbb{Z}$ with $|f(m)| \ll m^A$, set $L_f = \sum_{m \ge 1} f(m)/(2^m - 1) = \sum_{n \ge 1} c_f(n) 2^{-n}$ where $c_f = f * 1 \in \mathbb{Z}$, so Pillar (i) holds automatically.

- **Rational collapse:** $L_\mu = 1/2$, $L_\varphi = 2$.
- **Zero-density support (unconditionally non-normal):** $L_\lambda = \sum_{k \ge 1} 2^{-k^2}$ has $1$-bit frequency $0$. For $f(m) = (-1)^{\omega(m)}$, $c_f(n) = \prod_{p^e \parallel n}(1 - e)$ is supported strictly on powerful numbers ($O(\sqrt{x})$) with $|c_f(n)| \le \tau(n) \le n$; across every gap interior $[P_k, P_{k+1} - \lceil 2\log_2 P_{k+1}\rceil - 2]$, the binary digit is constant according to the sign of the remaining tail, forcing bit-transition density $O(\sqrt{N}\log N / N) \to 0$.
- **Half-split real nonprincipal Dirichlet characters $L_\chi$ (flagship $\chi = \chi_4$, $c_{\chi_4}(n) = r_2(n)/4$):**
  - *Theorem 3.2 (Unconditional non-normality):* Factoring $c_\chi(m) = 2^{V_\chi(m)} U_\chi(m)$ on its support $\mathcal{S}_\chi$ (density $\sim C_\chi/\sqrt{\log x}$), decomposing $m = sr$ (squarefree $\times$ squarefull) gives $\sum_{m \le x} U_\chi(m) \ll_\chi x/\sqrt{\log x}$. By Phase 14's exact arrival-sum reindexing (`ErdosBorweinArrivals.arrival_sum`) and Markov's inequality on $\sum_{d \ge 1} 2^{-d} C_\chi(n+d) \ge 0$, the proportion of $1$-bits on $[N, 2N)$ and $[1, N]$ is $O_\chi(1/\sqrt{\log N}) \to 0$.
  - **Theorem 3.3 (Base-2 disjunctivity and exact word order $\Theta_w(N/\sqrt{\log N})$; paper proof using Perelli–Pintz–Salerno 1985).** Let $\chi$ be a nonprincipal real Dirichlet character of conductor $q_0$, $w \in \{0, 1\}^k$ any binary word of length $k \ge 1$, and $7/12 < a \le 1$. Then for every sufficiently large $N$ and every window $I = [N, N + H)$ with $N^a \le H \le N$, the word $w$ occurs $\gg_{a,w,\chi} H/\sqrt{\log N}$ times in the binary expansion of $L_\chi$ starting in $I$. Combined with Theorem 3.2, every word $w$ containing at least one `1` occurs $\Theta_{w,\chi}(N/\sqrt{\log N})$ times in the first $N$ bits of $L_\chi$.
    *Proof.* Let $p_0$ be the least split prime ($\chi(p_0) = 1$; $p_0 = 5$ for $\chi_4$) and let $u_w = \sum_{i=1}^k w_i 2^{k-i} \in [0, 2^k - 1]$. Choose $\theta > 0$ small enough that $a - \theta > 7/12$. Let $\mathcal{M}$ be the set of squarefree integers $m \le N^\theta$ all of whose prime factors are split primes $> p_0$ and satisfying $\ell := \omega(m) \le 2\log\log N$. Because split primes have Dirichlet density $1/2$, $\sum_{m \le N^\theta,\; \mathrm{split\;sqfree}} 1/m \asymp_{\chi,\theta} \sqrt{\log N}$; by Rankin's bound with weight $2^{\omega(m) - 2\log\log N}$, the tail $\omega(m) > 2\log\log N$ contributes $\ll_\chi (\log N)^{1 - 2\log 2} = o(\sqrt{\log N})$ (since $1 - 2\log 2 \approx -0.386 < 1/2$), so $\sum_{m \in \mathcal{M}} 1/m \asymp_{\chi,\theta} \sqrt{\log N}$.
    For each $m \in \mathcal{M}$, set $b = p_0^{2u_w} m$ and $j_0 = k + 2 + \ell \le 3\log\log N$ (for large $N$). Let $X = (N + j_0)/b$, $Y = H/b \ge X^{a-\theta}$, and consider split primes $p \in (X, X + Y]$ (so $n := bp - j_0 \in I$). Since $p > N^{1-\theta} > b$, we have $\gcd(p, b) = 1$, hence $c_\chi(bp) = c_\chi(p_0^{2u_w}) c_\chi(m) c_\chi(p) = (2u_w + 1) 2^{\ell + 1}$, giving $c_\chi(n + j_0) 2^{-j_0} = (2u_w + 1) / 2^{k+1}$. By Huxley's short-interval prime number theorem in progressions (fixed modulus $q_0$, $Y \ge X^{7/12 + \varepsilon}$), the number of such planted primes $p$ is $(1 + o(1)) Y / (2 \log X) \asymp H / (b \log N)$.
    Put $J_1 := \lceil 10 \log\log N \rceil$. We call a planted prime $p \in (X, X + Y]$ *bad* if either (A) $c_\chi(bp + h) > 0$ for some $h = j - j_0$ with $1 \le j \le J_1$, $j \neq j_0$, or (B) the tail $E_{\mathrm{tail}}(p) := \sum_{j > J_1} c_\chi(bp + j - j_0) 2^{-j} \ge 2^{-(k+2)}$.
    - *Bound on (A):* Fix $h = j - j_0 \neq 0$ ($|h| \le J_1$). Let $z_0 = (\log N)^2$ and $z_1 = Y^{\rho/4}$, where $\rho = \rho(a, \theta) > 0$ is chosen so that $D := z_1^2 = Y^{\rho/2}$ lies within the short-interval Bombieri–Vinogradov range of Perelli–Pintz–Salerno (*J. London Math. Soc.* (2) **32** (1985), 211–222, Theorem 1, valid for $Y \ge X^{7/12+\varepsilon}$). Since $c_\chi(n) = 0$ whenever an inert prime $q$ ($\chi(q) = -1$) satisfies $q \parallel n$, every $p$ with $c_\chi(bp + h) > 0$ either satisfies $q^2 \mid (bp + h)$ for some inert $q \in (z_0, z_1]$ or satisfies $q \nmid (bp + h)$ for all inert $q \in (z_0, z_1]$. Because $\gcd(q, b) = 1$ (as $b$ has only split prime factors) and $q > z_0 > |h|$ (so $q \nmid h$), the square-divisible event has count at most $\sum_{z_0 < q \le z_1} (Y/q^2 + 1) \ll Y/(\log N)^2 + z_1 \ll Y/(\log N)^2$. For the sifted event, each inert $q \in (z_0, z_1]$ forbids one reduced residue class $p \equiv -h b^{-1} \pmod q$ coprime to $q_0$. Applying Selberg's upper-bound sieve of level $D = z_1^2$ with the short-interval Bombieri–Vinogradov remainder bound $O_A(Y/(\log X)^A)$ yields at most $\ll_\chi (Y/\log X)\prod_{z_0 < q \le z_1,\;\chi(q)=-1}(1 - 1/(q-1)) \ll_{a,\theta,\chi} (Y/\log N)\sqrt{(\log\log N)/\log N}$ bad primes for this $h$. Summing over the $\le J_1$ choices of $h$ gives total (A)-bad count $\ll_{a,\theta,\chi} (Y/\log N)(\log\log N)^{3/2}/\sqrt{\log N} = o(Y/\log N)$.
    - *Bound on (B):* For $j > N$, $0 \le c_\chi(bp + j - j_0) \le \tau(bp + j - j_0) \le 2N + j$, so $\sum_{j > N} c_\chi(bp + j - j_0) 2^{-j} \ll N 2^{-N}$ uniformly in $p$. For $J_1 < j \le N$ ($h = j - j_0$), we have $bp + h < 4N$, so $c_\chi(bp + h) \le \tau(bp + h) \le 2\sum_{d \le 2\sqrt{N}} \mathbf{1}_{d \mid (bp + h)}$. Writing $g = \gcd(d, b) \mid h$ and $d = g d'$, since $2\sqrt{N} \ll Y^{6/7}$, Brun–Titchmarsh on the progression $b'p \equiv -h' \pmod{d'}$ gives $\sum_{p \in (X, X+Y]} \tau(bp + h) \ll \tau(h) (Y / \log N) \sum_{d' \le 2\sqrt{N}} 1/\varphi(d') \ll \tau(h) Y$. Summing against $2^{-j}$ over $J_1 < j \le N$ gives $\sum_{p \in (X, X+Y]} E_{\mathrm{tail}}(p) \ll Y \sum_{j > J_1} \tau(j - j_0) 2^{-j} + Y N 2^{-N} \ll Y J_1 2^{-J_1} \ll Y (\log\log N)(\log N)^{-10\log 2}$. By Markov's inequality, the number of (B)-bad primes is at most $2^{k+2} \sum_p E_{\mathrm{tail}}(p) \ll_w Y (\log\log N)(\log N)^{-10\log 2} = o(Y/\log N)$ (since $10\log 2 \approx 6.93 > 1$).
    - *Deterministic subtraction and injectivity:* For every $m \in \mathcal{M}$, subtracting the (A)- and (B)-bad primes leaves $(1 - o(1)) Y/(2\log X) \asymp H/(b\log N)$ *good* primes $p$. At each good $p$, $n = bp - j_0 \in I$ satisfies $\{2^n L_\chi\} = \{(2u_w + 1)/2^{k+1} + E_{\mathrm{tail}}(p)\} \in [u_w/2^k, (u_w + 1)/2^k)$, so the binary word at shift $n$ is exactly $w$. Moreover, the map $(m, p) \mapsto n = bp - j_0$ is **injective** on good pairs: since $c_\chi(n + j) = 0$ for all $1 \le j \le J_1$ with $j \neq j_0$, $j_0 \le 3\log\log N < J_1$ is uniquely determined as the least $j \ge 1$ with $c_\chi(n + j) > 0$; hence $bp = n + j_0$ is uniquely determined, and $p > N^{1-\theta} > N^\theta \ge b$ recovers $p$ and $m$ uniquely. Summing over $m \in \mathcal{M}$ gives $\gg_{a,w,\chi} (H/\log N)\sum_{m \in \mathcal{M}} 1/m \asymp_{a,w,\chi} H/\sqrt{\log N}$ distinct occurrences of $w$ in $I$. $\square$
- **Zero-drift, linearly-growing odd $g(m) = m a_m = \prod_{p \mid m}(1 - p)$:** $c_g(n) = \prod_{p^e \parallel n}(1 + e(1-p)) = ((\mathrm{id}\cdot\mu)*\tau)(n)$ satisfies $L_g = \sum_{d \ge 1} d\mu(d) E(2^{-d})$, $|c_g(n)| < n$ for $n \ge 2$ (by Bernoulli's inequality, kernel-verified as `cleared_local_abs_lt`), $c_g(n) = 0 \iff n \equiv 2 \pmod 4$ (density $1/4$), and $v_2(c_g(n)) = 0$ iff $2 \mid v_2(n)$ (density $2/3$). Thus $2$-adic drift is zero while $|c_g(p)| = p - 2$ creates signed carries of size $\asymp N$ across $\Theta(\log N)$ active offsets—indicating why local isolation fails from the Archimedean side.
- **Full-density signed positive drift $f_{\mathrm{sym}}$ (benchmark model):** Defining $f_{\mathrm{sym}}(2^e) = 2$, $f_{\mathrm{sym}}(p) = -3$ ($p > 2$), $f_{\mathrm{sym}}(p^e) = 0$ ($p > 2, e \ge 2$) yields $c_{\mathrm{sym}}(2^e u) = (2e+1)(-2)^{\omega(u)}$: genuinely signed with equal $+$ and $-$ densities and exact $2$-adic drift $\omega(u) \sim \log\log n$. In the independent signed Poisson arrival model, sign symmetry makes the model one-frequency exactly $1/2$ (by contrast with $p_* \approx 0.4924$ for unsigned $E$); actual word-density bounds and normality for the signed series $L_{f_{\mathrm{sym}}}$ remain open.

## 4. Reproduction and finite checks

```sh
python3 -B scripts/phase16_weighted_lambert.py
```

The script checks Möbius inversion and $P^+(m)$ non-cancellation through $n = 2000$, $H_N^{\mathrm{Lam}} = R_N$ and prime-band congruences, the empirical mean and finite-$X$ variance of $v_2(a_m)$ over odd $m \le 200{,}000$ (mean $3.92212$ matching exact odd-multiple expectation $3.92212$; empirical variance $4.24481$ vs. finite-$X$ prediction $4.15324$, where the finite-$X$ missing-corner term is $4.90781$ trending slowly toward its asymptotic limit $2\pi^2/3 \approx 6.57974$), and certified integer-carry binary expansions through $2^{17} = 131{,}072$ bits for $L_{\chi_4}$, $L_{(-1)^\omega}$, $L_{m a_m}$, and $L_{\mathrm{sym}}$.
