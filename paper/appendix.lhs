%include custom.fmt

%\externaldocument{comp-trace-ext}

\renewcommand\thefigure{\thesection.\arabic{figure}}

\subsection{Proofs}

\providecommand{\tr}{\ensuremath{\tilde{ρ}}}

\begin{proof}[Of \Cref{thm:semlive-correct-1}]
  Let us fix $\pe$ and $\px$ and let us assume that there exists $\tr$ such that
  $\tr(\px) \not⊆ \semlive{\pe}$. The goal is to show that $\px$ is dead in $\pe$,
  so we are given an arbitrary $ρ$, $d_1$ and $d_2$ and have to show that
  $\semscott{\pe}_{ρ[\px↦d_1]} = \semscott{\pe}_{ρ[\px↦d_2]}$.
  We proceed by induction on $\pe$:
  \begin{itemize}
    \item \textbf{Case $\pe\triangleq\py$}: If $\px=\py$, then
      $\tr(\px) \not⊆ \semscott{\py}_ρ = \tr(\py) = \tr(\px)$, a contradiction.
      If $\px \not= \py$, then varying the entry for $\px$ won't matter; hence
      $\px$ is dead in $\py$.
    \item \textbf{Case $\pe\triangleq\Lam{\py}{\pe'}$}: The equality follows from
      pointwise equality on functions, so we pick an arbitrary $d$ to show
      $\semscott{\pe'}_{ρ[\px↦d_1][\py↦d]} = \semscott{\pe'}_{ρ[\px↦d_2][\py↦d]}$.

      This is simple to see if $\px=\py$. Otherwise, $\tr[\py↦\varnothing]$
      witnesses the fact that
      \[
        \tr[\py↦\varnothing](\px) = \tr(\px) \not⊆
        \semlive{\Lam{\px}{\pe'}}_{\tr} = \semlive{\pe'}_{\tr[\py↦\varnothing]}
      \]
      so we can apply the induction hypothesis to see that $\px$ must be dead in
      $\pe'$, hence the equality on $\semscott{\pe'}$ holds.
    \item \textbf{Case $\pe\triangleq\pe'~\py$}:
      From $\tr(\px) \not⊆ \semlive{\pe'} ∪ \tr(\py)$ we can see that
      $\tr(\px) \not⊆ \semlive{\pe'}$ and $\tr(\px) \not⊆ \tr(\py)$.
      If $\px=\py$ then the latter inequality leads to a contradiction.
      Otherwise, $\px$ must be dead in $\pe'$, hence both cases of
      $\semscott{\pe'~\py}$ evaluate bisimilarly, differing only in
      the environment. It remains to be shown that
      $ρ[\px↦d_1](\py) = ρ[\px↦d_2](\py)$, and that is easy to see since
      $\px \not= \py$.
    \item \textbf{Case $\pe\triangleq\Let{\py}{\pe_1}{\pe_2}$}:
      We have to show that
      \[
        \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
      \]
      where $d'_i = \semscott{\pe_1}_{ρ[\px↦d_i][\py↦d'_i]}$.
      The case $\px = \py$ is simple to see, because $ρ[\px↦d_i](\px)$ is never
      looked at.
      So we assume $\px \not= \py$ and see that $\tr(\px) = \tr'(\px)$, where
      $\tr'(\py) = \tr ⊔ [\py ↦ \semlive{\pe_1}_{\tr'}]$.

      We know that
      \[
        \tr'(\px) = \tr(\px) \not⊆ \semlive{\pe}_{\tr} = \semlive{\pe_2}_{\tr'}
      \]
      So by the induction hypothesis, $\px$ is dead in $\pe_2$.

      We proceed by cases over $\tr(\px) = \tr'(\px) ⊆ \semlive{\pe_1}_{\tr'}$.
      \begin{itemize}
        \item \textbf{Case $\tr'(\px) ⊆ \semlive{\pe_1}_{\tr'}$}: Then
          $\tr'(\px) ⊆ \tr'(\py)$ and $\py$ is also dead in $\pe_2$ by the above
          inequality.
          Both deadness facts together allow us to rewrite
          \[
            \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_1]} = \semscott{\pe_2}_{ρ[\px↦d_1][\py↦d'_2]} = \semscott{\pe_2}_{ρ[\px↦d_2][\py↦d'_2]}
          \]
          as requested.
        \item \textbf{Case $\tr'(\px) \not⊆ \semlive{\pe_1}_{\tr'}$}:
          Then $\px$ is dead in $\pe_1$ and $d'_1 = d'_2$. The goal follows
          from the fact that $\px$ is dead in $\pe_2$.
      \end{itemize}
  \end{itemize}
\end{proof}
