\section{Introduction}
\label{sec:introduction}

\begin{figure}
\[\begin{array}{c}
 \arraycolsep=3pt
 \begin{array}{rrclcl}
  \text{Variables}       & \px,\py,\pz & ∈ & \Var    &     & \\
  \text{Values}          &         \pv & ∈ & \Val    & ::= & \Lam{\px}{\pe} \\
  \text{Expressions}     &         \pe & ∈ & \Exp    & ::= & \slbl \px \mid \slbl \pv \mid \slbl \pe~\px \mid \slbl \Let{\px}{\pe_1}{\pe_2} \\
  \\
  \text{Scott Domain}    &          d  & ∈ & \ScottD & ::= & \FunV([\ScottD \to \ScottD]) \mid \bot \\
  \text{Liveness Domain} &      d^{∃l} & ∈ & \LiveD  & =   & \poset{\Var} \\
 \end{array} \\
\end{array}\]
\subcaption{Syntax of expressions and Scott Domain}
  \label{fig:syntax}
\begin{minipage}{0.52\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semscott{\wild} \colon \Exp → (\Var \to \ScottD) → \ScottD } } \\
  \\[-0.5em]
  \semscott{\px}_ρ & {}={} & ρ(\px) \\
  \semscott{\Lam{\px}{\pe}}_ρ & {}={} & \fn{d}{\semscott{\pe}_{ρ[\px ↦ d]}} \\
  \semscott{\pe~\px}_ρ & {}={} & \begin{cases}
     f(d_2) & \text{if $\semscott{\pe} = \FunV(f)$}  \\
     \bot   & \text{otherwise}  \\
   \end{cases} \\
  \semscott{\Let{\px}{\pe_1}{\pe_2}}_ρ & {}={} &
    \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semscott{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\subcaption{Denotational semantics after Scott}
  \label{fig:semantics}
\end{minipage}%
\begin{minipage}{0.5\textwidth}
\arraycolsep=0pt
\[\begin{array}{rcl}
  \multicolumn{3}{c}{ \ruleform{ \semlive{\wild} \colon \Exp → (\Var → \LiveD) → \LiveD } } \\
  \\[-0.5em]
  \semlive{\px}_ρ & {}={} & ρ(\px) \\
  \semlive{\Lam{\px}{\pe}}_ρ & {}={} & \semlive{\pe}_ρ[\px ↦ \varnothing] \setminus \{\px\} \\
  \\[-0.5em]
  \semlive{\pe~\px}_ρ & {}={} & \semlive{\pe} ∪ ρ(\px) \\
  \\[-0.5em]
  \semlive{\Let{\px}{\pe_1}{\pe_2}}_ρ& {}={} & \begin{letarray}
      \text{letrec}~ρ'. & ρ' = ρ \mathord{⊔} [\px \mathord{↦} d_1] \\
                        & d_1 = \{\px\} \mathord{∪} \semscott{\pe_1}_{ρ'} \\
      \text{in}         & \semlive{\pe_2}_{ρ'}
    \end{letarray} \\
\end{array}\]
\subcaption{Naïve liveness analysis}
  \label{fig:liveness}
\end{minipage}%
\end{figure}

